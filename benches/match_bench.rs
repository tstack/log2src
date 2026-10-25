//! Measure how long it takes to match log messages to their log statements.
//!
//! Usage: cargo bench --bench match_bench -- <source-dir> [rounds]

use log2src::{
    extract_variables, LogMatchOptions, LogMatcher, LogRef, LogRefBuilder, ProgressTracker,
    SourceRef,
};
use rayon::prelude::*;
use regex::RegexSet;
use regex_syntax::hir::{Hir, HirKind};
use std::collections::HashMap;
use std::path::Path;
use std::time::{Duration, Instant};

/// The longest run of literal bytes any match must contain, the same as the prefilter's key.
fn longest_literal(pattern: &str) -> Option<Vec<u8>> {
    fn walk(hir: &Hir, cur: &mut Vec<u8>, best: &mut Vec<u8>) {
        match hir.kind() {
            HirKind::Literal(lit) => cur.extend_from_slice(&lit.0),
            HirKind::Empty | HirKind::Look(_) => {}
            HirKind::Concat(subs) => subs.iter().for_each(|sub| walk(sub, cur, best)),
            _ => flush(cur, best),
        }
    }
    fn flush(cur: &mut Vec<u8>, best: &mut Vec<u8>) {
        if cur.len() > best.len() {
            std::mem::swap(cur, best);
        }
        cur.clear();
    }
    let hir = regex_syntax::Parser::new().parse(pattern).ok()?;
    let (mut cur, mut best) = (Vec::new(), Vec::new());
    walk(&hir, &mut cur, &mut best);
    flush(&mut cur, &mut best);
    (!best.is_empty()).then_some(best)
}

/// The runs of literal bytes in a pattern, in order, and whether the first run is at the very
/// start of the message.
fn literal_runs(pattern: &str) -> Option<(Vec<Vec<u8>>, bool, bool)> {
    fn walk(
        hir: &Hir,
        cur: &mut Vec<u8>,
        runs: &mut Vec<Vec<u8>>,
        seen_other: &mut bool,
        at_start: &mut Option<bool>,
    ) {
        match hir.kind() {
            HirKind::Literal(lit) => {
                if cur.is_empty() && runs.is_empty() && at_start.is_none() {
                    *at_start = Some(!*seen_other);
                }
                cur.extend_from_slice(&lit.0)
            }
            HirKind::Empty | HirKind::Look(_) => {}
            HirKind::Concat(subs) => subs
                .iter()
                .for_each(|sub| walk(sub, cur, runs, seen_other, at_start)),
            _ => {
                *seen_other = true;
                if !cur.is_empty() {
                    runs.push(std::mem::take(cur));
                }
            }
        }
    }
    let hir = regex_syntax::Parser::new().parse(pattern).ok()?;
    let (mut cur, mut runs, mut seen_other, mut at_start) = (Vec::new(), Vec::new(), false, None);
    walk(&hir, &mut cur, &mut runs, &mut seen_other, &mut at_start);
    if !cur.is_empty() {
        runs.push(cur);
    }
    Some((runs, at_start.unwrap_or(false), seen_other))
}

/// Report where the longest literal, which the prefilter keys on, sits in each pattern.
fn literal_position_stats(stmts: &[&SourceRef]) {
    const LABELS: [&str; 6] = [
        "no placeholders",
        "1 run, at start",
        "1 run, after placeholder",
        "longest first, at start",
        "longest first, after placeholder",
        "longest later",
    ];
    let mut by_lang: HashMap<&str, [usize; 6]> = HashMap::new();
    for stmt in stmts {
        let Some((runs, at_start, has_placeholder)) = literal_runs(stmt.pattern().as_str()) else {
            continue;
        };
        let longest = runs.iter().map(|r| r.len()).max().unwrap_or(0);
        let bucket = match runs.len() {
            _ if !has_placeholder => 0,
            1 if at_start => 1,
            1 => 2,
            // The prefilter takes the first of equal-length runs.
            _ if runs[0].len() == longest && at_start => 3,
            _ if runs[0].len() == longest => 4,
            _ => 5,
        };
        by_lang.entry(stmt.language.as_str()).or_default()[bucket] += 1;
    }
    let mut langs: Vec<_> = by_lang.into_iter().collect();
    langs.sort_by_key(|(_, c)| std::cmp::Reverse(c.iter().sum::<usize>()));
    for (lang, c) in langs {
        let total: usize = c.iter().sum();
        println!("{} ({} statements)", lang, total);
        for (label, count) in LABELS.iter().zip(c) {
            println!(
                "  {:<34} {:>6} ({:>4.1}%)",
                label,
                count,
                100.0 * count as f64 / total as f64
            );
        }
    }
}

fn percentile(sorted: &[usize], pct: usize) -> usize {
    sorted
        .get((sorted.len() * pct / 100).min(sorted.len().saturating_sub(1)))
        .copied()
        .unwrap_or(0)
}

/// Mirror the prefilter's candidate selection, without the filename filter, and report how
/// much work is left for the regexes.
fn prefilter_stats(stmts: &[&SourceRef], label: &str, bodies: &[&str]) {
    let mut literals: Vec<Vec<u8>> = Vec::new();
    let mut lit_ids: HashMap<Vec<u8>, usize> = HashMap::new();
    let mut by_literal: Vec<Vec<usize>> = Vec::new();
    let mut always: Vec<usize> = Vec::new();
    for (index, stmt) in stmts.iter().enumerate() {
        match longest_literal(stmt.pattern().as_str()) {
            Some(lit) => {
                let id = *lit_ids.entry(lit.clone()).or_insert_with(|| {
                    literals.push(lit);
                    by_literal.push(Vec::new());
                    literals.len() - 1
                });
                by_literal[id].push(index);
            }
            None => always.push(index),
        }
    }
    let ac = aho_corasick::AhoCorasick::new(&literals).unwrap();
    let (mut candidates, mut checks) = (Vec::new(), Vec::new());
    let (mut misses, mut wasted) = (0, 0);
    let mut hot_literals: HashMap<usize, usize> = HashMap::new();
    for body in bodies {
        let mut hits: Vec<usize> = ac
            .find_overlapping_iter(body)
            .map(|m| m.pattern().as_usize())
            .collect();
        hits.sort_unstable();
        hits.dedup();
        for &hit in &hits {
            *hot_literals.entry(hit).or_default() += by_literal[hit].len();
        }
        let mut cands: Vec<&SourceRef> = hits
            .iter()
            .flat_map(|&hit| by_literal[hit].iter())
            .chain(always.iter())
            .map(|&i| stmts[i])
            .collect();
        cands.sort_by(|lhs, rhs| rhs.quality.cmp(&lhs.quality));
        candidates.push(cands.len());
        let tried = match cands.iter().position(|c| c.pattern().is_match(body)) {
            Some(pos) => pos + 1,
            None => {
                misses += 1;
                cands.len()
            }
        };
        wasted += tried.saturating_sub(1);
        checks.push(tried);
    }
    candidates.sort_unstable();
    checks.sort_unstable();
    let avg = |v: &[usize]| v.iter().sum::<usize>() as f64 / v.len().max(1) as f64;
    println!(
        "{label}: {} lines, {} literals, {} always-checked statements",
        bodies.len(),
        literals.len(),
        always.len()
    );
    println!(
        "  candidates/line: avg {:.1}, p50 {}, p99 {}, max {}",
        avg(&candidates),
        percentile(&candidates, 50),
        percentile(&candidates, 99),
        candidates.last().unwrap_or(&0)
    );
    println!(
        "  is_match calls/line: avg {:.1}, p99 {}, max {}; {} non-matching calls, {} lines with no match",
        avg(&checks),
        percentile(&checks, 99),
        checks.last().unwrap_or(&0),
        wasted,
        misses
    );
    let mut hot: Vec<_> = hot_literals.into_iter().collect();
    hot.sort_by(|lhs, rhs| rhs.1.cmp(&lhs.1));
    for (id, count) in hot.iter().take(5) {
        println!(
            "  hot literal {:?}: {} candidates contributed",
            String::from_utf8_lossy(&literals[*id]),
            count
        );
    }
}

/// Generate a message that should be matched by the given pattern.
fn synthesize(pattern: &str) -> Option<String> {
    fn walk(hir: &Hir, out: &mut Vec<u8>, counter: &mut usize) {
        match hir.kind() {
            HirKind::Empty | HirKind::Look(_) => {}
            HirKind::Literal(lit) => out.extend_from_slice(&lit.0),
            HirKind::Class(_) => out.push(b'z'),
            HirKind::Capture(_) => {
                *counter += 1;
                out.extend_from_slice(format!("val{}", counter).as_bytes());
            }
            HirKind::Repetition(rep) => walk(&rep.sub, out, counter),
            HirKind::Concat(subs) => subs.iter().for_each(|s| walk(s, out, counter)),
            HirKind::Alternation(subs) => walk(&subs[0], out, counter),
        }
    }
    let hir = regex_syntax::Parser::new().parse(pattern).ok()?;
    let mut out = Vec::new();
    walk(&hir, &mut out, &mut 0);
    String::from_utf8(out).ok()
}

fn file_name(path: &str) -> &str {
    path.rsplit(['/', '\\']).next().unwrap_or(path)
}

struct Line {
    body: String,
    file: Option<String>,
}

fn time<F: FnMut(&Line) -> Option<(String, usize, usize)>>(
    lines: &[Line],
    rounds: usize,
    mut f: F,
) -> (Duration, Vec<Option<(String, usize, usize)>>) {
    let mut results = Vec::new();
    let start = Instant::now();
    for round in 0..rounds {
        for line in lines {
            let res = f(line);
            if round == 0 {
                results.push(res);
            }
        }
    }
    (start.elapsed() / rounds as u32, results)
}

fn key(src_ref: &SourceRef) -> (String, usize, usize) {
    (
        src_ref.source_path.clone(),
        src_ref.line_no,
        src_ref.quality,
    )
}

/// The per-file RegexSet matching that the prefilter replaced, rebuilt here for comparison.
struct OldMatcher<'a> {
    files: Vec<(&'a str, RegexSet, Vec<&'a SourceRef>)>,
    by_name: HashMap<&'a str, Vec<usize>>,
    /// Files where the RegexSet failed to build, which made the old code panic when matching.
    failed: usize,
}

impl<'a> OldMatcher<'a> {
    fn new(stmts: &[&'a SourceRef]) -> Self {
        let mut grouped: HashMap<&'a str, Vec<&'a SourceRef>> = HashMap::new();
        for stmt in stmts {
            grouped.entry(&stmt.source_path).or_default().push(stmt);
        }
        let mut files = Vec::new();
        let mut by_name: HashMap<&'a str, Vec<usize>> = HashMap::new();
        let mut failed = 0;
        for (path, stmts) in grouped {
            match RegexSet::new(stmts.iter().map(|s| s.pattern().as_str())) {
                Ok(set) => {
                    by_name
                        .entry(file_name(path))
                        .or_default()
                        .push(files.len());
                    files.push((path, set, stmts));
                }
                Err(_) => failed += 1,
            }
        }
        Self {
            files,
            by_name,
            failed,
        }
    }

    fn first_match(&self, index: usize, body: &str) -> Option<&'a SourceRef> {
        let (_path, set, stmts) = &self.files[index];
        set.matches(body).iter().next().map(|i| stmts[i])
    }

    fn match_log_statement(&self, log_ref: &LogRef) -> Option<&'a SourceRef> {
        let body = log_ref.body();
        let matches: Vec<&SourceRef> = match log_ref.details.and_then(|d| d.file) {
            Some(filename) => match self.by_name.get(filename) {
                Some(indexes) => indexes
                    .iter()
                    .flat_map(|&i| self.first_match(i, body))
                    .collect(),
                None => (0..self.files.len())
                    .filter(|&i| self.files[i].0.contains(filename))
                    .flat_map(|i| self.first_match(i, body))
                    .collect(),
            },
            None => (0..self.files.len())
                .into_par_iter()
                .flat_map(|i| self.first_match(i, body))
                .collect(),
        };
        let mut best: Option<&SourceRef> = None;
        for m in matches {
            if best.is_none_or(|b| m.quality > b.quality) {
                best = Some(m);
            }
        }
        // Do the same work as building the LogMapping in the real code.
        best.map(|src_ref| {
            let _ = extract_variables(log_ref, src_ref);
        });
        best
    }
}

fn main() {
    let args: Vec<String> = std::env::args()
        .skip(1)
        .filter(|a| a != "--bench")
        .collect();
    let root = args.first().expect("need a source directory");
    let rounds: usize = args.get(1).map(|s| s.parse().unwrap()).unwrap_or(3);

    let tracker = ProgressTracker::new();
    let mut matcher = LogMatcher::new();
    matcher.add_root(Path::new(root)).unwrap();
    let _ = matcher.discover_sources(&tracker);
    let start = Instant::now();
    matcher.extract_log_statements(&tracker);
    println!("extract: {:?}", start.elapsed());

    let start = Instant::now();
    matcher.rebuild_prefilters();
    println!("prefilter build alone: {:?}", start.elapsed());

    let stmts: Vec<&SourceRef> = matcher.statements().collect();
    if let Ok(path) = std::env::var("DUMP_STATEMENTS") {
        let mut out: Vec<String> = stmts
            .iter()
            .map(|s| {
                format!(
                    "{}:{}\t{}",
                    s.source_path,
                    s.line_no,
                    s.text.replace('\n', " ")
                )
            })
            .collect();
        out.sort();
        std::fs::write(path, out.join("\n")).unwrap();
        return;
    }
    let mut lines: Vec<Line> = Vec::new();
    for stmt in &stmts {
        if let Some(body) = synthesize(stmt.pattern().as_str()) {
            if stmt.pattern().is_match(&body) {
                lines.push(Line {
                    body,
                    file: Some(file_name(&stmt.source_path).to_string()),
                });
            }
        }
    }
    let matchable = lines.len();
    assert!(matchable > 0, "no log statements found in {}", root);
    // An equal number of lines from code we don't have the source for.
    for i in 0..matchable {
        lines.push(Line {
            body: format!("zqx{} vwk{} jjq{}", i, i % 997, i % 31),
            file: Some(format!("Unknown{}.java", i % 50)),
        });
    }
    println!(
        "{} statements, {} matchable lines + {} unmatched lines, {} rounds",
        stmts.len(),
        matchable,
        matchable,
        rounds
    );

    if std::env::var("LITERAL_POSITIONS").is_ok() {
        literal_position_stats(&stmts);
        return;
    }
    if std::env::var("PREFILTER_STATS").is_ok() {
        let bodies: Vec<&str> = lines.iter().map(|l| l.body.as_str()).collect();
        prefilter_stats(&stmts, "synthesized", &bodies[..matchable]);
        prefilter_stats(&stmts, "unknown", &bodies[matchable..]);
        if let Ok(path) = std::env::var("LOG_BODIES") {
            let text = std::fs::read_to_string(path).unwrap();
            let bodies: Vec<&str> = text.lines().collect();
            prefilter_stats(&stmts, "log bodies", &bodies);
        }
        return;
    }

    let start = Instant::now();
    let old_matcher = OldMatcher::new(&stmts);
    println!(
        "old per-file RegexSet build: {:?} ({} files, {} failed to build)",
        start.elapsed(),
        old_matcher.files.len() + old_matcher.failed,
        old_matcher.failed
    );

    for with_file in [false, true] {
        fn build(line: &Line, with_file: bool) -> LogRefBuilder<'_> {
            let mut builder = LogRefBuilder::new().with_body(Some(line.body.as_str()));
            if with_file {
                builder = builder.with_file(line.file.as_deref());
            }
            builder
        }
        let (elapsed, results) = time(&lines, rounds, |line| {
            let log_ref = build(line, with_file).build(&line.body);
            matcher
                .match_log_statement(&log_ref, &LogMatchOptions::default())
                .and_then(|m| m.src_ref.map(key))
        });
        let (old_elapsed, old_results) = time(&lines, rounds, |line| {
            let log_ref = build(line, with_file).build(&line.body);
            old_matcher.match_log_statement(&log_ref).map(key)
        });
        println!(
            "{:>13}: {:>10.2?} total, {:>8.2?}/line, {} matched  [old RegexSet]",
            if with_file {
                "with filename"
            } else {
                "no filename"
            },
            old_elapsed,
            old_elapsed / lines.len() as u32,
            old_results.iter().filter(|r| r.is_some()).count()
        );
        if std::env::var("SHOW_MISSES").is_ok() {
            for (line, _) in lines[..matchable]
                .iter()
                .zip(&results)
                .filter(|(_, r)| r.is_none())
                .take(6)
            {
                println!("  MISS {:?} file={:?}", line.body, line.file);
            }
        }
        println!(
            "{:>13}: {:>10.2?} total, {:>8.2?}/line, {} matched  [prefilter]",
            if with_file {
                "with filename"
            } else {
                "no filename"
            },
            elapsed,
            elapsed / lines.len() as u32,
            results.iter().filter(|r| r.is_some()).count()
        );
        let quality = |r: &Option<(String, usize, usize)>| r.as_ref().map(|k| k.2);
        let better = old_results
            .iter()
            .zip(&results)
            .filter(|(o, n)| quality(n) > quality(o))
            .count();
        let worse = old_results
            .iter()
            .zip(&results)
            .filter(|(o, n)| quality(n) < quality(o))
            .count();
        println!(
            "{:>13}  speedup {:.1}x; prefilter found a better match on {} lines, worse on {}",
            "",
            old_elapsed.as_secs_f64() / elapsed.as_secs_f64(),
            better,
            worse
        );
    }
}
