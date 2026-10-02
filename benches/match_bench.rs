//! Measure how long it takes to match log messages to their log statements.
//!
//! Usage: cargo bench --bench match_bench -- <source-dir> [rounds]

use log2src::{extract_variables, LogMatcher, LogRef, LogRefBuilder, ProgressTracker, SourceRef};
use rayon::prelude::*;
use regex::RegexSet;
use regex_syntax::hir::{Hir, HirKind};
use std::collections::HashMap;
use std::path::Path;
use std::time::{Duration, Instant};

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
            let src_ref = src_ref.clone();
            let _ = extract_variables(log_ref, &src_ref);
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
                .match_log_statement(&log_ref)
                .and_then(|m| m.src_ref.as_ref().map(key))
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
