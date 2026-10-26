//! Prototype: reverse an error value captured from a log message back to the
//! place in the source that created the error message.

use log2src::{LogLevel, LogMatchOptions, LogMatcher, LogRefBuilder, ProgressTracker, SourceRef};
use regex::Regex;
use std::collections::BTreeMap;
use std::path::PathBuf;

const SOURCE_CALLS: &[&str] = &[
    "bail", "anyhow", "anyhow::anyhow", "context", "with_context", "write", "writeln", "Err",
    "map_err", "ok_or", "ok_or_else", "error",
];

fn is_source(s: &SourceRef) -> bool {
    let Some(call) = s.call_name.as_deref() else {
        return false;
    };
    if !SOURCE_CALLS.contains(&call) {
        return false;
    }
    if matches!(call, "write" | "writeln") && s.name != "fmt" {
        return false;
    }
    !is_test(s)
}

fn is_test(s: &SourceRef) -> bool {
    s.source_path.contains("test") || s.name.starts_with("test_")
}

fn id(s: &SourceRef) -> String {
    format!("{}:{}", s.source_path.rsplit("/src/").next().unwrap(), s.line_no)
}

/// Render a Rust format string literal with each placeholder replaced by the next value.
fn render(text: &str, values: &mut dyn FnMut(usize) -> String) -> Option<String> {
    let body = text.strip_prefix('"')?.strip_suffix('"')?;
    let mut out = String::new();
    let mut chars = body.chars().peekable();
    let mut idx = 0;
    while let Some(c) = chars.next() {
        match c {
            '\\' => match chars.next()? {
                'n' => out.push('\n'),
                't' => out.push('\t'),
                '\n' => {
                    while chars.peek().is_some_and(|c| c.is_whitespace()) {
                        chars.next();
                    }
                }
                other => out.push(other),
            },
            '{' if chars.peek() == Some(&'{') => {
                chars.next();
                out.push('{');
            }
            '}' if chars.peek() == Some(&'}') => {
                chars.next();
                out.push('}');
            }
            '{' => {
                for c in chars.by_ref() {
                    if c == '}' {
                        break;
                    }
                }
                out.push_str(&values(idx));
                idx += 1;
            }
            _ => out.push(c),
        }
    }
    Some(out)
}

struct Resolver<'a> {
    sources: Vec<&'a SourceRef>,
}

#[derive(Debug)]
struct Cause<'a> {
    candidates: Vec<&'a SourceRef>,
    /// The causes of the values captured by the best candidate's placeholders.
    nested: Vec<Cause<'a>>,
}

impl<'a> Resolver<'a> {
    /// All sources whose pattern matches the whole value, best first.
    fn candidates(&self, value: &str) -> Vec<&'a SourceRef> {
        let mut out: Vec<&SourceRef> = self
            .sources
            .iter()
            .copied()
            .filter(|s| s.captures(value).is_some())
            .collect();
        out.sort_by_key(|s| std::cmp::Reverse(s.quality));
        out
    }

    /// Resolve a value, recursing into the captured placeholder values, and splitting
    /// anyhow's `{:#}` chains ("outer: inner: leaf").  The reading that explains the most
    /// literal text wins, since a generic wrapper like `"Error: {0}"` matches anything.
    fn resolve(&self, value: &str, depth: usize) -> Vec<Cause<'a>> {
        self.resolve_scored(value, depth).1
    }

    fn resolve_scored(&self, value: &str, depth: usize) -> (usize, Vec<Cause<'a>>) {
        if depth > 6 || value.len() < 4 {
            return (0, vec![]);
        }
        let mut best: (usize, Vec<Cause<'a>>) = (0, vec![]);
        let candidates = self.candidates(value);
        if let Some(first) = candidates.first() {
            let mut score = first.quality;
            let mut nested = vec![];
            if let Some(caps) = first.captures(value) {
                for m in caps.iter().skip(1).flatten() {
                    let (s, c) = self.resolve_scored(m.as_str(), depth + 1);
                    score += s;
                    nested.extend(c);
                }
            }
            best = (score, vec![Cause { candidates, nested }]);
        }
        for (pos, _) in value.match_indices(": ") {
            let head_candidates = self.candidates(&value[..pos]);
            let Some(head) = head_candidates.first() else {
                continue;
            };
            let (tail_score, tail) = self.resolve_scored(&value[pos + 2..], depth + 1);
            let score = head.quality + tail_score;
            if score > best.0 {
                let mut causes = vec![Cause {
                    candidates: head_candidates,
                    nested: vec![],
                }];
                causes.extend(tail);
                best = (score, causes);
            }
        }
        best
    }
}

/// Simple deterministic PRNG so runs are repeatable.
struct Rng(u64);
impl Rng {
    fn next(&mut self, n: usize) -> usize {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 % n as u64) as usize
    }
}

fn rank_of(cands: &[&SourceRef], want: &SourceRef) -> Option<usize> {
    cands
        .iter()
        .position(|c| c.source_path == want.source_path && c.line_no == want.line_no)
}

/// Like `rank_of()`, but sources with identical text count as the same answer.
fn same_text_hit(cands: &[&SourceRef], want: &SourceRef) -> bool {
    cands
        .first()
        .is_some_and(|c| c.text == want.text || rank_of(&cands[..1], want).is_some())
}

fn main() {
    let root = std::env::args().nth(1).unwrap();
    let verbose = std::env::args().any(|a| a == "-v");
    let mut lm = LogMatcher::new();
    lm.add_root(&PathBuf::from(&root)).unwrap();
    let tracker = ProgressTracker::new();
    let _ = lm.discover_sources(&tracker);
    let _ = lm.extract_log_statements(&tracker);

    let all: Vec<&SourceRef> = lm.statements().collect();
    let resolver = Resolver {
        sources: all.iter().copied().filter(|s| is_source(s)).collect(),
    };
    let mut by_call: BTreeMap<&str, usize> = BTreeMap::new();
    for s in &resolver.sources {
        *by_call.entry(s.call_name.as_deref().unwrap()).or_default() += 1;
    }
    println!("== {root}");
    println!("error-message sources: {} {:?}", resolver.sources.len(), by_call);

    // A: render each source with sample values and resolve it back.
    let mut found = 0;
    let mut top = 0;
    let mut unique = 0;
    let mut total = 0;
    let mut cand_hist: BTreeMap<usize, usize> = BTreeMap::new();
    for s in &resolver.sources {
        let Some(msg) = render(&s.text, &mut |i| format!("/var/tmp/val{i}")) else {
            continue;
        };
        total += 1;
        let cands = resolver.candidates(&msg);
        let n = cands.len();
        *cand_hist.entry(n.min(10)).or_default() += 1;
        if rank_of(&cands, s).is_some() {
            found += 1;
        }
        if same_text_hit(&cands, s) {
            top += 1;
        }
        if n == 1 {
            unique += 1;
        }
        if verbose && n > 3 {
            println!("  ambiguous ({n}): {:?} <- {}", msg, id(s));
        }
    }
    println!(
        "A. round trip: {total} sources, found {found} ({:.0}%), best-ranked {top} ({:.0}%), single candidate {unique} ({:.0}%)",
        100.0 * found as f64 / total as f64,
        100.0 * top as f64 / total as f64,
        100.0 * unique as f64 / total as f64
    );
    println!("   candidates per message (10 = 10+): {cand_hist:?}");

    // Sources that end in a placeholder can wrap another error, like
    // `bail!("failed to read {}: {}", path, e)`.
    let wrappers: Vec<&SourceRef> = resolver
        .sources
        .iter()
        .copied()
        .filter(|s| s.text.trim_end_matches('"').ends_with('}'))
        .collect();
    let leaves: Vec<&SourceRef> = resolver
        .sources
        .iter()
        .copied()
        .filter(|s| !s.text.contains('{') && s.quality >= 8)
        .collect();

    // B: a wrapper with a leaf error in its last placeholder, resolved as a chain.
    let mut rng = Rng(0x2545F4914F6CDD1D);
    let trials = 500.min(wrappers.len() * leaves.len());
    let mut outer_ok = 0;
    let mut inner_ok = 0;
    for _ in 0..trials {
        let w = wrappers[rng.next(wrappers.len())];
        let l = leaves[rng.next(leaves.len())];
        let leaf_msg = render(&l.text, &mut |_| unreachable!()).unwrap();
        let mut count = 0;
        render(&w.text, &mut |_| {
            count += 1;
            String::new()
        });
        let msg = render(&w.text, &mut |i| {
            if i + 1 == count {
                leaf_msg.clone()
            } else {
                format!("val{i}")
            }
        })
        .unwrap();
        let causes = resolver.resolve(&msg, 0);
        let Some(first) = causes.first() else { continue };
        if same_text_hit(&first.candidates, w) {
            outer_ok += 1;
        }
        let inner_hit = first
            .nested
            .iter()
            .any(|c| same_text_hit(&c.candidates, l));
        if inner_hit {
            inner_ok += 1;
        } else if verbose {
            println!("  chain miss: {msg:?} wrapper={} leaf={}", id(w), id(l));
        }
    }
    println!(
        "B. wrapped chains ({trials} random wrapper+leaf): outer best {outer_ok} ({:.0}%), inner best {inner_ok} ({:.0}%)",
        100.0 * outer_ok as f64 / trials as f64,
        100.0 * inner_ok as f64 / trials as f64
    );

    // C: anyhow `{:#}` output, "context: leaf".
    let contexts: Vec<&SourceRef> = leaves
        .iter()
        .copied()
        .filter(|s| matches!(s.call_name.as_deref(), Some("context" | "with_context")))
        .collect();
    let mut c_ok = 0;
    let c_trials = 300;
    for _ in 0..c_trials {
        let a = contexts[rng.next(contexts.len())];
        let b = leaves[rng.next(leaves.len())];
        let msg = format!(
            "{}: {}",
            render(&a.text, &mut |_| unreachable!()).unwrap(),
            render(&b.text, &mut |_| unreachable!()).unwrap()
        );
        let causes = resolver.resolve(&msg, 0);
        let ok = causes.len() >= 2
            && same_text_hit(&causes[0].candidates, a)
            && same_text_hit(&causes[causes.len() - 1].candidates, b);
        if ok {
            c_ok += 1;
        }
    }
    println!(
        "C. anyhow {{:#}} chains ({c_trials} random context+leaf): both resolved {c_ok} ({:.0}%)",
        100.0 * c_ok as f64 / c_trials as f64
    );

    // D: end to end.  Find logging statements with an error-like argument, put a source's
    // message into that argument, match the line with log2src, and resolve the value.
    let err_expr = Regex::new(r"^(e|err|error|\w+_err|\w+_error|e\.to_string\(\))$").unwrap();
    let opts = LogMatchOptions::default();
    let mut logs = 0;
    let mut matched = 0;
    let mut exact_value = 0;
    let mut resolved = 0;
    let mut samples = vec![];
    for s in all.iter().filter(|s| {
        matches!(s.level, LogLevel::Warn | LogLevel::Error | LogLevel::Info) && !is_test(s)
    }) {
        // Probe with distinct values to find which placeholder holds the error.
        let Some(probe) = render(&s.text, &mut |i| format!("PROBE{i}X")) else {
            continue;
        };
        let lr = LogRefBuilder::new().with_body(Some(&probe)).build(&probe);
        let Some(mapping) = lm.match_log_statement(&lr, &opts) else {
            continue;
        };
        let Some(err_idx) = mapping.variables.iter().find_map(|v| {
            err_expr
                .is_match(v.expr.trim())
                .then(|| v.value.trim_start_matches("PROBE").trim_end_matches('X').parse::<usize>().ok())
                .flatten()
        }) else {
            continue;
        };
        logs += 1;
        let src = resolver.sources[rng.next(resolver.sources.len())];
        let Some(err_msg) = render(&src.text, &mut |i| format!("val{i}")) else {
            continue;
        };
        let line = render(&s.text, &mut |i| {
            if i == err_idx {
                err_msg.clone()
            } else {
                format!("arg{i}")
            }
        })
        .unwrap();
        let lr = LogRefBuilder::new().with_body(Some(&line)).build(&line);
        let Some(mapping) = lm.match_log_statement(&lr, &opts) else {
            continue;
        };
        let Some(src_ref) = mapping.src_ref else { continue };
        if src_ref.source_path != s.source_path || src_ref.line_no != s.line_no {
            continue;
        }
        matched += 1;
        let Some(var) = mapping
            .variables
            .iter()
            .find(|v| err_expr.is_match(v.expr.trim()))
        else {
            continue;
        };
        if var.value == err_msg {
            exact_value += 1;
        }
        let causes = resolver.resolve(&var.value, 0);
        if causes.first().is_some_and(|c| same_text_hit(&c.candidates, src)) {
            resolved += 1;
        }
        if samples.len() < 6 && causes.first().is_some_and(|c| c.candidates.len() == 1) {
            samples.push(format!(
                "  {line:?}\n    log  {} {}\n    cause {} {}",
                id(s),
                s.text,
                id(src),
                src.text
            ));
        }
    }
    println!(
        "D. end to end: {logs} log statements with an error arg, matched {matched}, value extracted exactly {exact_value}, cause resolved {resolved} ({:.0}% of matched)",
        100.0 * resolved as f64 / matched.max(1) as f64
    );
    for s in samples {
        println!("{s}");
    }
}
