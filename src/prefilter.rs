use crate::source_hier::SourceFileID;
use crate::StatementsInFile;
use aho_corasick::{AhoCorasick, MatchKind};
use regex_syntax::hir::{Hir, HirKind};
use std::collections::HashMap;

/// Identifies a single log statement: the file it is in and its index in that file's
/// `log_statements`.
pub(crate) type StatementID = (SourceFileID, usize);

/// A prefilter for finding the log statements that could possibly match a log message.
///
/// The patterns generated for log statements are mostly literal text with `(.+)` in place of
/// the format placeholders.  So, we pick the longest literal run out of each pattern and put
/// them all into a single Aho-Corasick automaton.  A log message is then scanned once to find
/// the candidate statements, and only those have their full regex evaluated.
#[derive(Debug)]
pub(crate) struct Prefilter {
    ac: AhoCorasick,
    /// Indexed by Aho-Corasick pattern ID, the statements whose key literal is that pattern.
    by_literal: Vec<Vec<StatementID>>,
    /// Statements that did not have a usable literal and must always be checked.
    always: Vec<StatementID>,
}

impl Prefilter {
    pub(crate) fn new<'a>(files: impl Iterator<Item = &'a StatementsInFile>) -> Self {
        let mut literal_ids: HashMap<Vec<u8>, usize> = HashMap::new();
        let mut literals: Vec<Vec<u8>> = Vec::new();
        let mut by_literal: Vec<Vec<StatementID>> = Vec::new();
        let mut always = Vec::new();

        for sif in files {
            for (index, stmt) in sif.log_statements.iter().enumerate() {
                let sid = (sif.id, index);
                match longest_literal(stmt.pattern.as_str()) {
                    Some(lit) => {
                        let lit_id = *literal_ids.entry(lit.clone()).or_insert_with(|| {
                            literals.push(lit);
                            by_literal.push(Vec::new());
                            literals.len() - 1
                        });
                        by_literal[lit_id].push(sid);
                    }
                    None => always.push(sid),
                }
            }
        }

        let ac = AhoCorasick::builder()
            .match_kind(MatchKind::Standard)
            .build(&literals)
            .expect("literal set should build");
        Self {
            ac,
            by_literal,
            always,
        }
    }

    /// Call `f` with each statement that might match the given text.
    pub(crate) fn candidates(&self, text: &str, mut f: impl FnMut(StatementID)) {
        let mut hits: Vec<usize> = self
            .ac
            .find_overlapping_iter(text)
            .map(|m| m.pattern().as_usize())
            .collect();
        hits.sort_unstable();
        hits.dedup();
        for lit_id in hits {
            self.by_literal[lit_id].iter().copied().for_each(&mut f);
        }
        self.always.iter().copied().for_each(f);
    }
}

/// Parse the regex and return the longest run of literal bytes that any match must contain.
fn longest_literal(pattern: &str) -> Option<Vec<u8>> {
    fn walk(hir: &Hir, cur: &mut Vec<u8>, best: &mut Vec<u8>) {
        match hir.kind() {
            HirKind::Literal(lit) => cur.extend_from_slice(&lit.0),
            // Zero-width, so literals on either side are still adjacent in the haystack.
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
    let mut cur = Vec::new();
    let mut best = Vec::new();
    walk(&hir, &mut cur, &mut best);
    flush(&mut cur, &mut best);
    if best.is_empty() {
        None
    } else {
        Some(best)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_longest_literal() {
        assert_eq!(
            longest_literal(r"(?s)^Hello from foo i=(.+)$"),
            Some(b"Hello from foo i=".to_vec())
        );
        assert_eq!(
            longest_literal(r"(?s)^a=(.+) and then b=(.+)$"),
            Some(b" and then b=".to_vec())
        );
        assert_eq!(
            longest_literal(r"(?s)^x\.y\{(.+)\}$"),
            Some(b"x.y{".to_vec())
        );
        assert_eq!(longest_literal(r"(?s)^(.+)$"), None);
    }
}
