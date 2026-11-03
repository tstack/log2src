use crate::source_hier::SourceFileID;
use crate::{Statement, StatementsInFile};
use aho_corasick::{AhoCorasick, MatchKind};
use rayon::prelude::*;
use regex_syntax::hir::{Hir, HirKind};
use std::collections::HashMap;

/// Identifies a single log statement: the file it is in and its index in that file's
/// `statements()`.
pub(crate) type StatementID = (SourceFileID, usize);

/// A prefilter for finding the log statements that could possibly match a log message.
///
/// The patterns generated for log statements are mostly literal text with `(.*)` in place of
/// the format placeholders.  So, we pick the longest literal run out of each pattern and put
/// them all into a single Aho-Corasick automaton.  A log message is then scanned once to find
/// the candidate statements, and only those have their full regex evaluated.  The literals that
/// are a single byte, like the `=` in `"%s=%d"`, are looked up by byte instead, since an
/// automaton that reports overlapping matches copies them into nearly every one of its states,
/// which made building it for the Linux kernel take 15 seconds instead of one.
#[derive(Debug)]
pub(crate) struct Prefilter {
    ac: AhoCorasick,
    /// Indexed by Aho-Corasick pattern ID, the statements whose key literal is that pattern.
    by_literal: Vec<Vec<StatementID>>,
    /// Indexed by byte, the statements whose key literal is that single byte.
    by_byte: Vec<Vec<StatementID>>,
    /// Statements that did not have a usable literal and must always be checked.
    always: Vec<StatementID>,
    /// The position of each file in the order of their paths, so candidates can be ordered by
    /// their location without comparing the paths.
    ranks: HashMap<SourceFileID, u32>,
}

impl Prefilter {
    /// Index the statements in `files` that `keep` accepts.  A statement's index is still its
    /// position in `matchable_statements()`, so a [`StatementID`] is the same in every
    /// prefilter.
    pub(crate) fn new<'a>(
        files: impl Iterator<Item = &'a StatementsInFile>,
        keep: impl Fn(&Statement) -> bool,
    ) -> Self {
        let mut files: Vec<&StatementsInFile> = files.collect();
        files.sort_unstable_by(|lhs, rhs| lhs.path.cmp(&rhs.path));
        let ranks = files
            .iter()
            .zip(0..)
            .map(|(sif, rank)| (sif.id, rank))
            .collect();
        let mut literal_ids: HashMap<Vec<u8>, usize> = HashMap::new();
        let mut literals: Vec<Vec<u8>> = Vec::new();
        let mut by_literal: Vec<Vec<StatementID>> = Vec::new();
        let mut by_byte: Vec<Vec<StatementID>> = vec![Vec::new(); 256];
        let mut always = Vec::new();

        // Parsing the patterns is most of the work for a big tree, so it is done in parallel.
        let keyed: Vec<(StatementID, Option<Vec<u8>>)> = files
            .iter()
            .flat_map(|sif| {
                sif.matchable_statements()
                    .enumerate()
                    .filter(|(_, stmt)| keep(stmt))
                    .map(move |(index, stmt)| ((sif.id, index), stmt))
            })
            .collect::<Vec<_>>()
            .into_par_iter()
            .map(|(sid, stmt)| (sid, longest_literal(&stmt.pattern_source())))
            .collect();
        for (sid, lit) in keyed {
            match lit {
                Some(lit) if lit.len() == 1 => by_byte[usize::from(lit[0])].push(sid),
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

        let ac = AhoCorasick::builder()
            .match_kind(MatchKind::Standard)
            .build(&literals)
            .expect("literal set should build");
        Self {
            ac,
            by_literal,
            by_byte,
            always,
            ranks,
        }
    }

    /// The position of a file in the order of the paths of the files, which is the same as
    /// comparing the paths.
    pub(crate) fn rank(&self, file_id: SourceFileID) -> u32 {
        self.ranks.get(&file_id).copied().unwrap_or(u32::MAX)
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
        let mut seen = [false; 256];
        for byte in text.bytes() {
            let byte = usize::from(byte);
            if !std::mem::replace(&mut seen[byte], true) {
                self.by_byte[byte].iter().copied().for_each(&mut f);
            }
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
            longest_literal(r"(?s)^Hello from foo i=(.*)$"),
            Some(b"Hello from foo i=".to_vec())
        );
        assert_eq!(
            longest_literal(r"(?s)^a=(.*) and then b=(.*)$"),
            Some(b" and then b=".to_vec())
        );
        assert_eq!(
            longest_literal(r"(?s)^x\.y\{(.*)\}$"),
            Some(b"x.y{".to_vec())
        );
        assert_eq!(longest_literal(r"(?s)^(.*)$"), None);
    }
}
