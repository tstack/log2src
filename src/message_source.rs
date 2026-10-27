//! Find the statements that could have produced a message, like one copied from a log, a
//! screenshot, or a dialog in a GUI.  A message is often built out of other messages, like the
//! error in `"Unable to read file: {}"`, so the values of the placeholders are looked up too.

use crate::{compare_candidates, first_match, MessageCategory, SourceRef, MIN_FALLBACK_QUALITY};
use serde::Serialize;

/// The statements that could have produced some text in a message.
#[derive(Debug, Serialize)]
pub struct MessageSource<'s> {
    /// The text that was looked up.
    pub text: String,
    /// The statements whose pattern matches all of the text, best first.  It is empty if none
    /// match, like for an error from a library or the operating system.
    pub candidates: Vec<&'s SourceRef>,
    /// The sources of the values of the best candidate's placeholders, like the error in
    /// `"Unable to read file: {}"`.  Values that are too short to look up are left out.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub causes: Vec<MessageSource<'s>>,
    /// The candidates only share some literal text with the text, since none match all of it,
    /// like for a fragment of a message that was copied from a GUI.
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub partial: bool,
}

/// How deep to look up the values of placeholders, which also stops runaway recursion for a
/// pattern like `"{}: {}"`.
const MAX_DEPTH: usize = 6;

/// Values shorter than this are not looked up, since they would match all sorts of statements.
const MIN_VALUE_LEN: usize = 4;

/// The least amount of literal text, not counting whitespace, that a statement has to share with
/// a fragment of a message.
const MIN_FRAGMENT_LEN: usize = 10;

/// The most candidates to return for a fragment, since a lot of statements can share a few words.
const MAX_FRAGMENT_CANDIDATES: usize = 10;

/// Find the sources of a message in the given statements.  More than one source is returned
/// when the message is a chain of messages, like `"outer: inner: leaf"` from anyhow's `{:#}`,
/// and no statement matches all of it.  The reading of the message that explains the most
/// literal text wins, since a generic wrapper, like `"Error: {}"`, matches anything.  Statements
/// with too little literal text, like `warn!("{}: {}", a, b)`, are not used, even log
/// statements, since they would be the source of all sorts of messages.
pub fn find_message_sources<'s>(
    statements: impl IntoIterator<Item = &'s SourceRef>,
    message: &str,
) -> Vec<MessageSource<'s>> {
    let finder = Finder {
        statements: statements
            .into_iter()
            .filter(|stmt| stmt.quality >= MIN_FALLBACK_QUALITY)
            .collect(),
    };
    let message = message.trim();
    let sources = finder.resolve(message, 0, true).1;
    if !sources.is_empty() {
        return sources;
    }
    // Text copied from a GUI is often wrapped differently than the message.
    let collapsed = collapse_whitespace(message);
    let sources = finder.resolve(&collapsed, 0, true).1;
    if !sources.is_empty() {
        return sources;
    }
    // A message with some text in front of it, like `"Error: "` added by a dialog.
    let mut best = (0, vec![]);
    for (pos, sep) in collapsed.match_indices(": ") {
        let (score, mut sources) = finder.resolve(&collapsed[pos + sep.len()..], 0, true);
        if score > best.0 {
            sources.insert(0, MessageSource::unknown(&collapsed[..pos]));
            best = (score, sources);
        }
    }
    if !best.1.is_empty() {
        return best.1;
    }
    finder.fragment(&collapsed).into_iter().collect()
}

struct Finder<'s> {
    statements: Vec<&'s SourceRef>,
}

impl<'s> Finder<'s> {
    /// The statements that match all of `text`, best first.  The message itself could have come
    /// from anywhere, so all categories are used.  A value of a placeholder is a message that was
    /// made somewhere else, so only the errors and formatted messages are used for those.  The
    /// statements are ordered, and the best one is chosen, the same way as when matching a log
    /// line, so the answer agrees with `LogMatcher::match_log_statement()`.
    fn candidates(&self, text: &str, top: bool) -> Vec<&'s SourceRef> {
        let mut retval: Vec<&SourceRef> = self
            .statements
            .iter()
            .copied()
            .filter(|stmt| {
                top || matches!(
                    stmt.category,
                    MessageCategory::Error | MessageCategory::Format
                )
            })
            .filter(|stmt| stmt.pattern.is_match(text))
            .collect();
        retval.sort_by(|lhs, rhs| compare_candidates(lhs, rhs, None, None));
        let best = first_match(
            retval.iter().copied().enumerate(),
            text,
            None,
            |candidate: &(usize, &'s SourceRef)| candidate.1,
        );
        if let Some((index, _)) = best {
            let best = retval.remove(index);
            retval.insert(0, best);
        }
        retval
    }

    /// Find the sources of `text` and the amount of literal text they explain.
    fn resolve(&self, text: &str, depth: usize, top: bool) -> (usize, Vec<MessageSource<'s>>) {
        if depth > MAX_DEPTH || text.len() < MIN_VALUE_LEN {
            return (0, vec![]);
        }
        let mut best = match self.source(text, depth, top) {
            Some((score, source)) => (score, vec![source]),
            None => (0, vec![]),
        };
        // A chain of messages, like `"outer: inner: leaf"`, where each part was made separately.
        // A statement that matches all of the text wins a tie, like `"Unable to start: {:#}"`
        // with the whole chain in its placeholder.
        for (pos, sep) in text.match_indices(": ") {
            let Some((head_score, head)) = self.source(&text[..pos], depth, top) else {
                continue;
            };
            let tail_text = &text[pos + sep.len()..];
            let (tail_score, mut tail) = self.resolve(tail_text, depth + 1, false);
            let score = head_score + tail_score;
            if score > best.0 {
                if tail.is_empty() {
                    tail.push(MessageSource::unknown(tail_text));
                }
                tail.insert(0, head);
                best = (score, tail);
            }
        }
        best
    }

    /// The statements that match all of `text`, with the sources of the values of the best
    /// one's placeholders, and the amount of literal text they explain.
    fn source(&self, text: &str, depth: usize, top: bool) -> Option<(usize, MessageSource<'s>)> {
        let candidates = self.candidates(text, top);
        let first = candidates.first()?;
        let mut score = first.quality;
        let mut causes = vec![];
        if let Some(captures) = first.captures(text) {
            for value in captures.iter().skip(1).flatten() {
                let value = value.as_str().trim();
                if value.len() < MIN_VALUE_LEN {
                    continue;
                }
                let (value_score, value_sources) = self.resolve(value, depth + 1, false);
                score += value_score;
                if value_sources.is_empty() {
                    causes.push(MessageSource::unknown(value));
                }
                causes.extend(value_sources);
            }
        }
        let source = MessageSource {
            text: text.to_string(),
            candidates,
            causes,
            partial: false,
        };
        Some((score, source))
    }

    /// The statements that share the most literal text with `text`, which is not all of a
    /// message, like a fragment of one or one with extra text around it.  The whitespace in
    /// `text` should already be collapsed.
    fn fragment(&self, text: &str) -> Option<MessageSource<'s>> {
        let mut scored: Vec<(usize, &'s SourceRef)> = self
            .statements
            .iter()
            .map(|stmt| (shared_literal_len(stmt, text), *stmt))
            .filter(|(score, _)| *score >= MIN_FRAGMENT_LEN)
            .collect();
        scored.sort_by(|(lhs_score, lhs), (rhs_score, rhs)| {
            rhs_score
                .cmp(lhs_score)
                .then_with(|| compare_candidates(lhs, rhs, None, None))
        });
        scored.truncate(MAX_FRAGMENT_CANDIDATES);
        if scored.is_empty() {
            return None;
        }
        Some(MessageSource {
            text: text.to_string(),
            candidates: scored.into_iter().map(|(_, stmt)| stmt).collect(),
            causes: vec![],
            partial: true,
        })
    }
}

/// Replace each run of whitespace with a single space and trim the ends.
fn collapse_whitespace(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// The amount of literal text, not counting whitespace, that a statement shares with `text`.
/// The literal parts of the statement that are in the text count, like `"Unable to read "` in
/// `"Unable to read file"`.  When the text is only part of the message, the text can also be
/// in a literal part, or overlap the start or end of one, like `"read file: denied"` for
/// `"Unable to read file: {}"`.
fn shared_literal_len(stmt: &SourceRef, text: &str) -> usize {
    let non_ws = |s: &str| s.chars().filter(|c| !c.is_whitespace()).count();
    let mut contained = 0;
    let mut overlap = 0;
    for segment in &stmt.segments {
        let segment = collapse_whitespace(segment);
        if segment.is_empty() {
            continue;
        }
        if text.contains(&segment) {
            contained += non_ws(&segment);
        } else if segment.contains(text) {
            overlap = overlap.max(non_ws(text));
        } else {
            overlap = overlap.max(non_ws(edge_overlap(&segment, text)));
        }
    }
    contained.max(overlap)
}

/// The longest piece of `text` that is at the end of `segment` and the start of `text`, or the
/// start of `segment` and the end of `text`.
fn edge_overlap<'t>(segment: &str, text: &'t str) -> &'t str {
    let mut best = "";
    for (pos, _) in text.char_indices().skip(1) {
        let (head, tail) = text.split_at(pos);
        if head.len() > best.len() && segment.ends_with(head) {
            best = head;
        }
        if tail.len() > best.len() && segment.starts_with(tail) {
            best = tail;
        }
    }
    best
}

impl MessageSource<'_> {
    /// Text that no statement produced.
    fn unknown(text: &str) -> Self {
        MessageSource {
            text: text.to_string(),
            candidates: vec![],
            causes: vec![],
            partial: false,
        }
    }
}
