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
}

/// How deep to look up the values of placeholders, which also stops runaway recursion for a
/// pattern like `"{}: {}"`.
const MAX_DEPTH: usize = 6;

/// Values shorter than this are not looked up, since they would match all sorts of statements.
const MIN_VALUE_LEN: usize = 4;

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
    finder.resolve(message.trim(), 0, true).1
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
        };
        Some((score, source))
    }
}

impl MessageSource<'_> {
    /// Text that no statement produced.
    fn unknown(text: &str) -> Self {
        MessageSource {
            text: text.to_string(),
            candidates: vec![],
            causes: vec![],
        }
    }
}
