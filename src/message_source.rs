//! Find the statements that could have produced a message, like one copied from a log, a
//! screenshot, or a dialog in a GUI.  A message is often built out of other messages, like the
//! error in `"Unable to read file: {}"`, so the values of the placeholders are looked up too.
//! Text that is built up in pieces, like SQL that is appended to a `StringBuilder`, is explained
//! by the statements that added each piece.

use crate::source_ref::regex_literal_pieces;
use crate::{
    compare_candidates, first_match, MessageCategory, Statement, StatementRef, MIN_FALLBACK_QUALITY,
};
use serde::Serialize;
use std::cell::RefCell;
use std::collections::HashMap;

/// The statements that could have produced some text in a message.
#[derive(Clone, Debug, Serialize)]
pub struct MessageSource<'s> {
    /// The text that was looked up.
    pub text: String,
    /// The statements whose pattern matches all of the text, best first.  It is empty if none
    /// match, like for an error from a library or the operating system.
    pub candidates: Vec<StatementRef<'s>>,
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

/// How many of the `": "` separators in a text are tried as the end of a prefix or the head of a
/// chain.  Each one is a reading of the rest of the text, so trying all of them is quadratic in
/// a large message, like a JSON document, which has one for every field.  A prefix or the head
/// of a chain is a few words, so it is in front of the first few separators.
const MAX_SPLITS: usize = 8;

/// The longest prefix, in bytes, that is looked for in front of where a statement's text starts,
/// see `Finder::prefix_splits()`.  A prefix is a few words, like the device name that the Linux
/// kernel's `dev_info()` adds, `"[worker-3]"`, or `"<12>"`, while a statement's text can be found
/// almost anywhere in a long message that has a lot of punctuation, like a JSON document.
const MAX_PREFIX_LEN: usize = 64;

/// How much of a log message [`best_log_source`] reads for a prefix or the head of a chain.
/// Those are at the start of a message, and the rest can be very long, like a dump of a
/// service's status that is hundreds of kilobytes, where every reading runs the statements'
/// regexes over all of it.  A message that is not longer than this is read whole.
pub(crate) const MAX_LOG_HEAD_LEN: usize = 1024;

/// The least amount of literal text, not counting whitespace, that a statement has to share with
/// a fragment of a message.
const MIN_FRAGMENT_LEN: usize = 10;

/// The most candidates to return for a fragment, since a lot of statements can share a few words.
const MAX_FRAGMENT_CANDIDATES: usize = 10;

/// The least amount of literal text, not counting whitespace, that a statement needs to be one
/// of the pieces of a text that was built up, like the `" AND x = ?"` appended to some SQL.  A
/// piece from a function other than the one that explains the most of the text needs
/// [`MIN_FRAGMENT_LEN`], since short pieces of text are in all sorts of places.
const MIN_PIECE_LEN: usize = 4;

/// How many places in a text are tried for each statement, so a short piece, like `" OR "`,
/// does not blow up the number of readings.
const MAX_PIECE_PLACES: usize = 64;

/// Find the sources of a message in the given statements.  More than one source is returned
/// when the message is a chain of messages, like `"outer: inner: leaf"` from anyhow's `{:#}`,
/// and no statement matches all of it.  The reading of the message that explains the most
/// literal text wins, since a generic wrapper, like `"Error: {}"`, matches anything.  Statements
/// with too little literal text, like `warn!("{}: {}", a, b)`, are not used, even log
/// statements, since they would be the source of all sorts of messages.
pub fn find_message_sources<'s>(
    statements: impl IntoIterator<Item = StatementRef<'s>>,
    message: &str,
) -> Vec<MessageSource<'s>> {
    let finder = Finder {
        statements: statements
            .into_iter()
            .filter(|stmt| stmt.quality >= MIN_FALLBACK_QUALITY)
            .collect(),
        relaxed: false,
        top_log_only: false,
        memo: RefCell::default(),
    };
    let message = message.trim();
    let collapsed = collapse_whitespace(message);
    let mut best = finder.prefixed_resolve(message);
    // Text copied from a GUI, a man page, or a terminal is often wrapped and indented
    // differently than the message, or has one space where the message has two, so the
    // whitespace is ignored too.  The exact whitespace wins a tie.
    let relaxed = Finder {
        statements: finder.statements.clone(),
        relaxed: true,
        top_log_only: false,
        memo: RefCell::default(),
    };
    let loose = relaxed.prefixed_resolve(&collapsed);
    if loose.0 > best.0 || (best.1.is_empty() && !loose.1.is_empty()) {
        best = loose;
    }
    // A text that was built up in pieces, like SQL, can be explained by a generic statement,
    // like `"SELECT " + x`, but the pieces explain a lot more of it.
    let assembled = finder.assemble(&collapsed);
    if best.0 > 0 {
        return match assembled {
            Some((score, sources)) if score > best.0 => sources,
            _ => best.1,
        };
    }
    // No statement matches all of the text, or only one whose values do not fit its format
    // string, like `"%d messages"` for a fragment of a sentence that ends in "messages".  The
    // text is pieces or a fragment of other statements, and the reading that shares the most
    // literal text wins.
    let fragment = finder.fragment(&collapsed);
    match (assembled, fragment) {
        (Some((assembled_score, sources)), fragment)
            if fragment
                .as_ref()
                .is_none_or(|(fragment_score, _)| assembled_score > *fragment_score) =>
        {
            sources
        }
        (_, Some((_, fragment))) => vec![fragment],
        (_, None) => best.1,
    }
}

/// The statement that produced the most of a log message, when that is not all of it.  This
/// uses the same readings as [`find_message_sources`], like a prefix that is not from any
/// statement or a chain of messages, like `"outer: inner"`, so a log line can be matched when a
/// generic statement, like `"%s: %s"`, is the only one that matches all of it.  The statement
/// is the first one in the reading, which is the outermost one for a chain, since the others
/// made the values in it.  A reading of the whole message is left to the caller, which has
/// better evidence for choosing between the statements that match all of it, like the line
/// number in the log message.  Fragments are not used, since a statement that only shares some
/// text with the line is usually not where it came from.  The whitespace is not collapsed
/// either, since a log line has the same whitespace as the message.
pub(crate) fn best_log_source<'s>(
    statements: impl IntoIterator<Item = StatementRef<'s>>,
    body: &str,
    fallback: bool,
) -> Option<LogSource<'s>> {
    let finder = Finder {
        statements: statements
            .into_iter()
            .filter(|stmt| stmt.quality >= MIN_FALLBACK_QUALITY)
            .collect(),
        relaxed: false,
        top_log_only: !fallback,
        memo: RefCell::default(),
    };
    if finder.statements.is_empty() {
        return None;
    }
    let body = body.trim();
    let head = log_head(body);
    let (score, sources) = finder.prefixed_resolve(head);
    // A reading of the whole message is left to the caller, see above, even when only the
    // head was read.
    if sources.len() == 1 {
        return None;
    }
    // A prefix that is not from any statement is only ever the first in the reading.
    let prefix = sources
        .first()
        .filter(|source| source.candidates.is_empty())
        .map(|source| source.text.clone());
    // The sources are the parts of the head, in order, so only the last one runs to its end.
    let last = sources.len().saturating_sub(1);
    let prefixed_statement = prefix.is_some() && sources.len() == 2;
    let (index, source) = sources
        .into_iter()
        .enumerate()
        .find(|(_, source)| !source.candidates.is_empty())?;
    let MessageSource {
        text, candidates, ..
    } = source;
    let stmt = candidates.into_iter().next()?;
    let text = if index == last && head.len() != body.len() {
        let head_len = text.len();
        let text = finder.whole_text(stmt, text, head, body);
        // The statement did not produce the rest of the message, so its values would be cut
        // off at the end of the head, which is no better than not explaining the message.
        if text.len() == head_len {
            return None;
        }
        text
    } else {
        text
    };
    // The prefix and this statement are all of the message.
    let start = prefixed_statement.then(|| body.len() - text.len());
    Some(LogSource {
        score,
        stmt,
        text,
        prefix,
        start,
    })
}

/// The part of a log message's body that [`best_log_source`] reads: all of it, if it is not
/// longer than [`MAX_LOG_HEAD_LEN`] bytes, or else the lines that fit, or the start of the first
/// line if it does not fit.  It is always the start of the body, so the rest is
/// `&body[head.len()..]`.
pub(crate) fn log_head(body: &str) -> &str {
    if body.len() <= MAX_LOG_HEAD_LEN {
        return body;
    }
    let end = body.floor_char_boundary(MAX_LOG_HEAD_LEN);
    let start = &body[..end];
    match start.rfind('\n') {
        Some(pos) => start[..pos].trim_end_matches('\r'),
        None => start,
    }
}

/// The statement that produced the most of a log message, from [`best_log_source`].
pub(crate) struct LogSource<'s> {
    /// The amount of literal text explained by the reading of the message.
    pub score: usize,
    /// The statement.
    pub stmt: StatementRef<'s>,
    /// The part of the message that the statement produced.
    pub text: String,
    /// The text at the start of the message that no statement produced, if any.
    pub prefix: Option<String>,
    /// Where the statement's text starts in the trimmed message, when the reading is only the
    /// prefix and the statement, so the same reading can be found for other messages from the
    /// statement with a pattern for the prefix, see `SourceTree::learned_match()`.
    pub start: Option<usize>,
}

/// Where a prefix that is not from any statement ends in `message`, without its separator, if
/// the text at `start` can follow one.  The prefix has to end with punctuation and then
/// whitespace, like `"usb 1-5: "` or `"svc | "`, a closing bracket, like `"[worker-3]"` or
/// `"<12>"`, or a tab, so the separator does not have to be known.  A statement whose text
/// starts after a space between words, like `"open file: %s"` in `"Failed to open file: x"`, is
/// a fragment of another message, and one right after other punctuation, like the
/// `"properties"` in `"jcc.properties"` or a value in a JSON document, is part of a word or a
/// value, not what follows a prefix.  A separator, like the `:` or `|`, is not part of the
/// prefix, but a closing bracket is.
/// Where the text after a prefix could start in a trimmed log message, for a prefix that was
/// learned to end with `separator`, see `SourceTree::learned_match()`.  These are after the
/// first few times the separator is in the message, the same as the `": "` that are tried by
/// [`best_log_source`], and only where a prefix could end, see [`prefix_end`].
pub(crate) fn learned_prefix_starts<'a>(
    message: &'a str,
    separator: &'a str,
) -> impl Iterator<Item = usize> + 'a {
    message
        .match_indices(separator)
        .take(MAX_SPLITS)
        .map(move |(pos, sep)| pos + sep.len())
        .filter(move |start| prefix_end(message, *start).is_some())
}

pub(crate) fn prefix_end(message: &str, start: usize) -> Option<usize> {
    let before = message.get(..start)?;
    let trimmed = before.trim_end();
    let last = trimmed.chars().next_back()?;
    let space = &before[trimmed.len()..];
    let ends_prefix = if space.contains('\t') {
        true
    } else if space.is_empty() {
        matches!(last, ']' | ')' | '>' | '}')
    } else {
        !last.is_alphanumeric()
    };
    if !ends_prefix {
        return None;
    }
    let end = if matches!(last, ':' | '|' | ';' | ',' | '-' | '=' | '~') {
        trimmed.len() - last.len_utf8()
    } else {
        trimmed.len()
    };
    let prefix = message[..end].trim_end();
    (!prefix.is_empty()).then_some(prefix.len())
}

impl<'s> Finder<'s> {
    /// Find the sources of a whole message, which could have some text in front of it that is
    /// not from any statement, like `"Error: "` added by a dialog or the device name that the
    /// Linux kernel's `dev_info()` adds.  The readings with and without the text in front are
    /// compared by the amount of literal text they explain, so a generic statement that matches
    /// all of the message, like `"%s [%s]"`, does not hide a better one for the rest of it.  The
    /// whole message wins a tie, like a wrapper whose value is explained too.
    fn prefixed_resolve(&self, message: &str) -> (usize, Vec<MessageSource<'s>>) {
        self.memo.borrow_mut().reset(message);
        let mut best = self.resolve(message, 0, true);
        for (start, prefix_len) in self.prefix_splits(message) {
            let (score, mut sources) = self.resolve(&message[start..], 0, true);
            if !sources.is_empty() && score > best.0 {
                sources.insert(0, MessageSource::unknown(&message[..prefix_len]));
                best = (score, sources);
            }
        }
        best
    }

    /// Where the text after a prefix could start in `message`, with the length of the prefix,
    /// see [`prefix_end`].  These are after the first few `": "`, which can also start a chain
    /// of messages, like `"usb 1-5: Unable to start: No such file"`, and where the leading
    /// literal text of a statement is, whatever the separator in front of it is, like
    /// `"[worker-3] "`, which only has to be found, not matched, since the text after the prefix
    /// is resolved anyway.
    fn prefix_splits(&self, message: &str) -> Vec<(usize, usize)> {
        let mut starts: Vec<usize> = message
            .match_indices(": ")
            .take(MAX_SPLITS)
            .map(|(pos, sep)| pos + sep.len())
            .collect();
        // A relaxed pattern can match where the literal text is not.  A statement whose
        // text starts with whitespace, like `.append(" is already a named search")`, is a piece
        // added to some other text, not the start of a message after a prefix.
        if !self.relaxed {
            // The places a prefix can end are few, so each statement only has to be checked
            // for starting at one of them, and once all of them were found, the rest of the
            // statements do not have to be checked.
            let mut places: Vec<(usize, bool)> = (1..=MAX_PREFIX_LEN.min(message.len()))
                .filter(|start| message.is_char_boundary(*start))
                .filter(|start| prefix_end(message, *start).is_some())
                .map(|start| (start, false))
                .collect();
            let mut remaining = places.len();
            for stmt in self
                .statements
                .iter()
                .filter(|stmt| self.usable(stmt, true))
            {
                if remaining == 0 {
                    break;
                }
                let Some(literal) = stmt
                    .leading_literal()
                    .filter(|literal| !literal.starts_with(char::is_whitespace))
                else {
                    continue;
                };
                // The text has to fit after the prefix, but the rest of the statement is checked
                // when the text is resolved.
                if let Some(place) = places
                    .iter_mut()
                    .find(|(start, _)| message[*start..].starts_with(literal))
                    .filter(|(_, found)| !*found)
                {
                    place.1 = true;
                    remaining -= 1;
                }
            }
            starts.extend(
                places
                    .into_iter()
                    .filter_map(|(start, found)| found.then_some(start)),
            );
        }
        starts.sort_unstable();
        starts.dedup();
        starts
            .into_iter()
            .filter_map(|start| Some((start, prefix_end(message, start)?)))
            .collect()
    }
}

struct Finder<'s> {
    statements: Vec<StatementRef<'s>>,
    /// Use `Statement::relaxed_pattern()`, which ignores differences in whitespace, for text
    /// whose whitespace was collapsed.
    relaxed: bool,
    /// Only use logging calls for the whole text, not just for the parts of it, like when
    /// matching a log line without [`crate::LogMatchOptions::fallback`].
    top_log_only: bool,
    /// The answers already worked out for this message.  The readings of a message overlap a
    /// lot: each `": "` is tried as the end of a prefix and as the end of the head of a chain,
    /// and the tails of those are tried again a level down, so the same text is looked up many
    /// times.
    memo: RefCell<Memo<'s>>,
}

/// What [`Finder`] has already worked out for the message given to
/// [`Finder::prefixed_resolve`].  The texts that are looked up are all slices of that message, so
/// they are keyed by where they are in it ([`Memo::key`]), instead of copying and hashing them.
/// Indexed by `top`, since that changes the statements that are used.
#[derive(Default)]
struct Memo<'s> {
    /// Where the message is, as the address of its first byte and its length.
    message: (usize, usize),
    /// [`Finder::candidates`].
    candidates: [HashMap<(usize, usize), Vec<StatementRef<'s>>>; 2],
    /// [`Finder::resolve`], by depth too, since that limits how far down the values are looked
    /// up.
    resolved: [HashMap<(usize, usize, usize), (usize, Vec<MessageSource<'s>>)>; 2],
}

impl Memo<'_> {
    /// Forget everything and remember the answers for `message` from now on.
    fn reset(&mut self, message: &str) {
        *self = Memo {
            message: (message.as_ptr() as usize, message.len()),
            ..Memo::default()
        };
    }

    /// The offset and length of `text` in the message, or None if it is not a slice of it, so
    /// it is not remembered.
    fn key(&self, text: &str) -> Option<(usize, usize)> {
        let (start, len) = self.message;
        let offset = (text.as_ptr() as usize).checked_sub(start)?;
        (offset + text.len() <= len).then_some((offset, text.len()))
    }
}

impl<'s> Finder<'s> {
    /// The text that `stmt` produced, given the part at the end of the [`log_head`] that it
    /// explains.  The statement most likely produced the rest of the message too, like the lines
    /// of a stack trace in its last placeholder, so the rest is added if the statement matches it
    /// and its values still fit, so its values are extracted from all of it.
    fn whole_text(&self, stmt: StatementRef, text: String, head: &str, body: &str) -> String {
        if head.len() == body.len() {
            return text;
        }
        let whole = format!("{text}{}", &body[head.len()..]);
        if self.pattern(&stmt).is_match(&whole)
            && (self.fits(&stmt, &whole) || !self.fits(&stmt, &text))
        {
            whole
        } else {
            text
        }
    }

    /// The regex for matching text to a statement.
    fn pattern<'a>(&self, stmt: &'a Statement) -> &'a regex::Regex {
        if self.relaxed {
            stmt.relaxed_pattern()
        } else {
            stmt.pattern()
        }
    }

    /// The statements that match all of `text`, best first.  The message itself could have come
    /// from anywhere, so all categories are used.  A value of a placeholder is a message that was
    /// made somewhere else, so only the errors and formatted messages are used for those.  The
    /// statements are ordered, and the best one is chosen, the same way as when matching a log
    /// line, so the answer agrees with `LogMatcher::match_log_statement()`.
    fn candidates(&self, text: &str, top: bool) -> Vec<StatementRef<'s>> {
        let key = self.memo.borrow().key(text);
        if let Some(found) = key.and_then(|key| {
            self.memo.borrow().candidates[top as usize]
                .get(&key)
                .cloned()
        }) {
            return found;
        }
        let retval = self.find_candidates(text, top);
        if let Some(key) = key {
            self.memo.borrow_mut().candidates[top as usize].insert(key, retval.clone());
        }
        retval
    }

    /// Check if the statement can be used for the whole text, with `top`, or for a part of it.
    /// The message itself could have come from anywhere, so all categories are used, unless
    /// only logging calls are wanted.  A value of a placeholder is a message that was made
    /// somewhere else, so only the errors and formatted messages are used for those.
    fn usable(&self, stmt: &Statement, top: bool) -> bool {
        if top {
            !self.top_log_only || stmt.category == MessageCategory::Log
        } else {
            matches!(
                stmt.category,
                MessageCategory::Error | MessageCategory::Format
            )
        }
    }

    /// [`Self::candidates`], without the memo.
    fn find_candidates(&self, text: &str, top: bool) -> Vec<StatementRef<'s>> {
        let mut retval: Vec<StatementRef<'s>> = self
            .statements
            .iter()
            .copied()
            .filter(|stmt| self.usable(stmt, top))
            .filter(|stmt| self.pattern(stmt).is_match(text))
            .collect();
        retval.sort_by(|lhs, rhs| compare_candidates(lhs, rhs, None, None));
        // `first_match()` uses the exact pattern, which a statement that only matches with the
        // whitespace relaxed would fail, so the order is left as is.
        if !self.relaxed {
            let best = first_match(
                retval.iter().copied().enumerate(),
                text,
                None,
                |candidate: &(usize, StatementRef<'s>)| candidate.1.stmt,
            );
            if let Some((index, _)) = best {
                let best = retval.remove(index);
                retval.insert(0, best);
            }
        }
        // A statement whose values do not look like the format string says, like text for the
        // `%d` in `"%d messages"`, only matched because a placeholder matches anything, so it is
        // left out, unless it is all there is.
        let (fitting, misfits): (Vec<_>, Vec<_>) =
            retval.into_iter().partition(|stmt| self.fits(stmt, text));
        if fitting.is_empty() {
            misfits
        } else {
            fitting
        }
    }

    /// Check if the values of the placeholders in `text` look like the statement's kinds.
    fn fits(&self, stmt: &Statement, text: &str) -> bool {
        stmt.values_fit_kinds(self.pattern(stmt), text)
    }

    /// Find the sources of `text` and the amount of literal text they explain.
    fn resolve(&self, text: &str, depth: usize, top: bool) -> (usize, Vec<MessageSource<'s>>) {
        if depth > MAX_DEPTH || text.len() < MIN_VALUE_LEN {
            return (0, vec![]);
        }
        let key = self
            .memo
            .borrow()
            .key(text)
            .map(|(offset, len)| (offset, len, depth));
        if let Some(found) =
            key.and_then(|key| self.memo.borrow().resolved[top as usize].get(&key).cloned())
        {
            return found;
        }
        let retval = self.find_resolution(text, depth, top);
        if let Some(key) = key {
            self.memo.borrow_mut().resolved[top as usize].insert(key, retval.clone());
        }
        retval
    }

    /// [`Self::resolve`], without the memo.
    fn find_resolution(
        &self,
        text: &str,
        depth: usize,
        top: bool,
    ) -> (usize, Vec<MessageSource<'s>>) {
        let mut best = match self.source(text, depth, top) {
            Some((score, source)) => (score, vec![source]),
            None => (0, vec![]),
        };
        // A chain of messages, like `"outer: inner: leaf"`, where each part was made separately.
        // A statement that matches all of the text wins a tie, like `"Unable to start: {:#}"`
        // with the whole chain in its placeholder.
        for (pos, sep) in text.match_indices(": ").take(MAX_SPLITS) {
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
        // A statement that only matched because a placeholder matches anything does not explain
        // any of the text, so a reading that fits wins, but it is still better than nothing.
        let mut score = if self.fits(first, text) {
            first.quality
        } else {
            0
        };
        let mut causes = vec![];
        if let Some(captures) = self.pattern(first).captures(text) {
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

    /// Explain `text` as pieces that were put together, like SQL that is appended to a builder
    /// in a few statements, some of which only run sometimes.  The statements whose literal
    /// text is in `text` are each a piece, and the pieces that explain the most of the text
    /// without overlapping are used.  The function with the pieces that explain the most of
    /// the text is preferred, since that is usually where the text was built.  The pieces from
    /// other functions, like a helper that adds a clause, need more literal text, since a short
    /// piece of text could be from anywhere.  The text between the pieces is from somewhere
    /// else, like the values that were appended.  Returns the amount of literal text that is
    /// explained and the sources in the order of the text, or None if there are not at least
    /// two pieces.  The whitespace in `text` should already be collapsed.
    fn assemble(&self, text: &str) -> Option<(usize, Vec<MessageSource<'s>>)> {
        let mut pieces = vec![];
        for stmt in &self.statements {
            let literals = literal_pieces(stmt);
            let weight: usize = literals
                .iter()
                .map(|(literal, _, _)| literal.chars().filter(|c| !c.is_whitespace()).count())
                .sum();
            if weight < MIN_PIECE_LEN
                || !literals
                    .iter()
                    .all(|(literal, _, _)| text.contains(literal.as_str()))
            {
                continue;
            }
            for (start, end) in piece_places(text, &literals) {
                pieces.push(Piece {
                    start,
                    end,
                    weight,
                    stmt: *stmt,
                });
            }
        }
        // The function with the pieces that explain the most of the text.
        let function_of = |stmt: &StatementRef<'s>| -> (&'s str, &'s str) {
            (stmt.source_path(), stmt.stmt.qualified_name.as_str())
        };
        let mut by_function: HashMap<_, Vec<&Piece>> = HashMap::new();
        for piece in &pieces {
            by_function
                .entry(function_of(&piece.stmt))
                .or_default()
                .push(piece);
        }
        let home = by_function
            .iter()
            .map(|(function, pieces)| (best_cover(pieces, |_| false).0, *function))
            .max()?
            .1;
        let usable: Vec<&Piece> = pieces
            .iter()
            .filter(|piece| function_of(&piece.stmt) == home || piece.weight >= MIN_FRAGMENT_LEN)
            .collect();
        let (score, chosen) = best_cover(&usable, |piece| function_of(&piece.stmt) == home);
        if chosen.len() < 2 {
            return None;
        }
        let mut sources = vec![];
        let mut last_end = 0;
        for piece in chosen {
            let gap = text[last_end..piece.start].trim();
            if !gap.is_empty() {
                sources.push(MessageSource::unknown(gap));
            }
            // The other statements that could have produced the same piece, with the ones in
            // the preferred function first.
            let mut candidates: Vec<StatementRef<'s>> = usable
                .iter()
                .filter(|other| other.start == piece.start && other.end == piece.end)
                .map(|other| other.stmt)
                .collect();
            candidates.sort_by(|lhs, rhs| {
                (function_of(rhs) == home)
                    .cmp(&(function_of(lhs) == home))
                    .then_with(|| rhs.quality.cmp(&lhs.quality))
                    .then_with(|| compare_candidates(lhs, rhs, None, None))
            });
            candidates.dedup_by(|lhs, rhs| std::ptr::eq(lhs.stmt, rhs.stmt));
            sources.push(MessageSource {
                text: text[piece.start..piece.end].to_string(),
                candidates,
                causes: vec![],
                partial: false,
            });
            last_end = piece.end;
        }
        let gap = text[last_end..].trim();
        if !gap.is_empty() {
            sources.push(MessageSource::unknown(gap));
        }
        Some((score, sources))
    }

    /// The statements that share the most literal text with `text`, which is not all of a
    /// message, like a fragment of one or one with extra text around it.  The whitespace in
    /// `text` should already be collapsed.  The amount of literal text shared with the best one
    /// is returned with it.  A statement that only shares text that a better one shares too,
    /// like `"a named search must have a name"` for the `" is already a named search"` at the
    /// end of a message, explains nothing more, so it is left out.  The ones that share the
    /// same amount are kept, since any of them could be the source.
    fn fragment(&self, text: &str) -> Option<(usize, MessageSource<'s>)> {
        let mut scored: Vec<(SharedLiteral, StatementRef<'s>)> = self
            .statements
            .iter()
            .map(|stmt| (shared_literal(stmt, text), *stmt))
            .filter(|(shared, _)| shared.len >= MIN_FRAGMENT_LEN)
            .collect();
        scored.sort_by(|(lhs_shared, lhs), (rhs_shared, rhs)| {
            rhs_shared
                .len
                .cmp(&lhs_shared.len)
                .then_with(|| compare_candidates(lhs, rhs, None, None))
        });
        let score = scored.first()?.0.len;
        // The parts of the text shared by the statements with more shared text than the
        // current one, and by the ones with the same amount, which are added once the amount
        // goes down.
        let mut covered = vec![false; text.len()];
        let mut pending: Vec<std::ops::Range<usize>> = vec![];
        let mut pending_len = score;
        let mut candidates = vec![];
        for (shared, stmt) in scored {
            if shared.len < pending_len {
                for range in pending.drain(..) {
                    covered[range].fill(true);
                }
                pending_len = shared.len;
            }
            if shared
                .ranges
                .iter()
                .all(|range| covered[range.clone()].iter().all(|covered| *covered))
            {
                continue;
            }
            pending.extend(shared.ranges);
            candidates.push(stmt);
            if candidates.len() == MAX_FRAGMENT_CANDIDATES {
                break;
            }
        }
        Some((
            score,
            MessageSource {
                text: text.to_string(),
                candidates,
                causes: vec![],
                partial: true,
            },
        ))
    }
}

/// A place in a text that a statement could have produced, for [`Finder::assemble`].
struct Piece<'s> {
    start: usize,
    end: usize,
    /// The amount of literal text in the statement, not counting whitespace.
    weight: usize,
    stmt: StatementRef<'s>,
}

/// The literal text of a statement, between its placeholders, with the whitespace collapsed.
/// Each one is paired with whether there was whitespace at its start and end, which has to be
/// in the text too, so `" AND "` is not found in `"BRAND"`.
fn literal_pieces(stmt: &Statement) -> Vec<(String, bool, bool)> {
    stmt.segments
        .iter()
        .flat_map(|segment| regex_literal_pieces(segment))
        .filter_map(|piece| {
            let collapsed = collapse_whitespace(&piece);
            (!collapsed.is_empty()).then(|| {
                (
                    collapsed,
                    piece.starts_with(char::is_whitespace),
                    piece.ends_with(char::is_whitespace),
                )
            })
        })
        .collect()
}

/// The places in `text` where the literal pieces of a statement are, in order, as the start of
/// the first and the end of the last.
fn piece_places(text: &str, literals: &[(String, bool, bool)]) -> Vec<(usize, usize)> {
    // The position of `literal` at or after `from`, with the whitespace around it.
    let find = |from: usize, (literal, lead, trail): &(String, bool, bool)| {
        text[from..]
            .match_indices(literal.as_str())
            .map(|(pos, _)| from + pos)
            .find(|&pos| {
                let end = pos + literal.len();
                (!lead || pos == 0 || text[..pos].ends_with(' '))
                    && (!trail || end == text.len() || text[end..].starts_with(' '))
            })
            .map(|pos| (pos, pos + literal.len()))
    };
    let mut retval = vec![];
    let mut from = 0;
    while retval.len() < MAX_PIECE_PLACES {
        let Some((start, mut end)) = find(from, &literals[0]) else {
            break;
        };
        let mut complete = true;
        for literal in &literals[1..] {
            match find(end, literal) {
                Some((_, next_end)) => end = next_end,
                None => {
                    complete = false;
                    break;
                }
            }
        }
        if !complete {
            break;
        }
        retval.push((start, end));
        // The next place could start inside this one, like for `"a a"` in `"a a a"`.
        from = start + text[start..].chars().next().map_or(1, char::len_utf8);
    }
    retval
}

/// The pieces that explain the most literal text without overlapping, in order, along with the
/// amount of literal text and how much of that is from pieces that `preferred` accepts, which
/// breaks ties.
fn best_cover<'p, 's>(
    pieces: &[&'p Piece<'s>],
    preferred: impl Fn(&Piece<'s>) -> bool,
) -> (usize, Vec<&'p Piece<'s>>) {
    let mut sorted: Vec<&Piece> = pieces.to_vec();
    sorted.sort_by_key(|piece| (piece.end, piece.start));
    // best[i] is the best cover of the first `i` pieces, as (weight, preferred weight).
    let mut best: Vec<(usize, usize)> = vec![(0, 0); sorted.len() + 1];
    let mut taken = vec![false; sorted.len()];
    for (index, piece) in sorted.iter().enumerate() {
        // The pieces before this one that end before it starts.
        let before = sorted[..index].partition_point(|prev| prev.end <= piece.start);
        let bonus = if preferred(piece) { piece.weight } else { 0 };
        let with = (best[before].0 + piece.weight, best[before].1 + bonus);
        if with > best[index] {
            best[index + 1] = with;
            taken[index] = true;
        } else {
            best[index + 1] = best[index];
        }
    }
    let mut chosen = vec![];
    let mut index = sorted.len();
    while index > 0 {
        if taken[index - 1] {
            let piece = sorted[index - 1];
            chosen.push(piece);
            index = sorted[..index - 1].partition_point(|prev| prev.end <= piece.start);
        } else {
            index -= 1;
        }
    }
    chosen.reverse();
    (best[sorted.len()].0, chosen)
}

/// Replace each run of whitespace with a single space and trim the ends.
pub(crate) fn collapse_whitespace(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// The literal text that a statement shares with `text`, and where it is in `text`.
/// The literal parts of the statement that are in the text count, like `"Unable to read "` in
/// `"Unable to read file"`.  When the text is only part of the message, the text can also be
/// in a literal part, or overlap the start or end of one, like `"read file: denied"` for
/// `"Unable to read file: {}"`.
fn shared_literal(stmt: &Statement, text: &str) -> SharedLiteral {
    let non_ws = |s: &str| s.chars().filter(|c| !c.is_whitespace()).count();
    let mut contained = 0;
    let mut contained_ranges = vec![];
    let mut overlap = 0;
    let mut overlap_range = 0..0;
    // The segments are regexes, so they are turned back into the literal text.
    for segment in stmt
        .segments
        .iter()
        .flat_map(|segment| regex_literal_pieces(segment))
    {
        let segment = collapse_whitespace(&segment);
        if segment.is_empty() {
            continue;
        }
        if let Some(pos) = text.find(&segment) {
            contained += non_ws(&segment);
            contained_ranges.push(pos..pos + segment.len());
            continue;
        }
        let range = if segment.contains(text) {
            0..text.len()
        } else {
            edge_overlap(&segment, text)
        };
        let len = non_ws(&text[range.clone()]);
        if len > overlap {
            overlap = len;
            overlap_range = range;
        }
    }
    if contained >= overlap {
        SharedLiteral {
            len: contained,
            ranges: contained_ranges,
        }
    } else {
        SharedLiteral {
            len: overlap,
            ranges: vec![overlap_range],
        }
    }
}

/// The literal text that a statement shares with some text, from [`shared_literal`].
struct SharedLiteral {
    /// The amount of shared text, not counting whitespace.
    len: usize,
    /// Where the shared text is in the text.
    ranges: Vec<std::ops::Range<usize>>,
}

/// Where in `text` the longest piece is that is at the end of `segment` and the start of
/// `text`, or the start of `segment` and the end of `text`.
fn edge_overlap(segment: &str, text: &str) -> std::ops::Range<usize> {
    let mut best = 0..0;
    for (pos, _) in text.char_indices().skip(1) {
        let (head, tail) = text.split_at(pos);
        if head.len() > best.len() && segment.ends_with(head) {
            best = 0..pos;
        }
        if tail.len() > best.len() && segment.starts_with(tail) {
            best = pos..text.len();
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
