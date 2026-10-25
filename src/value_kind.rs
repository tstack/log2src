//! Disambiguation of the values substituted into a log message.
//!
//! A log message matcher is built by replacing each placeholder with `(.+)`, which is fine for
//! deciding whether a line came from a given statement.  However, when placeholders are only
//! separated by whitespace (or nothing), the greedy captures give everything to the first
//! placeholder.  This module re-splits the matched line using two sources of information:
//!
//! * The kind of value expected for each placeholder, derived from the format spec (e.g. `%d`,
//!   `{:x}`) or from the syntax of the argument expression (e.g. `list.size()`, `a == b`).
//! * Structured values, like `[a, b]` or `"a b"`, need to have balanced brackets/quotes.

use crate::SourceLanguage;
use regex::Regex;
use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::ops::Range;
use std::sync::LazyLock;

/// The kind of value that is expected to be substituted for a placeholder.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum ValueKind {
    Any,
    Integer,
    Hex,
    Octal,
    Binary,
    Float,
    HexFloat,
    Char,
    Bool,
    Pointer,
}

/// The capture group used in a message matcher for a placeholder whose value can be anything.
pub const ANY_CAPTURE: &str = "(.+)";

/// Regexes that match a whole value of each kind, indexed by `ValueKind::index()`.
static VALUE_REGEXES: LazyLock<Vec<Regex>> = LazyLock::new(|| {
    ValueKind::ALL
        .iter()
        .map(|kind| Regex::new(&format!("(?s)^{}$", kind.capture_regex())).unwrap())
        .collect()
});

impl ValueKind {
    const ALL: [ValueKind; 10] = [
        ValueKind::Any,
        ValueKind::Integer,
        ValueKind::Hex,
        ValueKind::Octal,
        ValueKind::Binary,
        ValueKind::Float,
        ValueKind::HexFloat,
        ValueKind::Char,
        ValueKind::Bool,
        ValueKind::Pointer,
    ];

    fn index(&self) -> usize {
        *self as usize
    }

    /// The capture group to use in a message matcher for a placeholder of this kind.  Padding
    /// is matched outside the group, so it is not included in the value.
    pub fn capture_regex(&self) -> &'static str {
        match self {
            ValueKind::Any => ANY_CAPTURE,
            ValueKind::Integer => r"\s*([-+]?\d+)\s*",
            ValueKind::Hex => r"\s*([-+]?(?:0[xX])?[0-9a-fA-F]+)\s*",
            ValueKind::Octal => r"\s*([-+]?(?:0[oO])?[0-7]+)\s*",
            ValueKind::Binary => r"\s*([-+]?(?:0[bB])?[01]+)\s*",
            ValueKind::Float => {
                r"\s*([-+]?(?:(?:\d+\.?\d*|\.\d+)(?:[eE][-+]?\d+)?|(?i:inf(?:inity)?|nan)))\s*"
            }
            // printf() includes the "0x" prefix, but std::format() and fmt do not.
            ValueKind::HexFloat => {
                r"\s*([-+]?(?:(?:0[xX])?[0-9a-fA-F]+(?:\.[0-9a-fA-F]*)?[pP][-+]?\d+|(?i:inf(?:inity)?|nan)))\s*"
            }
            ValueKind::Char => r"\s*(.)\s*",
            ValueKind::Bool => r"\s*((?i:true|false))\s*",
            // Most C libraries print "0x" and lowercase hex digits, but MSVC prints zero-padded
            // uppercase digits without the prefix, and glibc prints "(nil)" for null.
            ValueKind::Pointer => r"\s*((?:0[xX])?[0-9a-fA-F]+|\((?:nil|null)\))\s*",
        }
    }

    /// Derive the kind from the text of a placeholder in a format string, like `%5d` or `{:#x}`.
    pub fn from_placeholder(language: SourceLanguage, placeholder: &str) -> ValueKind {
        if let Some(spec) = placeholder.strip_prefix('%') {
            return match spec.chars().last() {
                Some('d' | 'i' | 'u') => ValueKind::Integer,
                Some('x' | 'X') => ValueKind::Hex,
                Some('o') => ValueKind::Octal,
                Some('e' | 'E' | 'f' | 'F' | 'g' | 'G') => ValueKind::Float,
                // In Python, `%a` is the ascii() of any value.
                Some('a' | 'A') if language != SourceLanguage::Python => ValueKind::HexFloat,
                Some('c') => ValueKind::Char,
                Some('p') => ValueKind::Pointer,
                _ => ValueKind::Any,
            };
        }
        if matches!(language, SourceLanguage::Java | SourceLanguage::Kotlin) {
            // SLF4J/Log4j placeholders do not have a format spec.
            return ValueKind::Any;
        }
        placeholder
            .strip_prefix('{')
            .and_then(|s| s.strip_suffix('}'))
            .and_then(|s| s.split_once(':'))
            .map_or(ValueKind::Any, |(_, spec)| Self::from_format_spec(spec))
    }

    /// Derive the kind from a `std::fmt`/`fmt::format`/Python format spec, which is the part
    /// after the colon in a `{...}` placeholder.
    pub fn from_format_spec(spec: &str) -> ValueKind {
        let mut chars = spec.chars();
        let rest = match (chars.next(), chars.next()) {
            // Python's `=` alignment puts the padding between the sign and the digits.
            (_, Some('=')) | (Some('='), _) => return ValueKind::Any,
            (Some(fill), Some('<' | '>' | '^')) => {
                if !fill.is_whitespace() {
                    // A fill character would be mixed in with the value.
                    return ValueKind::Any;
                }
                chars.as_str()
            }
            (Some('<' | '>' | '^'), _) => &spec[1..],
            _ => spec,
        };
        if rest.contains([',', '_', 'L']) {
            // Digit grouping/locale-specific formatting.
            return ValueKind::Any;
        }
        match rest.chars().last() {
            Some('d') => ValueKind::Integer,
            Some('x' | 'X') => ValueKind::Hex,
            Some('o') => ValueKind::Octal,
            Some('b' | 'B') => ValueKind::Binary,
            Some('e' | 'E' | 'f' | 'F' | 'g' | 'G') => ValueKind::Float,
            Some('a' | 'A') => ValueKind::HexFloat,
            Some('c') => ValueKind::Char,
            Some('p') => ValueKind::Pointer,
            _ => ValueKind::Any,
        }
    }

    /// The printf-style placeholder that is equivalent to this kind.
    pub fn printf_placeholder(&self) -> &'static str {
        match self {
            ValueKind::Integer => "%d",
            ValueKind::Hex => "%x",
            ValueKind::Octal => "%o",
            ValueKind::Float => "%f",
            ValueKind::Char => "%c",
            ValueKind::Pointer => "%p",
            ValueKind::Any | ValueKind::Binary | ValueKind::HexFloat | ValueKind::Bool => "%s",
        }
    }

    /// Guess the kind of value from the syntax of the argument expression.  Since we only have
    /// a syntax tree and no type information, this is limited to things like literals, casts,
    /// and calls/operators whose result type is obvious.
    pub fn from_expression(language: SourceLanguage, expr: &str) -> ValueKind {
        let expr = expr.trim();
        let top = top_level(expr);
        if top.contains('?')
            || top.starts_with('|')
            || top.starts_with("move ")
            || top.starts_with("if ")
            || top.starts_with("match ")
            || top.starts_with("lambda")
            || top.contains(" if ")
            || (matches!(language, SourceLanguage::Java | SourceLanguage::Kotlin)
                && top.contains("->"))
        {
            // Ternaries, closures, and conditional expressions.
            return ValueKind::Any;
        }

        if LITERAL_BOOL_REGEX.is_match(expr) {
            return ValueKind::Bool;
        }
        if LITERAL_INT_REGEX.is_match(expr) {
            return ValueKind::Integer;
        }
        if LITERAL_FLOAT_REGEX.is_match(expr) {
            return ValueKind::Float;
        }

        if language == SourceLanguage::Python && (top.contains(" and ") || top.contains(" or ")) {
            // These evaluate to one of the operands, not a bool.
            return ValueKind::Any;
        }
        let is_comparison = ["==", "!=", "<=", ">=", "&&", "||", " < ", " > "]
            .iter()
            .any(|op| top.contains(op) && !top.contains("<=>"));
        let is_negation = (top.starts_with('!') && !top.starts_with("!="))
            // In Rust, `!` is also bitwise-not for integers.
            && language != SourceLanguage::Rust;
        let is_python_test = language == SourceLanguage::Python
            && (top.starts_with("not ")
                || top.contains(" in ")
                || top.contains(" is ")
                || top.starts_with("isinstance("));
        let is_java_test = language == SourceLanguage::Java && top.contains(" instanceof ");
        let is_kotlin_test = language == SourceLanguage::Kotlin
            && (top.contains(" in ") || top.contains(" !in ") || top.contains(" is "));
        if is_comparison || is_negation || is_python_test || is_java_test || is_kotlin_test {
            return ValueKind::Bool;
        }

        if matches!(language, SourceLanguage::Rust | SourceLanguage::Kotlin) {
            // `as` binds tighter than the arithmetic operators and both sides of those need to
            // be the same type, so a trailing cast determines the type of the whole expression.
            if let Some(caps) = AS_CAST_REGEX.captures(&top) {
                return Self::from_type_name(&caps[1]);
            }
        }

        if let Some(caps) = C_CAST_REGEX.captures(expr) {
            let kind = Self::from_type_name(&caps[1]);
            if kind != ValueKind::Any {
                return if has_binary_op(&top_level(&caps[2])) {
                    ValueKind::Any
                } else {
                    kind
                };
            }
        }
        if let Some(caps) = STATIC_CAST_REGEX.captures(&top) {
            return Self::from_type_name(&caps[1]);
        }
        if has_binary_op(&top) {
            return ValueKind::Any;
        }
        if let Some(caps) = CONVERSION_CALL_REGEX.captures(&top) {
            return Self::from_type_name(&caps[1]);
        }
        if let Some(caps) = METHOD_CALL_REGEX.captures(&top) {
            let method = &caps[1];
            if INTEGER_METHODS.contains(&method) {
                return ValueKind::Integer;
            }
            if FLOAT_METHODS.contains(&method) {
                return ValueKind::Float;
            }
            if BOOL_METHODS.contains(&method) || BOOL_METHOD_REGEX.is_match(method) {
                return ValueKind::Bool;
            }
        }
        let is_size_property = match language {
            SourceLanguage::Java => top.ends_with(".length"),
            SourceLanguage::Kotlin => top.ends_with(".size") || top.ends_with(".length"),
            _ => false,
        };
        if is_size_property {
            return ValueKind::Integer;
        }

        ValueKind::Any
    }

    fn from_type_name(name: &str) -> ValueKind {
        let name = name.trim();
        if INTEGER_TYPE_REGEX.is_match(name) {
            ValueKind::Integer
        } else if matches!(
            name,
            "float" | "double" | "Float" | "Double" | "f32" | "f64"
        ) {
            ValueKind::Float
        } else if matches!(name, "bool" | "boolean" | "Boolean") {
            ValueKind::Bool
        } else if matches!(name, "char" | "Character" | "Char") {
            ValueKind::Char
        } else {
            ValueKind::Any
        }
    }

    /// The candidate end offsets for a value of this kind starting at the beginning of `text`,
    /// in ascending order.
    fn candidate_ends(&self, text: &str) -> Vec<usize> {
        match self {
            ValueKind::Any => balanced_ends(text),
            ValueKind::Char => text
                .chars()
                .next()
                .map(|c| vec![c.len_utf8()])
                .unwrap_or_default(),
            _ => {
                // None of these values contain whitespace except for padding, so the value
                // cannot extend past the second run of whitespace.
                let limit = text
                    .char_indices()
                    .skip_while(|(_, c)| c.is_whitespace())
                    .skip_while(|(_, c)| !c.is_whitespace())
                    .find(|(_, c)| !c.is_whitespace())
                    .map_or(text.len(), |(index, _)| index);
                (1..=limit).filter(|&i| text.is_char_boundary(i)).collect()
            }
        }
    }

    /// Check if `text` is a valid value of this kind and return the range of the value without
    /// any padding.
    fn value_range(&self, text: &str) -> Option<Range<usize>> {
        if *self == ValueKind::Any {
            return Some(0..text.len());
        }
        VALUE_REGEXES[self.index()]
            .captures(text)
            .map(|caps| caps.get(1).unwrap().range())
    }
}

static LITERAL_BOOL_REGEX: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"^(?:true|false|True|False)$").unwrap());
static LITERAL_INT_REGEX: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r"^-?(?:0[xX][0-9a-fA-F_]+|0[bB][01_]+|0[oO][0-7_]+|\d[\d_]*)(?:[uUlL]{1,3}|[iu](?:8|16|32|64|128|size))?$",
    )
    .unwrap()
});
static LITERAL_FLOAT_REGEX: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"^-?(?:\d[\d_]*\.\d*(?:[eE][-+]?\d+)?|\d+[eE][-+]?\d+)(?:[fFdD]|f32|f64)?$")
        .unwrap()
});
static INTEGER_TYPE_REGEX: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r"^(?:(?:unsigned|signed)(?:\s+(?:char|short|int|long|long\s+long))?|(?:long\s+)?long(?:\s+int)?|short|int|byte|Int|Integer|Long|Short|Byte|(?:std::)?s?size_t|(?:std::)?u?int(?:8|16|32|64)_t|[iu](?:8|16|32|64|128|size)|len)$",
    )
    .unwrap()
});
static AS_CAST_REGEX: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"\sas\s+([A-Za-z0-9]+)$").unwrap());
static C_CAST_REGEX: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"(?s)^\(\s*([A-Za-z_][\w:]*(?:\s+[A-Za-z_]\w*)*)\s*\)\s*(\S.*)$").unwrap()
});
static STATIC_CAST_REGEX: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"^static_cast<\s*([^<>]+?)\s*>\(\)$").unwrap());
static CONVERSION_CALL_REGEX: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"^(int|long|float|double|bool|len|(?:std::)?size_t)\s*\(\)$").unwrap()
});
static METHOD_CALL_REGEX: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"(?:\.|->)([A-Za-z_]\w*)\(\)$").unwrap());
static BOOL_METHOD_REGEX: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"^(?:is|has)(?:[A-Z_]\w*)?$").unwrap());

const INTEGER_METHODS: &[&str] = &[
    "size",
    "length",
    "len",
    "count",
    "ordinal",
    "hashCode",
    "intValue",
    "longValue",
    "toInt",
    "toLong",
];
const FLOAT_METHODS: &[&str] = &["doubleValue", "floatValue", "toDouble", "toFloat"];
const BOOL_METHODS: &[&str] = &[
    "empty",
    "exists",
    "contains",
    "containsKey",
    "containsValue",
    "equals",
    "equalsIgnoreCase",
    "startsWith",
    "endsWith",
    "starts_with",
    "ends_with",
    "startswith",
    "endswith",
];

/// Reduce an expression to its top-level syntax by dropping the contents of any brackets and
/// string/char literals.  For example, `foo(a == b).len()` becomes `foo().len()`.
fn top_level(expr: &str) -> String {
    let mut retval = String::with_capacity(expr.len());
    let mut depth = 0usize;
    let mut quote: Option<char> = None;
    let mut escaped = false;
    let mut prev: Option<char> = None;
    for c in expr.chars() {
        if let Some(q) = quote {
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == q {
                quote = None;
                if depth == 0 {
                    retval.push(c);
                }
            }
        } else {
            match c {
                '(' | '[' | '{' => {
                    if depth == 0 {
                        retval.push(c);
                    }
                    depth += 1;
                }
                ')' | ']' | '}' => {
                    depth = depth.saturating_sub(1);
                    if depth == 0 {
                        retval.push(c);
                    }
                }
                '"' | '\'' if prev.is_none_or(|p| !p.is_alphanumeric()) => {
                    quote = Some(c);
                    if depth == 0 {
                        retval.push(c);
                    }
                }
                _ if depth == 0 => retval.push(c),
                _ => {}
            }
        }
        prev = Some(c);
    }
    retval
}

/// Check if a top-level expression contains any binary operators, ignoring member access.
fn has_binary_op(top: &str) -> bool {
    top.replace("->", ".").replace("::", ".").contains([
        '+', '-', '*', '/', '%', '&', '|', '^', '<', '>', '=', '?', ':',
    ]) || top.contains(" and ")
        || top.contains(" or ")
}

/// Call `on_balanced` with each offset where a prefix of `text` has balanced brackets and
/// quotes.  Stops early if no longer prefix can be balanced.
fn scan_balanced(text: &str, mut on_balanced: impl FnMut(usize)) {
    let mut stack = Vec::new();
    let mut quote: Option<char> = None;
    let mut escaped = false;
    let mut prev: Option<char> = None;
    for (index, c) in text.char_indices() {
        if let Some(q) = quote {
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == q {
                quote = None;
            }
        } else {
            match c {
                '(' => stack.push(')'),
                '[' => stack.push(']'),
                '{' => stack.push('}'),
                ')' | ']' | '}' => {
                    if stack.pop() != Some(c) {
                        return;
                    }
                }
                // Only treat a quote as the start of a literal if it is not an apostrophe in
                // the middle of a word, like "don't".
                '"' | '\'' if prev.is_none_or(|p| !p.is_alphanumeric()) => quote = Some(c),
                _ => {}
            }
        }
        prev = Some(c);
        if quote.is_none() && stack.is_empty() {
            on_balanced(index + c.len_utf8());
        }
    }
}

/// Find the offsets where a prefix of `text` has balanced brackets and quotes.
fn balanced_ends(text: &str) -> Vec<usize> {
    let mut retval = Vec::new();
    scan_balanced(text, |end| retval.push(end));
    retval
}

fn is_balanced(text: &str) -> bool {
    let mut last = 0;
    scan_balanced(text, |end| last = end);
    last == text.len()
}

/// Check if ending a value at `end` is unlikely because the value would end with whitespace,
/// which is more likely to be padding, or because it would separate an identifier from a
/// following `{`, like the Rust Debug output `Foo { x: 1 }`.
fn is_weak_end(text: &str, end: usize) -> bool {
    let Some(last) = text[..end].chars().last() else {
        return false;
    };
    if last.is_whitespace() {
        return true;
    }
    let after = &text[end..];
    let fields = after.trim_start();
    after.len() != fields.len()
        && fields.starts_with('{')
        && (last.is_alphanumeric() || last == '_')
}

/// Compile anchored regexes for the literal segments of a message, as needed by
/// `split_values()`.
pub(crate) fn compile_segments(segments: &[String]) -> Option<Vec<Regex>> {
    let last = segments.len().checked_sub(1)?;
    segments
        .iter()
        .enumerate()
        .map(|(index, segment)| {
            let end = if index == last { "$" } else { "" };
            Regex::new(&format!("(?s)^(?:{segment}){end}")).ok()
        })
        .collect()
}

/// Check if the values found by the greedy captures of the message matcher are plausible for
/// the kinds of values expected.  If they are, `split_values()` would return the same values, so
/// the more expensive search can be skipped.
pub(crate) fn is_plausible(text: &str, values: &[Range<usize>], kinds: &[ValueKind]) -> bool {
    std::iter::zip(values, kinds).all(|(range, kind)| {
        let value = &text[range.clone()];
        let valid = match kind {
            ValueKind::Any => is_balanced(value),
            _ => kind.value_range(value) == Some(0..value.len()),
        };
        valid && !is_weak_end(&text[range.start..], value.len())
    })
}

/// The maximum number of candidate values to try before giving up on splitting a line.
const MAX_CANDIDATES: usize = 10_000;

/// Split `text` into the values for each placeholder.
///
/// `segments` are anchored regexes for the literal text before, between, and after the
/// placeholders, so there must be one more segment than there are kinds.  The search prefers
/// longer values for earlier placeholders, which is the same preference as the greedy captures
/// in the message matcher.  Returns `None` if there is no valid split.
pub(crate) fn split_values(
    text: &str,
    segments: &[Regex],
    kinds: &[ValueKind],
) -> Option<Vec<Range<usize>>> {
    if segments.len() != kinds.len() + 1 {
        return None;
    }
    let start = segments[0].find(text)?.end();
    let mut search = SplitSearch {
        text,
        segments,
        kinds,
        values: Vec::with_capacity(kinds.len()),
        failed: HashSet::new(),
        budget: MAX_CANDIDATES,
    };
    if search.search(0, start) {
        Some(search.values)
    } else {
        None
    }
}

struct SplitSearch<'a> {
    text: &'a str,
    segments: &'a [Regex],
    kinds: &'a [ValueKind],
    values: Vec<Range<usize>>,
    /// The (placeholder, offset) pairs that are known to not lead to a valid split.
    failed: HashSet<(usize, usize)>,
    budget: usize,
}

impl SplitSearch<'_> {
    fn search(&mut self, index: usize, pos: usize) -> bool {
        if index == self.kinds.len() {
            return true;
        }
        if self.failed.contains(&(index, pos)) {
            return false;
        }
        let kind = self.kinds[index];
        let rest = &self.text[pos..];
        // Try longer values first, but defer the ends that are less likely.
        let (strong, weak): (Vec<usize>, Vec<usize>) = kind
            .candidate_ends(rest)
            .into_iter()
            .rev()
            .partition(|&end| !is_weak_end(rest, end));
        for end in strong.into_iter().chain(weak) {
            if self.budget == 0 {
                return false;
            }
            self.budget -= 1;
            let Some(sep) = self.segments[index + 1].find(&rest[end..]) else {
                continue;
            };
            let Some(value) = kind.value_range(&rest[..end]) else {
                continue;
            };
            self.values.push(pos + value.start..pos + value.end);
            if self.search(index + 1, pos + end + sep.end()) {
                return true;
            }
            self.values.pop();
        }
        self.failed.insert((index, pos));
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kinds_of(language: SourceLanguage, exprs: &[&str]) -> Vec<ValueKind> {
        exprs
            .iter()
            .map(|expr| ValueKind::from_expression(language, expr))
            .collect()
    }

    #[test]
    fn test_from_placeholder() {
        use SourceLanguage::*;
        use ValueKind::*;
        let cases = [
            (Cpp, "%d", Integer),
            (Cpp, "%-5lld", Integer),
            (Cpp, "%zu", Integer),
            (Cpp, "%#x", Hex),
            (Cpp, "%o", Octal),
            (Cpp, "%.2f", Float),
            (Cpp, "%g", Float),
            (Cpp, "%c", Char),
            (Cpp, "%s", Any),
            (Cpp, "%a", HexFloat),
            (Cpp, "%.2A", HexFloat),
            (Cpp, "{:a}", HexFloat),
            (Cpp, "{:>20A}", HexFloat),
            (Python, "%a", Any),
            (Cpp, "%p", Pointer),
            (Cpp, "%-20p", Pointer),
            (Cpp, "{:p}", Pointer),
            (Rust, "{:p}", Pointer),
            (Cpp, "{:d}", Integer),
            (Cpp, "{0:>8.3f}", Float),
            (Cpp, "{:Ld}", Any),
            (Cpp, "{:*>5d}", Any),
            (Cpp, "{: >5d}", Integer),
            (Rust, "{}", Any),
            (Rust, "{:?}", Any),
            (Rust, "{:x?}", Any),
            (Rust, "{:#x}", Hex),
            (Rust, "{count:08b}", Binary),
            (Rust, "{:e}", Float),
            (Rust, "{:.2}", Any),
            (Rust, "{:>width$}", Any),
            (Python, "%d", Integer),
            (Python, "%s", Any),
            (Java, "{}", Any),
            (Kotlin, "{}", Any),
        ];
        for (language, placeholder, expected) in cases {
            assert_eq!(
                ValueKind::from_placeholder(language, placeholder),
                expected,
                "{placeholder}"
            );
        }
    }

    #[test]
    fn test_from_format_spec_python() {
        assert_eq!(ValueKind::from_format_spec(">5.2f"), ValueKind::Float);
        assert_eq!(ValueKind::from_format_spec(",d"), ValueKind::Any);
        assert_eq!(ValueKind::from_format_spec("_x"), ValueKind::Any);
        assert_eq!(ValueKind::from_format_spec(".1%"), ValueKind::Any);
        assert_eq!(ValueKind::from_format_spec("n"), ValueKind::Any);
        assert_eq!(ValueKind::from_format_spec("=5d"), ValueKind::Any);
        assert_eq!(ValueKind::from_format_spec(" =+8.2f"), ValueKind::Any);
        assert_eq!(ValueKind::from_format_spec(">5c"), ValueKind::Char);
    }

    #[test]
    fn test_from_expression() {
        use SourceLanguage::*;
        use ValueKind::*;
        let cases = [
            (Java, "items.size()", Integer),
            (Java, "name.length()", Integer),
            (Java, "args.length", Integer),
            (Java, "(int) value", Integer),
            (Java, "(double) total / count", Any),
            (Java, "(String) obj", Any),
            (Java, "map.isEmpty()", Bool),
            (Java, "map.containsKey(key)", Bool),
            (Java, "a == b", Bool),
            (Java, "!done", Bool),
            (Java, "obj instanceof Foo", Bool),
            (Java, "a == b ? x : y", Any),
            (Java, "\"prefix\" + items.size()", Any),
            (Java, "items.stream().filter(x -> x == 1).count()", Integer),
            (Java, "issue()", Any),
            (Java, "42", Integer),
            (Java, "100L", Integer),
            (Java, "1.5f", Float),
            (Java, "true", Bool),
            (Java, "name", Any),
            (Java, "getName()", Any),
            (Rust, "v.len()", Integer),
            (Rust, "v.is_empty()", Bool),
            (Rust, "opt.is_some()", Bool),
            (Rust, "a + b as u64", Integer),
            (Rust, "x as f64", Float),
            (Rust, "a == b as u32", Bool),
            (Rust, "!mask", Any),
            (Rust, "foo(a == b).len()", Integer),
            (Rust, "if a { 1 } else { 2 }", Any),
            (Rust, "42u32", Integer),
            (Cpp, "vec.size()", Integer),
            (Cpp, "ptr->size()", Integer),
            (Cpp, "vec.empty()", Bool),
            (Cpp, "static_cast<int>(x)", Integer),
            (Cpp, "(unsigned long) x", Integer),
            (Cpp, "a < b", Bool),
            (Cpp, "std::vector<int>()", Any),
            (Python, "len(items)", Integer),
            (Python, "int(value)", Integer),
            (Python, "float(value)", Float),
            (Python, "str(value)", Any),
            (Python, "key in items", Bool),
            (Python, "not done", Bool),
            (Python, "a == b and c", Any),
            (Python, "x if a == b else y", Any),
            (Python, "isinstance(x, int)", Bool),
            (Kotlin, "items.size", Integer),
            (Kotlin, "name.length", Integer),
            (Kotlin, "x as Int", Integer),
            (Kotlin, "s.toDouble()", Float),
            (Kotlin, "x in items", Bool),
            (Kotlin, "x is String", Bool),
            (Kotlin, "items?.size", Any),
            (Kotlin, "x ?: 0", Any),
        ];
        for (language, expr, expected) in cases {
            assert_eq!(
                ValueKind::from_expression(language, expr),
                expected,
                "{language:?} {expr}"
            );
        }
    }

    #[test]
    fn test_balanced_ends() {
        assert_eq!(balanced_ends("a [b, c] d"), vec![1, 2, 8, 9, 10]);
        assert_eq!(balanced_ends("a) b"), vec![1]);
        assert_eq!(balanced_ends("don't stop"), (1..=10).collect::<Vec<_>>());
        assert_eq!(balanced_ends("'a b' c"), vec![5, 6, 7]);
        assert_eq!(balanced_ends(r#""a \" b" c"#), vec![8, 9, 10]);
    }

    fn split(text: &str, segments: &[&str], kinds: &[ValueKind]) -> Option<Vec<String>> {
        let last = segments.len() - 1;
        let segments: Vec<Regex> = segments
            .iter()
            .enumerate()
            .map(|(index, seg)| {
                let end = if index == last { "$" } else { "" };
                Regex::new(&format!("(?s)^(?:{seg}){end}")).unwrap()
            })
            .collect();
        split_values(text, &segments, kinds).map(|ranges| {
            ranges
                .into_iter()
                .map(|range| text[range].to_string())
                .collect()
        })
    }

    #[test]
    fn test_split_brackets() {
        use ValueKind::*;
        assert_eq!(
            split(
                "foo bar: 1 2 [a, b]",
                &["foo bar: ", " ", " ", ""],
                &[Any, Any, Any]
            ),
            Some(vec!["1".into(), "2".into(), "[a, b]".into()])
        );
        assert_eq!(
            split(
                "foo bar: [k=v, z=1] null 42",
                &["foo bar: ", " ", " ", ""],
                &[Any, Any, Any]
            ),
            Some(vec!["[k=v, z=1]".into(), "null".into(), "42".into()])
        );
        assert_eq!(
            split(
                r#"got: "a b" Foo { x: 1 }"#,
                &["got: ", " ", ""],
                &[Any, Any]
            ),
            Some(vec![r#""a b""#.into(), "Foo { x: 1 }".into()])
        );
    }

    #[test]
    fn test_split_kinds() {
        use ValueKind::*;
        assert_eq!(
            split(
                "foo bar: hello world 2 3",
                &["foo bar: ", " ", " ", ""],
                &kinds_of(SourceLanguage::Java, &["a", "b.size()", "c"])
            ),
            Some(vec!["hello world".into(), "2".into(), "3".into()])
        );
        assert_eq!(
            split(
                "foo bar: 1 hello world 3",
                &["foo bar: ", " ", " ", ""],
                &[Integer, Any, Integer]
            ),
            Some(vec!["1".into(), "hello world".into(), "3".into()])
        );
        assert_eq!(
            split("adjacent: 42abc", &["adjacent: ", "", ""], &[Integer, Any]),
            Some(vec!["42".into(), "abc".into()])
        );
        assert_eq!(
            split("padded:    42|", &["padded: ", r"\|"], &[Integer]),
            Some(vec!["42".into()])
        );
        assert_eq!(
            split("flag: true yes", &["flag: ", " ", ""], &[Bool, Any]),
            Some(vec!["true".into(), "yes".into()])
        );
    }

    #[test]
    fn test_split_ambiguous_prefers_greedy() {
        use ValueKind::*;
        assert_eq!(
            split(
                "foo bar: 1 hello world 3",
                &["foo bar: ", " ", " ", ""],
                &[Any, Any, Any]
            ),
            Some(vec!["1 hello".into(), "world".into(), "3".into()])
        );
    }

    #[test]
    fn test_split_no_valid() {
        use ValueKind::*;
        assert_eq!(
            split("value: a) b", &["value: ", " ", ""], &[Any, Any]),
            None
        );
        assert_eq!(split("count: abc", &["count: ", ""], &[Integer]), None);
    }

    #[test]
    fn test_is_plausible() {
        use ValueKind::*;
        let text = "a [b, c] 42";
        assert!(is_plausible(
            text,
            &[0..1, 2..8, 9..11],
            &[Any, Any, Integer]
        ));
        // Unbalanced brackets.
        assert!(!is_plausible(
            text,
            &[0..4, 5..8, 9..11],
            &[Any, Any, Integer]
        ));
        // The value does not match the kind from the argument expression.
        assert!(!is_plausible(
            text,
            &[0..1, 2..8, 9..11],
            &[Integer, Any, Integer]
        ));
        // Trailing whitespace is more likely to be padding.
        assert!(!is_plausible("a  42", &[0..2, 3..5], &[Any, Integer]));
    }

    /// The default formatting of values in each language, which is what a placeholder without a
    /// format spec produces when the kind comes from the argument expression.
    #[test]
    fn test_value_range_default_formats() {
        use ValueKind::*;
        let cases = [
            // Java/Kotlin
            (Integer, "-2147483648"),
            (Float, "1.0E20"),
            (Float, "1.0E-7"),
            (Float, "Infinity"),
            (Float, "-Infinity"),
            (Float, "NaN"),
            (Bool, "true"),
            (Char, "a"),
            // Rust
            (Float, "100000000000000000000"),
            (Float, "0.0000001"),
            (Float, "inf"),
            (Float, "-inf"),
            // Python
            (Float, "1e+20"),
            (Float, "1e-07"),
            (Float, "nan"),
            (Bool, "False"),
            // C++ std::format/fmt
            (Float, "-0"),
            (Char, " "),
        ];
        for (kind, text) in cases {
            assert_eq!(
                kind.value_range(text),
                Some(0..text.len()),
                "{kind:?} {text:?}"
            );
        }
        for text in [
            "0x1.921f9f01b866ep+1",
            "-0X1.4P+1",
            "0x2.p+1",
            "0x0.0000000000001p-1022",
            "1.921f9f01b866ep+1",
            "1p-1074",
            "inf",
            "-NAN",
        ] {
            assert_eq!(
                HexFloat.value_range(text),
                Some(0..text.len()),
                "HexFloat {text:?}"
            );
        }
        for text in ["0x7ffe2628436c", "0x0", "(nil)", "000000000061FE14", "0"] {
            assert_eq!(
                Pointer.value_range(text),
                Some(0..text.len()),
                "Pointer {text:?}"
            );
        }
        // Padding is not part of the value.
        assert_eq!(Char.value_range("    a"), Some(4..5));
        assert_eq!(Char.value_range("a    "), Some(0..1));
        assert_eq!(Integer.value_range("  42"), Some(2..4));
    }
}
