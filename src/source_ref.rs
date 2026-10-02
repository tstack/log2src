use crate::{CodeSource, QueryResult, SourceLanguage};
use core::fmt;
use regex::{Captures, Regex};
use serde::{Deserialize, Serialize};
use std::str::Chars;

#[derive(Clone, Debug, Serialize, Deserialize, Eq, PartialEq)]
pub enum FormatArgument {
    Named(String),
    Positional(usize),
    Placeholder,
}

#[derive(Clone, Debug, Serialize)]
pub struct CallSite {
    pub name: String,
    #[serde(rename(serialize = "sourcePath"))]
    pub source_path: String,
    pub language: SourceLanguage,
    #[serde(rename(serialize = "lineNumber"))]
    pub line_no: usize,
}

// TODO: get rid of this clone?
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SourceRef {
    #[serde(rename(serialize = "sourcePath"))]
    pub source_path: String,
    pub language: SourceLanguage,
    #[serde(rename(serialize = "lineNumber"))]
    pub line_no: usize,
    #[serde(rename(serialize = "endLineNumber"))]
    pub end_line_no: usize,
    pub column: usize,
    pub name: String,
    pub text: String,
    pub quality: usize,
    #[serde(with = "serde_regex")]
    pub(crate) pattern: Regex,
    /// The string form of `pattern`, kept for lnav.
    #[serde(skip)]
    pub pattern_str: String,
    pub(crate) args: Vec<FormatArgument>,
    pub(crate) vars: Vec<String>,
}

struct MessageMatcher {
    matcher: Regex,
    quality: usize,
    args: Vec<FormatArgument>,
}

impl SourceRef {
    pub(crate) fn new(code: &CodeSource, result: QueryResult) -> Option<SourceRef> {
        let range = result.range;
        let source = code.buffer.as_str();
        let text = source[range.start_byte..range.end_byte].to_string();
        let line_no = range.start_point.row + 1;
        let end_line_no = range.end_point.row + 1;
        let col = range.start_point.column;
        let start = range.start_byte + 1;
        let mut end = range.end_byte - 1;
        if start == range.end_byte {
            end = range.end_byte;
        }
        let unquoted = if let Some(pat) = result.pattern {
            pat
        } else {
            source[start..end].to_string()
        };
        if let Some(MessageMatcher {
            matcher,
            mut args,
            quality,
        }) = build_matcher(result.raw, &unquoted, code.info.language)
        {
            let name = source[result.name_range].to_string();
            if !result.args.is_empty() {
                args = result.args;
            }
            Some(SourceRef {
                source_path: code.filename.clone(),
                language: code.info.language,
                line_no,
                end_line_no,
                column: col,
                name,
                text,
                quality,
                pattern_str: matcher.as_str().to_string(),
                pattern: matcher,
                args,
                vars: vec![],
            })
        } else {
            None
        }
    }

    pub fn captures<'a>(&self, line: &'a str) -> Option<Captures<'a>> {
        self.pattern.captures(line)
    }

    /// The regex used to match log messages to this statement.
    pub fn pattern(&self) -> &Regex {
        &self.pattern
    }
}

impl fmt::Display for SourceRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[Line: {}, Col: {}] source `{}` name `{}` vars={:?}",
            self.line_no, self.column, self.text, self.name, self.vars
        )
    }
}

impl PartialEq for SourceRef {
    fn eq(&self, other: &Self) -> bool {
        self.line_no == other.line_no
            && self.column == other.column
            && self.name == other.name
            && self.text == other.text
            && self.vars == other.vars
    }
}

fn build_matcher(raw: bool, text: &str, language: SourceLanguage) -> Option<MessageMatcher> {
    let mut args = Vec::new();
    let mut last_end = 0;
    let mut pattern = "(?s)^".to_string();
    let mut quality = 0;
    for cap in language.get_placeholder_regex().captures_iter(text) {
        let placeholder = cap.get(0).unwrap();
        if !raw && is_unicode_escape(&text[..placeholder.start()]) {
            // Something like Rust's "\u{1F600}" is an escape and not a placeholder.
            continue;
        }
        let subtext = literal_to_regex(raw, language, &text[last_end..placeholder.start()]);
        quality += subtext.chars().filter(|c| !c.is_whitespace()).count();
        pattern.push_str(subtext.as_str());
        last_end = placeholder.end();
        pattern.push_str("(.+)");
        args.push(language.captures_to_format_arg(&cap));
    }
    let subtext = literal_to_regex(raw, language, &text[last_end..]);
    quality += subtext.chars().filter(|c| !c.is_whitespace()).count();
    if quality == 0 {
        None
    } else {
        pattern.push_str(subtext.as_str());
        pattern.push('$');
        // A pattern that does not compile is not usable, so skip the log statement.
        Regex::new(pattern.as_str())
            .ok()
            .map(|matcher| MessageMatcher {
                matcher,
                quality,
                args,
            })
    }
}

/// Check if the text ends with a `\u` that is not itself escaped.
fn is_unicode_escape(prefix: &str) -> bool {
    match prefix.strip_suffix('u') {
        Some(rest) => (rest.len() - rest.trim_end_matches('\\').len()) % 2 == 1,
        None => false,
    }
}

/// Append a regex that matches the given character literally.
fn push_regex_literal(out: &mut String, c: char) {
    match c {
        '\n' => out.push_str("\\n"),
        '\r' => out.push_str("\\r"),
        '\t' => out.push_str("\\t"),
        '.' | '*' | '+' | '?' | '^' | '$' | '{' | '}' | '(' | ')' | '|' | '[' | ']' | '\\' => {
            out.push('\\');
            out.push(c);
        }
        c if c.is_control() => out.push_str(&format!("\\x{:02X}", c as u32)),
        c => out.push(c),
    }
}

/// Consume up to `max` hex digits and return their value, if there were any.
fn take_hex(chars: &mut Chars, max: usize) -> Option<u32> {
    let mut value: u32 = 0;
    let mut count = 0;
    while count < max {
        match chars.clone().next().and_then(|c| c.to_digit(16)) {
            Some(digit) => {
                value = value.saturating_mul(16).saturating_add(digit);
                chars.next();
                count += 1;
            }
            None => break,
        }
    }
    (count > 0).then_some(value)
}

/// Decode a `\uXXXX` escape, which Java and Python use for UTF-16 code units, so a surrogate
/// pair spread across two escapes needs to be combined into one character.
fn take_utf16_escape(chars: &mut Chars) -> Option<char> {
    // Java allows any number of 'u's in a unicode escape.
    while chars.clone().next() == Some('u') {
        chars.next();
    }
    let high = take_hex(chars, 4)?;
    if (0xD800..0xDC00).contains(&high) {
        let mut ahead = chars.clone();
        if ahead.next() == Some('\\') && ahead.next() == Some('u') {
            if let Some(low @ 0xDC00..0xE000) = take_hex(&mut ahead, 4) {
                *chars = ahead;
                return char::from_u32(0x10000 + ((high - 0xD800) << 10) + (low - 0xDC00));
            }
        }
    }
    char::from_u32(high)
}

/// Convert a segment of a string-literal from the source code into a regex that matches the
/// text the literal produces at runtime.  Escape sequences are decoded into the characters they
/// represent and then any characters that are special to regexes are escaped.
fn literal_to_regex(raw: bool, language: SourceLanguage, segment: &str) -> String {
    let mut result = String::with_capacity(segment.len() * 2);
    let mut chars = segment.chars();
    while let Some(c) = chars.next() {
        if raw || c != '\\' {
            push_regex_literal(&mut result, c);
            continue;
        }
        let Some(esc) = chars.next() else {
            push_regex_literal(&mut result, '\\');
            break;
        };
        let remaining = chars.as_str().len();
        let decoded = match esc {
            '\n' | '\r' => {
                // A line continuation, which does not produce any characters.
                if esc == '\r' && chars.clone().next() == Some('\n') {
                    chars.next();
                }
                if language == SourceLanguage::Rust {
                    // Rust also skips the whitespace at the start of the next line.
                    while chars.clone().next().is_some_and(char::is_whitespace) {
                        chars.next();
                    }
                }
                continue;
            }
            'n' => Some('\n'),
            'r' => Some('\r'),
            't' => Some('\t'),
            'a' if language != SourceLanguage::Rust => Some('\x07'),
            'b' if language != SourceLanguage::Rust => Some('\x08'),
            'e' if language == SourceLanguage::Cpp => Some('\x1B'),
            'f' if language != SourceLanguage::Rust => Some('\x0C'),
            'v' if matches!(language, SourceLanguage::Cpp | SourceLanguage::Python) => Some('\x0B'),
            's' if language == SourceLanguage::Java => Some(' '),
            '0' if language == SourceLanguage::Rust => Some('\0'),
            '0'..='7' => {
                let mut value = esc.to_digit(8).unwrap();
                for _ in 0..2 {
                    match chars.clone().next().and_then(|c| c.to_digit(8)) {
                        Some(digit) => {
                            value = value * 8 + digit;
                            chars.next();
                        }
                        None => break,
                    }
                }
                char::from_u32(value)
            }
            'x' if language != SourceLanguage::Java => {
                // C++ hex escapes consume as many digits as are present.
                let max = if language == SourceLanguage::Cpp {
                    8
                } else {
                    2
                };
                take_hex(&mut chars, max).and_then(char::from_u32)
            }
            'u' if language == SourceLanguage::Rust => {
                let mut ahead = chars.clone();
                if ahead.next() == Some('{') {
                    let value = take_hex(&mut ahead, 6);
                    if ahead.next() == Some('}') {
                        chars = ahead;
                    }
                    value.and_then(char::from_u32)
                } else {
                    None
                }
            }
            'u' => take_utf16_escape(&mut chars),
            'U' if matches!(language, SourceLanguage::Cpp | SourceLanguage::Python) => {
                take_hex(&mut chars, 8).and_then(char::from_u32)
            }
            'N' if language == SourceLanguage::Python && chars.clone().next() == Some('{') => {
                // The Python named-Unicode escape.  Ideally, we'd interpret the name, but that
                // seems like a lot of work.  So, we'll just match any character.
                for c in chars.by_ref() {
                    if c == '}' {
                        break;
                    }
                }
                result.push('.');
                continue;
            }
            // Python keeps the backslash for unrecognized escapes.
            _ if language == SourceLanguage::Python && !matches!(esc, '\\' | '\'' | '"') => {
                push_regex_literal(&mut result, '\\');
                Some(esc)
            }
            _ => Some(esc),
        };
        match decoded {
            Some(c) => push_regex_literal(&mut result, c),
            // The escape was well-formed, but its value is not a valid character, like a lone
            // surrogate.  We don't know what the runtime will produce, so match anything.
            None if chars.as_str().len() != remaining => result.push('.'),
            // Fall back to treating a malformed escape as literal text.
            None => push_regex_literal(&mut result, esc),
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_build_matcher_needs_escape() {
        let MessageMatcher {
            matcher,
            args: _args,
            ..
        } = build_matcher(false, "{}) {}, {} \\033", SourceLanguage::Cpp).unwrap();
        assert_eq!(
            Regex::new(r#"(?s)^(.+)\) (.+), (.+) \x1B$"#)
                .unwrap()
                .as_str(),
            matcher.as_str()
        );
    }

    #[test]
    fn test_build_matcher_named() {
        let MessageMatcher { matcher, .. } =
            build_matcher(false, "abc {main_path:?} def", SourceLanguage::Rust).unwrap();
        assert_eq!(
            Regex::new(r#"(?s)^abc (.+) def$"#).unwrap().as_str(),
            matcher.as_str()
        );
    }

    #[test]
    fn test_build_matcher_mix() {
        let MessageMatcher { matcher, args, .. } =
            build_matcher(false, "{}) {:?}, {foo.bar}", SourceLanguage::Rust).unwrap();
        assert_eq!(
            Regex::new(r#"(?s)^(.+)\) (.+), (.+)$"#).unwrap().as_str(),
            matcher.as_str()
        );
        assert_eq!(args[2], FormatArgument::Named("foo.bar".to_string()));
    }

    #[test]
    fn test_build_matcher_positional() {
        let MessageMatcher { matcher, args, .. } =
            build_matcher(false, "second={2}", SourceLanguage::Rust).unwrap();
        assert_eq!(
            Regex::new(r#"(?s)^second=(.+)$"#).unwrap().as_str(),
            matcher.as_str()
        );
        assert_eq!(args[0], FormatArgument::Positional(2));
    }

    #[test]
    fn test_build_matcher_cpp() {
        let MessageMatcher { matcher, args, .. } =
            build_matcher(false, "they are %d years old", SourceLanguage::Cpp).unwrap();
        assert_eq!(
            Regex::new(r#"(?s)^they are (.+) years old$"#)
                .unwrap()
                .as_str(),
            matcher.as_str()
        );
        assert_eq!(args[0], FormatArgument::Placeholder);
    }

    #[test]
    fn test_build_matcher_cpp_spdlog() {
        let MessageMatcher { matcher, args, .. } =
            build_matcher(false, "they are {0:d} years old", SourceLanguage::Cpp).unwrap();
        assert_eq!(
            Regex::new(r#"(?s)^they are (.+) years old$"#)
                .unwrap()
                .as_str(),
            matcher.as_str()
        );
        assert_eq!(args[0], FormatArgument::Positional(0));
    }

    #[test]
    fn test_build_matcher_none() {
        let build_res = build_matcher(false, "%s", SourceLanguage::Cpp);
        assert!(build_res.is_none());
    }

    #[test]
    fn test_build_matcher_multiline() {
        let MessageMatcher { matcher, .. } = build_matcher(
            false,
            "you're only as funky\n as your last cut",
            SourceLanguage::Rust,
        )
        .unwrap();
        assert_eq!(
            Regex::new(r#"(?s)^you're only as funky\n as your last cut$"#)
                .unwrap()
                .as_str(),
            matcher.as_str()
        );
    }

    #[test]
    fn test_build_matcher_raw() {
        let MessageMatcher { matcher, .. } =
            build_matcher(true, "Hard-coded \\Windows\\Path", SourceLanguage::Rust).unwrap();
        assert_eq!(
            Regex::new(r#"(?s)^Hard-coded \\Windows\\Path$"#)
                .unwrap()
                .as_str(),
            matcher.as_str()
        );
    }

    #[test]
    fn test_literal_to_regex_escapes() {
        use SourceLanguage::*;
        let cases: &[(SourceLanguage, &str, &str)] = &[
            // A C backspace is not a regex word boundary.
            (Cpp, r"\b%c", r"\x08%c"),
            (Cpp, r"\a\f\v\e", r"\x07\x0C\x0B\x1B"),
            (Cpp, r"\x41\x4a", "AJ"),
            (Cpp, r"\101\0", r"A\x00"),
            (Cpp, r#"\"quoted\" \\path\?"#, r#""quoted" \\path\?"#),
            (Cpp, r"\u00e9\U0001F600", "é😀"),
            (Rust, r"caf\u{e9} \u{1F600}", "café 😀"),
            (Rust, r"\x41\0", r"A\x00"),
            (Rust, "one \\\n      two", "one two"),
            (Java, r"tab\there\s", r"tab\there "),
            (Java, r"\u00e9 \uuu0041 \uD83D\uDE00", "é A 😀"),
            (Python, r"\N{BULLET} item", ". item"),
            (Python, r"C:\dir\x41", r"C:\\dirA"),
            (Python, "one \\\n  two", "one   two"),
            // Malformed escapes are treated as literal text.
            (Rust, r"\u{zz}", "u\\{zz\\}"),
            (Cpp, r"\xg", "xg"),
            // Escapes for values that are not valid characters match any character.
            (Java, r"\uD83D!", ".!"),
            (Rust, r"\u{110000}x", ".x"),
            (Cpp, r"\xFFFFFFFF.", r".\."),
            // Regex meta-characters still get escaped.
            (
                Cpp,
                "a.b*c(d)[e]{f}|^$+?",
                r"a\.b\*c\(d\)\[e\]\{f\}\|\^\$\+\?",
            ),
        ];
        for (language, input, expected) in cases {
            assert_eq!(
                literal_to_regex(false, *language, input),
                *expected,
                "input {:?} for {:?}",
                input,
                language
            );
            assert!(Regex::new(expected).is_ok());
        }
    }

    #[test]
    fn test_build_matcher_backspace_is_not_word_boundary() {
        let MessageMatcher { matcher, .. } =
            build_matcher(false, r"\b%c", SourceLanguage::Cpp).unwrap();
        assert!(!matcher.is_match("zqx1 vwk2 jjq3"));
        assert!(matcher.is_match("\x08/"));
    }

    #[test]
    fn test_build_matcher_rust_unicode_escape() {
        let MessageMatcher { matcher, .. } =
            build_matcher(false, r"bullet \u{2022} {}", SourceLanguage::Rust).unwrap();
        assert!(matcher.is_match("bullet • 42"));
    }
}
