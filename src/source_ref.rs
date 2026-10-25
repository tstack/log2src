use crate::{CodeSource, QueryResult, SourceLanguage};
use core::fmt;
use regex::{Captures, Regex};
use serde::Serialize;
use std::sync::LazyLock;

#[derive(Clone, Debug, Serialize, Eq, PartialEq)]
pub enum FormatArgument {
    Named(String),
    Positional(usize),
    Placeholder,
}

/// The normalized level of a log statement, derived from the name of the logging call.
#[derive(Copy, Clone, Debug, Serialize, Eq, PartialEq)]
pub enum LogLevel {
    Trace,
    Debug,
    Info,
    Warn,
    Error,
    Fatal,
}

impl LogLevel {
    /// Map the name of a logging function/macro/method, like `log::warn`, `logger.warning`,
    /// `spdlog::info`, `log_debug`, or `SPDLOG_ERROR`, to a level.  This is also used for
    /// level arguments, like `LOG_ERR` or `spdlog::level::warn`.  Returns `None` for names that
    /// don't indicate a level, like `println` or `printf`.
    pub fn from_name(name: &str) -> Option<LogLevel> {
        let name = name
            .rsplit(|c: char| !(c.is_alphanumeric() || c == '_'))
            .find(|s| !s.is_empty())?
            .to_lowercase();
        let mut words = name.split('_').filter(|s| !s.is_empty());
        let last = words.next_back()?;
        // For names like `log_debug`, `SPDLOG_INFO`, or `LOG_ERR`, the level is at the end and
        // one of the other words needs to look logging related so that something like
        // `report_error` is not treated as a log statement.
        let mut prefix = words.peekable();
        if prefix.peek().is_some()
            && !prefix.any(|w| w.contains("log") || w == "level" || w == "lvl")
        {
            return None;
        }
        match last {
            "trace" | "finer" | "finest" => Some(LogLevel::Trace),
            "debug" | "dbg" | "fine" => Some(LogLevel::Debug),
            "info" | "notice" => Some(LogLevel::Info),
            "warn" | "warning" => Some(LogLevel::Warn),
            "error" | "err" | "exception" | "severe" => Some(LogLevel::Error),
            "fatal" | "critical" | "crit" | "alert" | "emerg" => Some(LogLevel::Fatal),
            _ => None,
        }
    }
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
#[derive(Clone, Debug, Serialize)]
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
    #[serde(skip_serializing_if = "Option::is_none")]
    pub level: Option<LogLevel>,
    pub quality: usize,
    #[serde(skip_serializing)]
    pub(crate) matcher: Regex,
    pub pattern: String,
    pub(crate) args: Vec<FormatArgument>,
    pub(crate) vars: Vec<String>,
}

struct MessageMatcher {
    matcher: Regex,
    quality: usize,
    pattern: String,
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
            pattern,
            mut args,
            quality,
        }) = build_matcher(result.raw, &unquoted, code.info.language)
        {
            let name = source[result.name_range].to_string();
            // A level passed as an argument, like `syslog(LOG_ERR, ...)`, takes precedence
            // over the name of the call.
            let level = result
                .leading_args
                .iter()
                .chain(result.call_name.iter())
                .find_map(|name| LogLevel::from_name(name));
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
                level,
                quality,
                matcher,
                pattern,
                args,
                vars: vec![],
            })
        } else {
            None
        }
    }

    pub fn captures<'a>(&self, line: &'a str) -> Option<Captures<'a>> {
        self.matcher.captures(line)
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
        let subtext = escape_ignore_newlines(raw, &text[last_end..placeholder.start()]);
        quality += subtext.chars().filter(|c| !c.is_whitespace()).count();
        pattern.push_str(subtext.as_str());
        last_end = placeholder.end();
        pattern.push_str("(.+)");
        args.push(language.captures_to_format_arg(&cap));
    }
    let subtext = escape_ignore_newlines(raw, &text[last_end..]);
    quality += subtext.chars().filter(|c| !c.is_whitespace()).count();
    if quality == 0 {
        None
    } else {
        pattern.push_str(subtext.as_str());
        pattern.push('$');
        Some(MessageMatcher {
            matcher: Regex::new(pattern.as_str()).unwrap(),
            quality,
            pattern,
            args,
        })
    }
}

/// Regex for finding values that need to be escaped in a string-literal.  The components are
/// as follows:
///
/// * `[.*+?^${}()|\[\]]` - Characters that are used in regexes and need to be escaped.
/// * `[\n\r\t]` - White space characters that we should turn into regex escape sequences.
/// * `\\[0-7]{3}|\\0` - Regex does not support octal escape-sequences, so we need to turn
///   them into a hex escape.
/// * `\\N\{[^}]+}` - Python named-Unicode escape that is turned into a `\w` since it would be
///   challenging to get the names all right.
static ESCAPE_REGEX: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r#"([.*+?^${}()|\[\]])|([\n\r\t])|(\\[0-7]{3}|\\0)|(\\N\{[^}]+})"#).unwrap()
});

/// Regex for finding values that need to be escaped in a raw string-literal.  The components are
/// as follows:
///
/// * `[.*+?^${}()|\[\]]` - Characters that are used in regexes and need to be escaped.
/// * `[\n\r\t]` - White space characters that we should turn into regex escape sequences.
/// * `\\` - A backslash
static RAW_ESCAPE_REGEX: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r#"([.*+?^${}()|\[\]])|([\n\r\t])|(\\)"#).unwrap());

/// Escape special chars except newlines and carriage returns in order to support multiline strings
fn escape_ignore_newlines(raw: bool, segment: &str) -> String {
    const HEX_CHARS: [char; 16] = [
        '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F',
    ];

    let mut result = String::with_capacity(segment.len() * 2);
    let mut last_end = 0;
    let regex = if raw {
        &RAW_ESCAPE_REGEX
    } else {
        &ESCAPE_REGEX
    };
    for cap in regex.captures_iter(segment) {
        let overall_range = cap.get(0).unwrap().range();
        result.push_str(segment[last_end..overall_range.start].as_ref());
        last_end = overall_range.end;
        if let Some(c) = cap.get(1) {
            result.push('\\');
            result.push_str(c.as_str());
        } else if let Some(c) = cap.get(2) {
            match c.as_str() {
                "\n" => result.push_str("\\n"),
                "\r" => result.push_str("\\r"),
                "\t" => result.push_str("\\t"),
                _ => unreachable!(),
            }
        } else if let Some(c) = cap.get(3) {
            if raw {
                result.push('\\');
                result.push_str(c.as_str());
            } else {
                let c = c.as_str();
                let c = &c[1..];
                let c = u8::from_str_radix(c, 8).unwrap();
                result.push('\\');
                result.push('x');
                result.push(HEX_CHARS[(c >> 4) as usize]);
                result.push(HEX_CHARS[(c & 0xf) as usize]);
            }
        } else if let Some(_c) = cap.get(4) {
            // XXX This is the fancy Python "\N{...}" escape sequence.  Ideally, we'd interpret the
            // name of the escape, but that seems like a lot of work.  So, we'll just match any
            // character.
            result.push_str("\\w");
        } else {
            unreachable!();
        }
    }
    result.push_str(segment[last_end..].as_ref());
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_log_level_from_name() {
        let cases = [
            ("debug", Some(LogLevel::Debug)),
            ("log::warn", Some(LogLevel::Warn)),
            ("tracing::trace", Some(LogLevel::Trace)),
            ("error", Some(LogLevel::Error)),
            ("info", Some(LogLevel::Info)),
            ("spdlog::info", Some(LogLevel::Info)),
            ("spdlog::critical", Some(LogLevel::Fatal)),
            ("logger->warn", Some(LogLevel::Warn)),
            ("SPDLOG_ERROR", Some(LogLevel::Error)),
            ("logger.warning", Some(LogLevel::Warn)),
            ("logging.exception", Some(LogLevel::Error)),
            ("self.log.critical", Some(LogLevel::Fatal)),
            ("fine", Some(LogLevel::Debug)),
            ("log_debug", Some(LogLevel::Debug)),
            ("log_warning", Some(LogLevel::Warn)),
            ("LOG_ERR", Some(LogLevel::Error)),
            ("LOG_CRIT", Some(LogLevel::Fatal)),
            ("APLOG_MARK", None),
            ("spdlog::level::warn", Some(LogLevel::Warn)),
            ("LEVEL_INFO", Some(LogLevel::Info)),
            ("println", None),
            ("printf", None),
            ("print", None),
            ("report_error", None),
        ];
        for (name, expected) in cases {
            assert_eq!(LogLevel::from_name(name), expected, "{name}");
        }
    }

    #[test]
    fn test_build_matcher_needs_escape() {
        let MessageMatcher {
            matcher,
            pattern: _pat,
            args: _args,
            ..
        } = build_matcher(false, "{}) {}, {} \\033", SourceLanguage::Rust).unwrap();
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
        let MessageMatcher { matcher, .. } = build_matcher(
            true,
            "Hard-coded \\Windows\\Path",
            SourceLanguage::Rust,
        )
            .unwrap();
        assert_eq!(
            Regex::new(r#"(?s)^Hard-coded \\Windows\\Path$"#)
                .unwrap()
                .as_str(),
            matcher.as_str()
        );
    }
}
