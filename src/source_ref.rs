use crate::java_symbols::MessageRef;
use crate::value_kind::{self, ValueKind, ANY_CAPTURE};
use crate::{CodeSource, QueryResult, SourceLanguage};
use core::fmt;
use regex::{Captures, Regex};
use serde::{Deserialize, Serialize};
use std::str::Chars;
use std::sync::OnceLock;

#[derive(Clone, Debug, Serialize, Deserialize, Eq, PartialEq)]
pub enum FormatArgument {
    Named(String),
    Positional(usize),
    Placeholder,
}

/// The normalized level of a log statement, derived from the name of the logging call.
#[derive(
    Copy, Clone, Debug, Serialize, Deserialize, Eq, PartialEq, Ord, PartialOrd, clap::ValueEnum,
)]
pub enum LogLevel {
    Trace,
    Debug,
    Info,
    Warn,
    Error,
    Fatal,
    /// The level could not be determined, which also means the statement might not be logging
    /// at all, like a `printf()` or a call that just happens to take a string.
    Unknown,
}

impl LogLevel {
    /// Map the name of a logging function/macro/method, like `log::warn`, `logger.warning`,
    /// `spdlog::info`, `log_debug`, `logInfo`, `SPDLOG_ERROR`, or `ws_warning`, to a level.
    /// Returns `None` for names that don't indicate a level, like `println`, `printf`, or
    /// `parser.error`.  An unqualified name that ends in a level after a prefix that isn't
    /// logging related, like `ws_warning` or `report_error`, is given a level too.  Whether
    /// such a prefix is really a logger is decided later, across all of the calls in a source
    /// tree, using [`LogLevel::call_family`].
    pub fn from_name(name: &str) -> Option<LogLevel> {
        // An attribute, like thiserror's `#[error("...")]`, is not a logging call.
        if name.starts_with('#') {
            return None;
        }
        Self::from_known_name(name)
            .or_else(|| Self::from_prefixed_name(name).map(|(level, _)| level))
    }

    /// Like [`LogLevel::from_name`], but only for names that are known to be logging on their
    /// own, without the names with a prefix that might not be a logger.
    fn from_known_name(name: &str) -> Option<LogLevel> {
        Self::classify(name, false)
    }

    /// The family of a call whose level only comes from a prefix that might not be a logger,
    /// which is the prefix, like `ws` for `ws_warning` and `report` for `reportError`.  Returns
    /// `None` for names that are known to be logging, or don't indicate a level.
    pub fn call_family(name: &str) -> Option<String> {
        if Self::from_known_name(name).is_some() {
            return None;
        }
        Self::from_prefixed_name(name).map(|(_, family)| family)
    }

    /// The level and prefix of an unqualified name that ends in a level, like `ws_warning`.
    /// "message" is taken as `Info` here, like GLib's `g_message`, since the family check
    /// does not count `Info`.
    fn from_prefixed_name(name: &str) -> Option<(LogLevel, String)> {
        if name.contains(|c: char| !(c.is_alphanumeric() || c == '_')) {
            return None;
        }
        let mut words = split_words(name);
        let last = words.pop()?;
        if words.is_empty() {
            return None;
        }
        let level = match last.as_str() {
            "message" => Some(LogLevel::Info),
            _ => Self::from_word(&last),
        };
        level.map(|level| (level, words.join("_")))
    }

    /// Map an argument that is passed to a logging call, like `LOG_ERR`, `logging.WARNING`, or
    /// `spdlog::level::warn`, to a level.  Unlike [`LogLevel::from_name`], the argument has to
    /// be qualified by something logging related, so that a variable like `err` is ignored.
    pub fn from_level_arg(arg: &str) -> Option<LogLevel> {
        Self::classify(arg, true)
    }

    /// Map the level text from a log message, like `WARN` or `error`, to a level.
    pub fn from_log_text(text: &str) -> Option<LogLevel> {
        let word = text.trim().to_lowercase();
        Self::from_word(&word).or_else(|| Self::from_jul_word(&word))
    }

    fn classify(name: &str, require_qualifier: bool) -> Option<LogLevel> {
        let mut segments: Vec<&str> = name
            .split(|c: char| !(c.is_alphanumeric() || c == '_'))
            .filter(|s| !s.is_empty())
            .collect();
        let mut words = split_words(segments.pop()?);
        let last = words.pop()?;
        // For names like `log_debug`, `SPDLOG_INFO`, or `LOG_ERR`, the level is at the end and
        // one of the other words needs to look logging related so that something like
        // `report_error` is not treated as a log statement.
        if !words.is_empty() {
            // A prefix of single letters, like the `q` in Qt's `qWarning`, the `qC` in
            // `qCDebug`, or the `g` in GLib's `g_warning`, is a library namespace instead of a
            // logging word.  Longer words are not accepted since `on_error` is not logging.
            if segments.is_empty() && words.iter().all(|w| w.chars().count() == 1) {
                return match (&words[..], last.as_str()) {
                    ([g], "message") if g == "g" => Some(LogLevel::Info),
                    _ => Self::from_word(&last),
                };
            }
            // The level is usually at the end, but there can be a suffix after it, like the
            // `once` in `log_warn_once`, the `if` in `LOG_INFO_IF`, or the `hand` in
            // `tr_logAddTraceHand`.  In that case, the level has to come after a logging word.
            // If the logging word is only in the qualifier, like `logger.warning_once`, the
            // level has to be the first word so that `logger.isDebugEnabled` is not a level.
            words.push(last);
            if let Some(pos) = words.iter().position(|w| is_logging_word(w)) {
                return words[pos + 1..]
                    .iter()
                    .rev()
                    .find_map(|w| Self::from_word(w));
            }
            // A level followed by OpenSSH's suffixes, like `fatal_fr`, `error_r`, and
            // `debug3_f`, which add the function name and the error code.
            if segments.is_empty()
                && !require_qualifier
                && words[1..]
                    .iter()
                    .all(|w| matches!(w.as_str(), "f" | "r" | "fr"))
            {
                if let Some(level) = Self::from_word(&words[0]) {
                    return Some(level);
                }
            }
            let qualified = segments
                .iter()
                .flat_map(|seg| split_words(seg))
                .any(|w| is_logging_word(&w));
            return if qualified {
                Self::from_word(&words[0])
            } else {
                None
            };
        }
        // For a qualified name, like `logger.warn` or `spdlog::level::info`, the qualifier
        // needs to look logging related so that something like `warnings.warn` or
        // `parser.error` is not treated as a log statement.
        let qualified = segments
            .iter()
            .flat_map(|seg| split_words(seg))
            .any(|w| is_logging_word(&w));
        if segments.is_empty() && !require_qualifier && matches!(last.as_str(), "err" | "errx") {
            // The BSD `err.h` functions that exit the process, unlike `warn` and `warnx`.
            Some(LogLevel::Fatal)
        } else if qualified || (segments.is_empty() && !require_qualifier) {
            // A java.util.logging level can also be a whole name, like the `config` method or
            // `Level.CONFIG`.
            Self::from_word(&last).or_else(|| Self::from_jul_word(&last))
        } else {
            None
        }
    }

    fn from_word(word: &str) -> Option<LogLevel> {
        // A verbosity, like the `2` in OpenSSH's `debug2`.
        let word = match word.trim_end_matches(|c: char| c.is_ascii_digit()) {
            "debug" => "debug",
            _ => word,
        };
        match word {
            "trace" | "finer" | "finest" => Some(LogLevel::Trace),
            // `verbose` is below the default level in OpenSSH and Redis, like debug.
            "debug" | "dbg" | "fine" | "verbose" => Some(LogLevel::Debug),
            "info" | "notice" => Some(LogLevel::Info),
            // The BSD `err.h` functions and OpenBSD's `fatalx` do not append `errno`.
            "warn" | "warning" | "warnx" => Some(LogLevel::Warn),
            "error" | "err" | "exception" | "severe" => Some(LogLevel::Error),
            "fatal" | "fatalx" | "critical" | "crit" | "alert" | "emerg" => Some(LogLevel::Fatal),
            _ => None,
        }
    }

    /// Levels that are only words on their own when they are clearly from java.util.logging.
    /// `config` is a level between `info` and `fine`, but it is also part of many names that
    /// have nothing to do with logging, like `log_config`.
    fn from_jul_word(word: &str) -> Option<LogLevel> {
        (word == "config").then_some(LogLevel::Info)
    }
}

fn is_logging_word(word: &str) -> bool {
    // Words that contain "log" but have nothing to do with logging.
    const NOT_LOGGING: &[&str] = &[
        "analog",
        "backlog",
        "blog",
        "catalog",
        "changelog",
        "dialog",
        "epilog",
        "logic",
        "logical",
        "login",
        "logo",
        "logon",
        "logout",
        "prolog",
    ];
    (word.contains("log") && !word.contains("ology") && !NOT_LOGGING.contains(&word))
        // `ll` is short for "log level", like Redis's `LL_WARNING`.
        || matches!(word, "level" | "lvl" | "ll" | "tracing")
}

/// Split an identifier into lowercase words on underscores and case changes, so `log_debug`,
/// `logDebug`, `LogDebug`, and `LOG_DEBUG` all become `["log", "debug"]`.
fn split_words(ident: &str) -> Vec<String> {
    let chars: Vec<char> = ident.chars().collect();
    let mut words = Vec::new();
    let mut word = String::new();
    for (i, &c) in chars.iter().enumerate() {
        if c == '_' {
            if !word.is_empty() {
                words.push(std::mem::take(&mut word));
            }
            continue;
        }
        if c.is_uppercase() && !word.is_empty() {
            let prev = chars[i - 1];
            let next_is_lower = chars.get(i + 1).is_some_and(|n| n.is_lowercase());
            // Split `logDebug` before the `D` and `LOGDebug` before the `D`, but not `SPDLOG`.
            if prev.is_lowercase()
                || prev.is_ascii_digit()
                || (prev.is_uppercase() && next_is_lower)
            {
                words.push(std::mem::take(&mut word));
            }
        }
        word.extend(c.to_lowercase());
    }
    if !word.is_empty() {
        words.push(word);
    }
    words
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

/// What a placeholder in a format string is replaced with at runtime.
pub(crate) enum Substitution {
    /// A literal character, like the `%` for `%%` or the `{` for `{{`.
    Literal(char),
    /// Nothing, like for `%n`, which stores the number of characters written so far.
    Nothing,
    /// The value of an argument.
    Value(FormatArgument),
}

/// Tracks the arguments used by the placeholders in a format string.  Some printf-style
/// placeholders use arguments without printing them, like `%n` or the `*` in `%*d`, so the
/// placeholders after them refer to their arguments by position.
#[derive(Default)]
pub(crate) struct ArgCounter {
    /// The number of arguments used so far.
    used: usize,
    /// The number of `FormatArgument::Placeholder`s returned so far.
    placeholders: usize,
}

impl ArgCounter {
    pub(crate) fn substitution(
        &mut self,
        language: SourceLanguage,
        caps: &Captures,
    ) -> Substitution {
        let text = caps.get(0).unwrap().as_str();
        match text {
            "{{" => return Substitution::Literal('{'),
            "}}" => return Substitution::Literal('}'),
            _ => {}
        }
        if let Some(spec) = text.strip_prefix('%') {
            if spec.ends_with('%') {
                return Substitution::Literal('%');
            }
            if language.is_c_family() && spec.ends_with('m') {
                // glibc's `%m` prints the message for `errno` without using an argument.
                return Substitution::Value(FormatArgument::Named("strerror(errno)".to_string()));
            }
            if let Some((index, _)) = spec.split_once('$') {
                // An explicit argument, like `%2$s`, which is 1-based.
                if let Some(index) = index.parse::<usize>().ok().and_then(|i| i.checked_sub(1)) {
                    return Substitution::Value(FormatArgument::Positional(index));
                }
            }
            // A `*` width or precision is taken from an argument.
            self.used += spec.matches('*').count();
            if spec.ends_with('n') {
                self.used += 1;
                return Substitution::Nothing;
            }
        }
        Substitution::Value(match language.captures_to_format_arg(caps) {
            FormatArgument::Placeholder => {
                let index = self.used;
                self.used += 1;
                if index == self.placeholders {
                    self.placeholders += 1;
                    FormatArgument::Placeholder
                } else {
                    FormatArgument::Positional(index)
                }
            }
            arg => arg,
        })
    }
}

/// What a statement's message is used for.  Statements are found by their shape, like a call
/// that takes a format string, so this is decided after extraction, and log messages are only
/// matched against other kinds of statements when no `Log` statement matches.  The order in
/// which the categories are tried is given by [`MessageCategory::match_priority`], not by the
/// order of the variants.
#[derive(Copy, Clone, Debug, Serialize, Deserialize, Eq, PartialEq, Ord, PartialOrd)]
pub enum MessageCategory {
    /// A logging call, whose level is in `SourceRef::level`.
    Log,
    /// An error or panic message, like `bail!("...")`, `.context("...")`, thiserror's
    /// `#[error("...")]`, or `.expect("...")`.
    Error,
    /// A message that is formatted and then used somewhere else, like `format!("...")`, or
    /// written by a `Display` impl.
    Format,
    /// Some other use of a message, like `println!("...")`, or a call in a family that
    /// `prune_log_calls()` decided does not look like logging.
    Other,
}

impl MessageCategory {
    /// The tier that statements in this category are matched in when looking for the source of
    /// a log message, lowest first.  A statement in a later tier is only used when none in an
    /// earlier tier matches.  After the log statements, the order is from the most to the least
    /// likely to be printed as a line on its own, like a `println!()`.
    pub fn match_priority(&self) -> u8 {
        match self {
            MessageCategory::Log => 0,
            MessageCategory::Other => 1,
            MessageCategory::Error => 2,
            MessageCategory::Format => 3,
        }
    }

    /// The category of a statement that is not in a pruned family.  A call that is known not to
    /// be logging, like `bail!` or `.context()`, has a category from its name, even if the name
    /// looks like it has a level, like `Err`.  Otherwise, a statement with a level is `Log`.
    /// Only Rust is classified by name for now, so the statements in other languages are `Log`.
    pub(crate) fn classify(src_ref: &SourceRef) -> MessageCategory {
        if let Some(category) = Self::from_call(src_ref) {
            return category;
        }
        if src_ref.level != LogLevel::Unknown || src_ref.language != SourceLanguage::Rust {
            return MessageCategory::Log;
        }
        match Self::short_call_name(src_ref) {
            // a level that is not known until runtime, like `log!(lvl, "...")`
            "log" | "event" => MessageCategory::Log,
            _ => MessageCategory::Other,
        }
    }

    /// The category of a call that is known not to be logging, from its name and the function
    /// it is in.
    pub(crate) fn from_call(src_ref: &SourceRef) -> Option<MessageCategory> {
        if src_ref.language != SourceLanguage::Rust {
            return None;
        }
        let call_name = Self::short_call_name(src_ref);
        if Self::is_rust_error_call(call_name) {
            return Some(MessageCategory::Error);
        }
        let category = match call_name {
            "format" | "format_args" => MessageCategory::Format,
            "print" | "println" | "eprint" | "eprintln" => MessageCategory::Other,
            "write" | "writeln" => Self::classify_write(&src_ref.qualified_name),
            _ => return None,
        };
        Some(category)
    }

    /// Check if a Rust call, by the last part of its name, makes an error or panic with the
    /// message, like `bail!("...")` or `.context("...")`.
    pub(crate) fn is_rust_error_call(name: &str) -> bool {
        matches!(
            name,
            "bail"
                | "anyhow"
                | "ensure"
                | "eyre"
                | "context"
                | "with_context"
                | "wrap_err"
                | "wrap_err_with"
                | "Err"
                | "ok_or"
                | "ok_or_else"
                | "map_err"
                | "#[error]"
                | "panic"
                | "unreachable"
                | "todo"
                | "unimplemented"
                | "assert"
                | "assert_eq"
                | "assert_ne"
                | "debug_assert"
                | "debug_assert_eq"
                | "debug_assert_ne"
                | "expect"
                | "expect_err"
        )
    }

    /// The last part of the name of the call, like `context` for `.context()` or `anyhow` for
    /// `anyhow::anyhow!`.
    fn short_call_name(src_ref: &SourceRef) -> &str {
        let call_name = src_ref.call_name.as_deref().unwrap_or_default();
        call_name.rsplit(['.', ':']).next().unwrap_or(call_name)
    }

    /// A `write!` in `<Type as Display>::fmt` is the message of an error type when the type
    /// is named like one, `Format` in any other `fmt`, and `Other` everywhere else, like a
    /// write to a file.
    fn classify_write(qualified_name: &str) -> MessageCategory {
        let Some(impl_name) = qualified_name.strip_suffix("::fmt") else {
            return MessageCategory::Other;
        };
        // The impl is named like `<Type<T> as fmt::Display>`, after the names of any modules.
        let Some((before_as, _)) = impl_name.rsplit_once(" as ") else {
            return MessageCategory::Format;
        };
        let start = match before_as.find("::<") {
            Some(index) => index + 3,
            None => usize::from(before_as.starts_with('<')),
        };
        let ty = before_as[start..].split('<').next().unwrap_or_default();
        let ty = ty.rsplit("::").next().unwrap_or(ty);
        if impl_name.ends_with("Display>") && (ty.ends_with("Error") || ty.ends_with("Err")) {
            MessageCategory::Error
        } else {
            MessageCategory::Format
        }
    }
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
    /// The name of the enclosing function qualified by its containers, like namespaces,
    /// classes, and modules.
    #[serde(rename(serialize = "qualifiedName"))]
    pub qualified_name: String,
    /// The start byte of the innermost lexical block containing the call.  Statements with the
    /// same `source_path` and `block_id` are in the same block.
    #[serde(rename(serialize = "blockId"))]
    pub block_id: u32,
    pub text: String,
    pub level: LogLevel,
    pub category: MessageCategory,
    /// The name of the logging function/macro/method that was called, as written in the source,
    /// like `ws_debug`, `logger.info`, or `syslog`.
    #[serde(rename(serialize = "callName"))]
    pub call_name: Option<String>,
    pub quality: usize,
    #[serde(with = "serde_regex")]
    pub(crate) pattern: Regex,
    /// The string form of `pattern`, kept for lnav.
    #[serde(skip)]
    pub pattern_str: String,
    pub(crate) args: Vec<FormatArgument>,
    /// The kind of value produced by the expression of each `FormatArgument::Named` in `args`.
    #[serde(rename(serialize = "argKinds"))]
    pub(crate) arg_kinds: Vec<ValueKind>,
    pub(crate) vars: Vec<String>,
    /// The kind of value produced by each expression in `vars`.
    #[serde(rename(serialize = "varKinds"))]
    pub(crate) var_kinds: Vec<ValueKind>,
    /// The kind of value expected for each placeholder based on its format spec.
    pub(crate) kinds: Vec<ValueKind>,
    /// The regexes in `pattern` for the literal text before, between, and after the
    /// placeholders.
    pub(crate) segments: Vec<String>,
    /// `kinds` refined by the argument expressions.  This, and `segment_matchers`, are only
    /// computed when needed since most statements are never matched.
    #[serde(skip)]
    value_kinds: OnceLock<Vec<ValueKind>>,
    #[serde(skip)]
    segment_matchers: OnceLock<Option<Vec<Regex>>>,
    #[serde(skip)]
    lazy_matcher: OnceLock<Option<Regex>>,
    #[serde(skip)]
    separators: OnceLock<Option<Vec<Regex>>>,
    #[serde(skip)]
    non_empty_matcher: OnceLock<Option<Regex>>,
}

struct MessageMatcher {
    matcher: Regex,
    quality: usize,
    args: Vec<FormatArgument>,
    kinds: Vec<ValueKind>,
    segments: Vec<String>,
}

impl SourceRef {
    pub(crate) fn new(code: &CodeSource, result: QueryResult) -> Option<SourceRef> {
        let range = result.range;
        let level = result.level();
        let call_name = result.call_name.clone();
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
            kinds,
            segments,
        }) = build_matcher(result.raw, &unquoted, code.info.language)
        {
            let name = result.name;
            let arg_kinds = if result.args.is_empty() {
                vec![ValueKind::Any; args.len()]
            } else {
                let arg_kinds;
                (args, arg_kinds) = result.args.into_iter().unzip();
                arg_kinds
            };
            let mut src_ref = SourceRef {
                source_path: code.filename.clone(),
                language: code.info.language,
                line_no,
                end_line_no,
                column: col,
                name,
                qualified_name: result.qualified_name,
                block_id: result.block_id,
                text,
                level,
                category: MessageCategory::Log,
                call_name,
                quality,
                pattern_str: matcher.as_str().to_string(),
                pattern: matcher,
                args,
                arg_kinds,
                vars: vec![],
                var_kinds: vec![],
                kinds,
                segments,
                value_kinds: OnceLock::new(),
                segment_matchers: OnceLock::new(),
                lazy_matcher: OnceLock::new(),
                separators: OnceLock::new(),
                non_empty_matcher: OnceLock::new(),
            };
            // Redone by `prune_log_calls()`, which can change the level.
            src_ref.category = MessageCategory::classify(&src_ref);
            if src_ref.category != MessageCategory::Log {
                // Only log statements have a level, the name of an error call, like `Err`,
                // does not mean anything.
                src_ref.level = LogLevel::Unknown;
            }
            Some(src_ref)
        } else {
            None
        }
    }

    /// Create a statement for a Java log call whose message is the given constant value.  The
    /// location is the call site, not where the constant is defined.
    pub(crate) fn from_message_ref(
        source_path: &str,
        message_ref: &MessageRef,
        value: &str,
    ) -> Option<SourceRef> {
        let MessageMatcher {
            matcher,
            args,
            quality,
            kinds,
            segments,
        } = build_matcher(false, value, SourceLanguage::Java)?;
        Some(SourceRef {
            source_path: source_path.to_string(),
            language: SourceLanguage::Java,
            line_no: message_ref.line_no,
            end_line_no: message_ref.end_line_no,
            column: message_ref.column,
            name: message_ref.name.clone(),
            qualified_name: message_ref.qualified_name.clone(),
            block_id: message_ref.block_id,
            text: message_ref.text.clone(),
            level: message_ref.level,
            category: MessageCategory::Log,
            call_name: message_ref.call_name.clone(),
            quality,
            pattern_str: matcher.as_str().to_string(),
            pattern: matcher,
            arg_kinds: vec![ValueKind::Any; args.len()],
            args,
            vars: message_ref.vars.clone(),
            var_kinds: message_ref.var_kinds.clone(),
            kinds,
            segments,
            value_kinds: OnceLock::new(),
            segment_matchers: OnceLock::new(),
            lazy_matcher: OnceLock::new(),
            separators: OnceLock::new(),
            non_empty_matcher: OnceLock::new(),
        })
    }

    pub fn captures<'a>(&self, line: &'a str) -> Option<Captures<'a>> {
        self.pattern.captures(line)
    }

    /// The regex used to match log messages to this statement.
    pub fn pattern(&self) -> &Regex {
        &self.pattern
    }

    /// The argument expression for each placeholder and the kind of value it produces, in the
    /// order the placeholders appear in the message.
    fn resolved_args(&self) -> impl Iterator<Item = (&str, ValueKind)> {
        let var = |index: usize| {
            (
                self.vars.get(index).map_or("<unknown>", String::as_str),
                self.var_kinds.get(index).copied().unwrap_or(ValueKind::Any),
            )
        };
        let mut placeholder_index = 0;
        self.args
            .iter()
            .enumerate()
            .map(move |(index, arg)| match arg {
                FormatArgument::Named(name) => (
                    name.as_str(),
                    self.arg_kinds.get(index).copied().unwrap_or(ValueKind::Any),
                ),
                FormatArgument::Positional(pos) => var(*pos),
                FormatArgument::Placeholder => {
                    placeholder_index += 1;
                    var(placeholder_index - 1)
                }
            })
    }

    /// The argument expressions for each placeholder, in the order the placeholders appear in
    /// the message.
    pub(crate) fn arg_exprs(&self) -> Vec<&str> {
        self.resolved_args().map(|(expr, _)| expr).collect()
    }

    /// The kinds of values expected for the placeholders, based on the format spec and, when
    /// the spec does not have a kind, the argument expression.  These are computed the first
    /// time they are needed and then cached.
    pub(crate) fn value_kinds(&self) -> &[ValueKind] {
        self.value_kinds.get_or_init(|| {
            std::iter::zip(&self.kinds, self.resolved_args())
                .map(|(kind, (_, expr_kind))| match kind {
                    ValueKind::Any => expr_kind,
                    _ => *kind,
                })
                .collect()
        })
    }

    /// Anchored regexes for the literal text before, between, and after the placeholders.
    pub(crate) fn segment_matchers(&self) -> Option<&[Regex]> {
        self.segment_matchers
            .get_or_init(|| value_kind::compile_segments(&self.segments))
            .as_deref()
    }

    /// A matcher like `pattern`, but with lazy captures.
    pub(crate) fn lazy_matcher(&self) -> Option<&Regex> {
        self.lazy_matcher
            .get_or_init(|| value_kind::compile_matcher(&self.segments, "(.*?)"))
            .as_ref()
    }

    /// Unanchored regexes for the literal text after each placeholder.
    pub(crate) fn separators(&self) -> Option<&[Regex]> {
        self.separators
            .get_or_init(|| value_kind::compile_separators(&self.segments))
            .as_deref()
    }

    /// Check if `body` matches this statement with a non-empty value for every placeholder.
    pub(crate) fn matches_without_empty_values(&self, body: &str) -> bool {
        if self.kinds.is_empty() {
            return self.pattern.is_match(body);
        }
        self.non_empty_matcher
            .get_or_init(|| value_kind::compile_matcher(&self.segments, "(.+)"))
            .as_ref()
            .is_some_and(|matcher| matcher.is_match(body))
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
    let mut kinds = Vec::new();
    let mut segments = Vec::new();
    let mut last_end = 0;
    let mut pattern = "(?s)^".to_string();
    // Where the capture group for the last placeholder ends in `pattern`.
    let mut last_group_end = pattern.len();
    let mut quality = 0;
    // The regex for literal text that has not been added to `pattern` yet.
    let mut pending = String::new();
    let mut counter = ArgCounter::default();
    for cap in language.get_placeholder_regex().captures_iter(text) {
        let placeholder = cap.get(0).unwrap();
        if !raw && is_unicode_escape(&text[..placeholder.start()]) {
            // Something like Rust's "\u{1F600}" is an escape and not a placeholder.
            continue;
        }
        pending.push_str(&literal_to_regex(
            raw,
            language,
            &text[last_end..placeholder.start()],
        ));
        last_end = placeholder.end();
        let arg = match counter.substitution(language, &cap) {
            Substitution::Literal(c) => {
                push_regex_literal(&mut pending, c);
                continue;
            }
            Substitution::Nothing => continue,
            Substitution::Value(arg) => arg,
        };
        let subtext = std::mem::take(&mut pending);
        quality += subtext.chars().filter(|c| !c.is_whitespace()).count();
        pattern.push_str(subtext.as_str());
        segments.push(subtext);
        // The kind of value is only used to split the values, so a value that does not look
        // like the format spec, such as a date for `{:%Y-%m-%d}`, still matches.
        pattern.push_str(ANY_CAPTURE);
        last_group_end = pattern.len();
        kinds.push(ValueKind::from_placeholder(language, placeholder.as_str()));
        args.push(arg);
    }
    let mut subtext = pending;
    subtext.push_str(&literal_to_regex(raw, language, &text[last_end..]));
    quality += subtext.chars().filter(|c| !c.is_whitespace()).count();
    if quality == 0 {
        None
    } else {
        pattern.push_str(subtext.as_str());
        // Trailing whitespace, like the newline at the end of a multi-line message, is often
        // trimmed by the logging framework or the log viewer, so it is optional.
        let trimmed_len = trim_trailing_whitespace_regex(&pattern).len();
        if trimmed_len < pattern.len() && trimmed_len > "(?s)^".len() {
            pattern.truncate(trimmed_len);
            if pattern.ends_with(ANY_CAPTURE) {
                // Leave the whitespace out of the value of a placeholder at the end.
                pattern.insert(pattern.len() - 1, '?');
                last_group_end += 1;
            }
            pattern.push_str("\\s*");
        }
        segments.push(pattern[last_group_end..].to_string());
        pattern.push('$');
        // A pattern that does not compile is not usable, so skip the log statement.
        Regex::new(pattern.as_str())
            .ok()
            .map(|matcher| MessageMatcher {
                matcher,
                quality,
                args,
                kinds,
                segments,
            })
    }
}

/// Remove the whitespace at the end of a regex built by `push_regex_literal()`.
fn trim_trailing_whitespace_regex(regex: &str) -> &str {
    let mut rest = regex;
    loop {
        if let Some(prefix) = rest.strip_suffix(' ') {
            rest = prefix;
            continue;
        }
        let escaped = ["\\n", "\\r", "\\t"]
            .iter()
            .find_map(|esc| rest.strip_suffix(esc))
            // The backslash must not itself be escaped, like in `\\n`.
            .filter(|prefix| (prefix.len() - prefix.trim_end_matches('\\').len()) % 2 == 0);
        match escaped {
            Some(prefix) => rest = prefix,
            None => return rest,
        }
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
            'e' if language.is_c_family() => Some('\x1B'),
            'f' if language != SourceLanguage::Rust => Some('\x0C'),
            'v' if matches!(
                language,
                SourceLanguage::C | SourceLanguage::Cpp | SourceLanguage::Python
            ) =>
            {
                Some('\x0B')
            }
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
                // C and C++ hex escapes consume as many digits as are present.
                let max = if language.is_c_family() { 8 } else { 2 };
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
            'U' if matches!(
                language,
                SourceLanguage::C | SourceLanguage::Cpp | SourceLanguage::Python
            ) =>
            {
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
            ("report_error", Some(LogLevel::Error)),
            ("logInfo", Some(LogLevel::Info)),
            ("LogWarning", Some(LogLevel::Warn)),
            ("m_logger->logError", Some(LogLevel::Error)),
            ("LOGError", Some(LogLevel::Error)),
            ("reportError", Some(LogLevel::Error)),
            ("tracing::error", Some(LogLevel::Error)),
            ("spdlog::get(\"app\")->warn", Some(LogLevel::Warn)),
            ("warnings.warn", None),
            ("parser.error", None),
            ("errors.error", None),
            ("debug2", Some(LogLevel::Debug)),
            ("debug3_f", Some(LogLevel::Debug)),
            ("fatal_fr", Some(LogLevel::Fatal)),
            ("error_f", Some(LogLevel::Error)),
            ("fatalx", Some(LogLevel::Fatal)),
            ("warnx", Some(LogLevel::Warn)),
            ("verbose_f", Some(LogLevel::Debug)),
            ("set_verbose", Some(LogLevel::Debug)),
            ("trace_on", None),
            ("debug_fn", None),
            ("error_no", None),
            ("alert_ok", None),
            ("err2", None),
            ("info1", None),
            ("debug2_fr", Some(LogLevel::Debug)),
            ("error_r", Some(LogLevel::Error)),
            ("err", Some(LogLevel::Fatal)),
            ("errx", Some(LogLevel::Fatal)),
            ("logger.err", Some(LogLevel::Error)),
            ("error_message", Some(LogLevel::Info)),
            ("info_get", None),
        ];
        for (name, expected) in cases {
            assert_eq!(LogLevel::from_name(name), expected, "{name}");
        }
    }

    #[test]
    fn test_call_family() {
        let cases = [
            ("ws_warning", Some("ws")),
            ("reportError", Some("report")),
            ("zbee_append_info", Some("zbee_append")),
            ("luaL_error", Some("lua_l")),
            ("log_debug", None),
            ("g_warning", None),
            ("error", None),
            ("logger.error", None),
            ("parser.error", None),
            ("ws_log", None),
            ("ws_message", Some("ws")),
        ];
        for (name, expected) in cases {
            assert_eq!(LogLevel::call_family(name).as_deref(), expected, "{name}");
        }
    }

    #[test]
    fn test_log_level_from_level_arg() {
        let cases = [
            ("LOG_ERR", Some(LogLevel::Error)),
            ("spdlog::level::trace", Some(LogLevel::Trace)),
            ("logging.WARNING", Some(LogLevel::Warn)),
            ("Level::Warn", Some(LogLevel::Warn)),
            ("tracing::Level::INFO", Some(LogLevel::Info)),
            ("Level.SEVERE", Some(LogLevel::Error)),
            ("err", None),
            ("info", None),
            ("level", None),
            ("errors.error", None),
            ("LL_WARNING", Some(LogLevel::Warn)),
            ("LL_DEBUG", Some(LogLevel::Debug)),
            ("LL_VERBOSE", Some(LogLevel::Debug)),
            ("SYSLOG_LEVEL_VERBOSE", Some(LogLevel::Debug)),
            ("NGX_LOG_ERR", Some(LogLevel::Error)),
        ];
        for (name, expected) in cases {
            assert_eq!(LogLevel::from_level_arg(name), expected, "{name}");
        }
    }

    #[test]
    fn test_log_level_from_log_text() {
        let cases = [
            ("WARN", Some(LogLevel::Warn)),
            ("warning", Some(LogLevel::Warn)),
            (" ERROR ", Some(LogLevel::Error)),
            ("W", None),
        ];
        for (name, expected) in cases {
            assert_eq!(LogLevel::from_name(name), expected, "{name}");
        }
    }

    #[test]
    fn test_build_matcher_needs_escape() {
        let MessageMatcher {
            matcher,
            args: _args,
            ..
        } = build_matcher(false, "{}) {}, {} \\033", SourceLanguage::Cpp).unwrap();
        assert_eq!(
            Regex::new(r#"(?s)^(.*)\) (.*), (.*) \x1B$"#)
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
            Regex::new(r#"(?s)^abc (.*) def$"#).unwrap().as_str(),
            matcher.as_str()
        );
    }

    #[test]
    fn test_build_matcher_mix() {
        let MessageMatcher { matcher, args, .. } =
            build_matcher(false, "{}) {:?}, {foo.bar}", SourceLanguage::Rust).unwrap();
        assert_eq!(
            Regex::new(r#"(?s)^(.*)\) (.*), (.*)$"#).unwrap().as_str(),
            matcher.as_str()
        );
        assert_eq!(args[2], FormatArgument::Named("foo.bar".to_string()));
    }

    #[test]
    fn test_build_matcher_positional() {
        let MessageMatcher { matcher, args, .. } =
            build_matcher(false, "second={2}", SourceLanguage::Rust).unwrap();
        assert_eq!(
            Regex::new(r#"(?s)^second=(.*)$"#).unwrap().as_str(),
            matcher.as_str()
        );
        assert_eq!(args[0], FormatArgument::Positional(2));
    }

    #[test]
    fn test_build_matcher_cpp() {
        let MessageMatcher { matcher, args, .. } =
            build_matcher(false, "they are %d years old", SourceLanguage::Cpp).unwrap();
        assert_eq!(
            Regex::new(r#"(?s)^they are (.*) years old$"#)
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
            Regex::new(r#"(?s)^they are (.*) years old$"#)
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
    fn test_build_matcher_trailing_whitespace() {
        let MessageMatcher { matcher, .. } =
            build_matcher(false, "Headers:\\n{}\\n \\t", SourceLanguage::Kotlin).unwrap();
        assert_eq!(r#"(?s)^Headers:\n(.*?)\s*$"#, matcher.as_str());
        assert!(matcher.is_match("Headers:\nA: b\n"));
        assert!(matcher.is_match("Headers:\nA: b"));

        // An escaped backslash followed by an 'n' is not a newline.
        let MessageMatcher { matcher, .. } =
            build_matcher(false, "path is C:\\\\n", SourceLanguage::Java).unwrap();
        assert_eq!(r#"(?s)^path is C:\\n$"#, matcher.as_str());
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
            (Kotlin, r"\$price\té\b", r"\$price\té\x08"),
            (
                Kotlin,
                r#"\"quoted\" \'c\' \\path"#,
                r#""quoted" 'c' \\path"#,
            ),
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

    fn segments_and_kinds(text: &str, language: SourceLanguage) -> (Vec<String>, Vec<ValueKind>) {
        let MessageMatcher {
            matcher,
            kinds,
            segments,
            ..
        } = build_matcher(false, text, language).unwrap();
        // The segments and capture groups should make up the whole pattern.
        let mut pattern = "(?s)^".to_string();
        for segment in &segments[..segments.len() - 1] {
            pattern.push_str(segment);
            pattern.push_str(ANY_CAPTURE);
        }
        pattern.push_str(segments.last().unwrap());
        pattern.push('$');
        assert_eq!(
            pattern.replace("(.*?)", "(.*)"),
            matcher.as_str().replace("(.*?)", "(.*)")
        );
        (segments, kinds)
    }

    #[test]
    fn test_build_matcher_segments() {
        use ValueKind::*;
        assert_eq!(
            segments_and_kinds("foo (x) %s %5d%c", SourceLanguage::Cpp),
            (
                vec![
                    r"foo \(x\) ".to_string(),
                    " ".to_string(),
                    "".to_string(),
                    "".to_string()
                ],
                vec![Any, Integer, Char]
            )
        );
        assert_eq!(
            segments_and_kinds("no placeholders", SourceLanguage::Rust),
            (vec!["no placeholders".to_string()], vec![])
        );
        // Trailing whitespace is optional.
        assert_eq!(
            segments_and_kinds("a {} b\n", SourceLanguage::Rust),
            (vec!["a ".to_string(), r" b\s*".to_string()], vec![Any])
        );
        assert_eq!(
            segments_and_kinds("a {}\n", SourceLanguage::Rust),
            (vec!["a ".to_string(), r"\s*".to_string()], vec![Any])
        );
        assert_eq!(
            segments_and_kinds("a {:x}\n", SourceLanguage::Rust),
            (vec!["a ".to_string(), r"\s*".to_string()], vec![Hex])
        );
    }

    #[test]
    fn test_build_matcher_percent() {
        let MessageMatcher { matcher, args, .. } =
            build_matcher(false, "100%% done %d", SourceLanguage::Cpp).unwrap();
        assert_eq!(matcher.as_str(), r"(?s)^100% done (.*)$");
        assert_eq!(args, vec![FormatArgument::Placeholder]);

        let MessageMatcher { matcher, args, .. } =
            build_matcher(false, "%s at 50%%", SourceLanguage::Python).unwrap();
        assert_eq!(matcher.as_str(), r"(?s)^(.*) at 50%$");
        assert_eq!(args, vec![FormatArgument::Placeholder]);
    }

    #[test]
    fn test_build_matcher_unprinted_args() {
        // `%n` uses an argument but prints nothing.
        let MessageMatcher { matcher, args, .. } =
            build_matcher(false, "wrote%n %s", SourceLanguage::Cpp).unwrap();
        assert_eq!(matcher.as_str(), r"(?s)^wrote (.*)$");
        assert_eq!(args, vec![FormatArgument::Positional(1)]);

        // A `*` width uses an argument.
        let MessageMatcher { args, .. } =
            build_matcher(false, "%*d items %s", SourceLanguage::Cpp).unwrap();
        assert_eq!(
            args,
            vec![FormatArgument::Positional(1), FormatArgument::Positional(2)]
        );
    }

    #[test]
    fn test_build_matcher_braces() {
        use FormatArgument::*;
        let cases = [
            // Escaped braces in Rust and fmt.
            (
                SourceLanguage::Rust,
                "a {{x}} b {}",
                r"(?s)^a \{x\} b (.*)$",
                vec![Placeholder],
            ),
            (
                SourceLanguage::Rust,
                "{{{}}}",
                r"(?s)^\{(.*)\}$",
                vec![Placeholder],
            ),
            (
                SourceLanguage::Rust,
                "x {{0}} {0}",
                r"(?s)^x \{0\} (.*)$",
                vec![Positional(0)],
            ),
            (
                SourceLanguage::Rust,
                "{}}}",
                r"(?s)^(.*)\}$",
                vec![Placeholder],
            ),
            (
                SourceLanguage::Cpp,
                "map {{{}: {}}}",
                r"(?s)^map \{(.*): (.*)\}$",
                vec![Placeholder, Placeholder],
            ),
            // Other braces in an SLF4J message are literal.
            (
                SourceLanguage::Java,
                r#"json {{"a": {}}}"#,
                r#"(?s)^json \{\{"a": (.*)\}\}$"#,
                vec![Placeholder],
            ),
            (
                SourceLanguage::Kotlin,
                "obj {} {{}}",
                r"(?s)^obj (.*) \{(.*)\}$",
                vec![Placeholder, Placeholder],
            ),
            // java.util.logging's placeholders.
            (
                SourceLanguage::Java,
                "{0} of {1}",
                r"(?s)^(.*) of (.*)$",
                vec![Placeholder, Placeholder],
            ),
        ];
        for (language, text, pattern, expected_args) in cases {
            let MessageMatcher { matcher, args, .. } =
                build_matcher(false, text, language).unwrap();
            assert_eq!(matcher.as_str(), pattern, "{language:?} {text:?}");
            assert_eq!(args, expected_args, "{language:?} {text:?}");
        }
    }
}
