use crate::java_symbols::MessageRef;
use crate::value_kind::{self, SplitOrder, ValueKind, ANY_CAPTURE};
use crate::{pointer_extension, CodeSource, QueryResult, SourceLanguage};
use core::fmt;
use regex::{Captures, Regex};
use serde::{Deserialize, Serialize};
use std::borrow::Cow;
use std::ops::Range;
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
        // An attribute, like thiserror's `#[error("...")]`, or a `throw` or `raise` of an
        // exception is not a logging call.
        if name.starts_with('#') || MessageCategory::is_exception_call(name) {
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
            // Kernel pointer extensions can end in these letters too, like `%pm` for a MAC
            // address or `%pOFn` for a device tree node name, which take an argument.
            let is_pointer = language.is_c_family() && pointer_extension(spec).is_some();
            if language.is_c_family() && !is_pointer && spec.ends_with('m') {
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
            if !is_pointer && spec.ends_with('n') {
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
    /// A logging call, whose level is in `Statement::level`.
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
    /// Only Kotlin is not classified yet, so its statements are `Log`.
    pub(crate) fn classify(src_ref: &Statement, language: SourceLanguage) -> MessageCategory {
        if let Some(category) = Self::from_call(src_ref, language) {
            return category;
        }
        if src_ref.level != LogLevel::Unknown {
            return MessageCategory::Log;
        }
        match language {
            SourceLanguage::Rust => match Self::short_call_name(src_ref) {
                // a level that is not known until runtime, like `log!(lvl, "...")`
                "log" | "event" => MessageCategory::Log,
                _ => MessageCategory::Other,
            },
            SourceLanguage::C | SourceLanguage::Cpp => MessageCategory::Other,
            SourceLanguage::Python => match Self::short_call_name(src_ref) {
                // a level that is not known until runtime, like `logger.log(lvl, "...")`
                "log" => MessageCategory::Log,
                _ => MessageCategory::Other,
            },
            // The other Java calls with a message are methods of a builder, like the `append`
            // in `new StringBuilder().append("...")`.
            SourceLanguage::Java => match Self::short_call_name(src_ref) {
                // a level that is not known until runtime, like `logger.log(lvl, "...")`
                "log" => MessageCategory::Log,
                _ => MessageCategory::Other,
            },
            // The Kotlin query only finds calls on a logger.
            SourceLanguage::Kotlin => MessageCategory::Log,
        }
    }

    /// The category of a call that is known not to be logging, from its name and the function
    /// it is in.
    pub(crate) fn from_call(
        src_ref: &Statement,
        language: SourceLanguage,
    ) -> Option<MessageCategory> {
        let full_name = src_ref.call_name.as_deref().unwrap_or_default();
        match language {
            SourceLanguage::Rust => {}
            SourceLanguage::C | SourceLanguage::Cpp => return Self::from_c_call(full_name),
            SourceLanguage::Java | SourceLanguage::Python => {
                return Self::is_exception_call(full_name).then_some(MessageCategory::Error);
            }
            SourceLanguage::Kotlin => return None,
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

    /// The category of a C or C++ call that is known not to be logging, from its name.
    pub(crate) fn from_c_call(name: &str) -> Option<MessageCategory> {
        if Self::is_c_error_call(name) {
            Some(MessageCategory::Error)
        } else if Self::is_c_format_call(name) {
            Some(MessageCategory::Format)
        } else {
            None
        }
    }

    /// Check if a C or C++ call makes an error with the message, like a C++
    /// `throw std::runtime_error("...")`, which is named `throw std::runtime_error`, GLib's
    /// `g_set_error()`, or the `Err()` of a C++ `Result` type, like lnav's.
    pub(crate) fn is_c_error_call(name: &str) -> bool {
        Self::is_exception_call(name)
            || matches!(name, "g_set_error" | "g_set_error_literal")
            || name.rsplit("::").next() == Some("Err")
    }

    /// Check if a call makes an exception with the message, like a C++ or Java
    /// `throw ...("...")`, which is named `throw ...`, or a Python `raise ...("...")`, which is
    /// named `raise ...`.
    pub(crate) fn is_exception_call(name: &str) -> bool {
        name.starts_with("throw ") || name.starts_with("raise ")
    }

    /// Check if a C or C++ call formats the message into a string, like `snprintf()` or
    /// `fmt::format()`, by the last part of its name.
    pub(crate) fn is_c_format_call(name: &str) -> bool {
        let name = name.rsplit("::").next().unwrap_or(name);
        matches!(
            name,
            "sprintf"
                | "snprintf"
                | "vsprintf"
                | "vsnprintf"
                | "asprintf"
                | "vasprintf"
                | "swprintf"
                | "vswprintf"
                | "g_snprintf"
                | "g_vsnprintf"
                | "g_strdup_printf"
                | "g_strdup_vprintf"
                | "g_string_printf"
                | "g_string_append_printf"
                | "format"
                | "format_to"
                | "StrFormat"
        )
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
    fn short_call_name(src_ref: &Statement) -> &str {
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

/// A step that a message takes from the call that has its text to the statement that prints it,
/// like the `dev_info(&udev->dev, "%s: %s\n", id, string)` in `show_string()` for the
/// `show_string(udev, "Product", udev->product)` call, or the macro
/// `#define acpi_handle_info(handle, fmt, ...) acpi_handle_printk(KERN_INFO, handle, fmt, ...)`.
#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ChainFrame {
    pub source_path: String,
    pub line_number: usize,
    pub column: usize,
    /// The function or macro that the message goes through.
    pub name: String,
    /// What it calls with the message, like `dev_info`.
    pub call_name: String,
    /// The statement, or the definition of the macro.
    pub text: String,
    /// The parameter that the message, or the string in it, is passed in.
    pub parameter: String,
}

/// A call that continues the line started by an earlier statement, like a `pr_cont()` after a
/// `pr_info()` that did not end the line.  See `Statement::join()`.
#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Continuation {
    pub line_number: usize,
    pub end_line_number: usize,
    pub column: usize,
    pub call_name: String,
    pub text: String,
}

/// How the message of a call ends up in a placeholder of a statement in the function it calls,
/// for `Statement::splice()`.
pub(crate) struct Splice<'a> {
    /// The statement in the called function that prints the message.
    pub inner: &'a Statement,
    /// The placeholder of `inner` that prints the message of the call.
    pub placeholder: usize,
    /// The regexes for the text that the macros between the call and the function add before
    /// and after the message, like the `"foo: "` in `pr_debug("foo: " fmt, ...)`.
    pub prefix: String,
    pub suffix: String,
    /// The placeholders of `inner` that print nothing, like the `%s` for a `KERN_INFO` level in
    /// `printk("%sACPI: %s: %pV", level, ...)`, since printk() takes the level out.
    pub empty: Vec<usize>,
    /// The expressions in the call for the placeholders of `inner` whose arguments are
    /// parameters of the function, like `udev->product` for the `string` in
    /// `dev_info(&udev->dev, "%s: %s\n", id, string)`, by placeholder.
    pub caller_exprs: Vec<Option<String>>,
    /// The steps from the call to `inner`.
    pub frames: Vec<ChainFrame>,
}

/// A log statement as it is stored in a `StatementsInFile`.  The things that are the same for
/// every statement in a file, like the path and language, are kept in the file instead.  A
/// `StatementRef` pairs a statement with its file.
#[derive(Debug, Serialize, Deserialize)]
pub struct Statement {
    pub line_no: usize,
    pub end_line_no: usize,
    pub column: usize,
    pub name: String,
    /// The name of the enclosing function qualified by its containers, like namespaces,
    /// classes, and modules.
    pub qualified_name: String,
    /// The start byte of the innermost lexical block containing the call.  Statements with the
    /// same source file and `block_id` are in the same block.
    pub block_id: u32,
    pub text: String,
    pub level: LogLevel,
    pub category: MessageCategory,
    /// The name of the logging function/macro/method that was called, as written in the source,
    /// like `ws_debug`, `logger.info`, or `syslog`.
    pub call_name: Option<String>,
    pub quality: usize,
    pub(crate) args: Vec<FormatArgument>,
    /// The kind of value produced by the expression of each `FormatArgument::Named` in `args`.
    pub(crate) arg_kinds: Vec<ValueKind>,
    pub(crate) vars: Vec<String>,
    /// The kind of value produced by each expression in `vars`.
    pub(crate) var_kinds: Vec<ValueKind>,
    /// The kind of value expected for each placeholder based on its format spec.
    pub(crate) kinds: Vec<ValueKind>,
    /// The regexes in `pattern` for the literal text before, between, and after the
    /// placeholders.
    pub(crate) segments: Vec<String>,
    /// For each placeholder, the regexes for the only values that its argument can produce,
    /// like `colour` and `mono` for `vc->vc_can_do_color ? "colour" : "mono"`, or empty if it
    /// can be anything.  This is empty when no placeholder has choices.
    pub(crate) choices: Vec<Vec<String>>,
    /// For each placeholder, whether it prints its argument as-is, like `%s` without a width or
    /// precision, so the value is one of the argument's choices.  Only needed until the
    /// arguments are known and `resolve_choices()` is called.
    #[serde(skip)]
    plain: Vec<bool>,
    /// The choices for each expression in `vars`, which become `choices` for the placeholders
    /// they are printed by.  See `value_kind::value_choices()`.
    #[serde(skip)]
    pub(crate) var_choices: Vec<Vec<String>>,
    /// For a C or C++ message, the position of the argument that holds it in the call, which is
    /// used to find the parameter that a string passed to a function is bound to.
    pub(crate) arg_position: Option<u32>,
    /// For a statement derived from one in a function that was called with a string for one of
    /// its placeholders, the calls from the outermost one inward.  See
    /// `SourceTree::derive_call_statements()`.
    #[serde(skip)]
    pub call_chain: Vec<ChainFrame>,
    /// For a statement derived from one that starts a line and the calls that continue it,
    /// like `pr_info("Console: switching ")` and the `pr_cont("to %s\n", ...)` after it, the
    /// continuations.  See `Statement::join()`.
    #[serde(skip)]
    pub continuations: Vec<Continuation>,
    /// The regex used to match log messages, built from `segments`.  This, and the rest of the
    /// fields below, are only computed when needed since most statements are never matched.
    #[serde(skip)]
    pattern: OnceLock<Regex>,
    /// `kinds` refined by the argument expressions.
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
    #[serde(skip)]
    choice_matchers: OnceLock<Option<Vec<Option<Regex>>>>,
    /// `pattern` with each run of whitespace in the literal text matching any whitespace, for
    /// text whose whitespace was changed, like a message copied from a GUI that wrapped it.
    /// None if `pattern` already matches the same text, see `relaxed_pattern()`.
    #[serde(skip)]
    relaxed_pattern: OnceLock<Option<Regex>>,
}

struct MessageMatcher {
    /// The source of the regex that matches the messages, which is the same as
    /// `value_kind::pattern_source()` of the segments, so only the tests look at it.  The regex
    /// is only compiled when it is needed, since most statements are never matched.
    #[cfg_attr(not(test), allow(dead_code))]
    matcher: String,
    quality: usize,
    args: Vec<FormatArgument>,
    kinds: Vec<ValueKind>,
    segments: Vec<String>,
    plain: Vec<bool>,
}

impl Statement {
    pub(crate) fn new(code: &CodeSource, result: QueryResult) -> Option<Statement> {
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
            matcher: _,
            mut args,
            quality,
            kinds,
            segments,
            plain,
        }) = build_any_matcher(result.raw, &unquoted, code.info.language)
        {
            let name = result.name;
            let arg_kinds = if result.args.is_empty() {
                vec![ValueKind::Any; args.len()]
            } else {
                let arg_kinds;
                (args, arg_kinds) = result.args.into_iter().unzip();
                arg_kinds
            };
            let mut src_ref = Statement {
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
                pattern: OnceLock::new(),
                args,
                arg_kinds,
                vars: vec![],
                var_kinds: vec![],
                kinds,
                segments,
                choices: vec![],
                plain,
                var_choices: vec![],
                arg_position: result.arg_position.and_then(|pos| u32::try_from(pos).ok()),
                call_chain: vec![],
                continuations: vec![],
                value_kinds: OnceLock::new(),
                segment_matchers: OnceLock::new(),
                lazy_matcher: OnceLock::new(),
                separators: OnceLock::new(),
                non_empty_matcher: OnceLock::new(),
                choice_matchers: OnceLock::new(),
                relaxed_pattern: OnceLock::new(),
            };
            if quality == 0 {
                // A message without literal text matches anything, so it is only kept if it
                // continues a line that an earlier statement started, like `pr_cont(" %s", x)`
                // or `pr_cont("\n")`, see `is_bare_continuation()`.
                if !src_ref.is_continuation() {
                    return None;
                }
                if src_ref.ends_line() {
                    if let Some(last) = src_ref.segments.last_mut() {
                        // The newline is optional, like at the end of any other message.
                        *last = "\\s*".to_string();
                    }
                }
            }
            // Redone by `prune_log_calls()`, which can change the level.
            src_ref.category = MessageCategory::classify(&src_ref, code.info.language);
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
    pub(crate) fn from_message_ref(message_ref: &MessageRef, value: &str) -> Option<Statement> {
        let MessageMatcher {
            matcher: _,
            args,
            quality,
            kinds,
            segments,
            plain: _,
        } = build_matcher(false, value, SourceLanguage::Java)?;
        Some(Statement {
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
            pattern: OnceLock::new(),
            arg_kinds: vec![ValueKind::Any; args.len()],
            args,
            vars: message_ref.vars.clone(),
            var_kinds: message_ref.var_kinds.clone(),
            kinds,
            segments,
            choices: vec![],
            plain: vec![],
            var_choices: vec![],
            arg_position: None,
            call_chain: vec![],
            continuations: vec![],
            value_kinds: OnceLock::new(),
            segment_matchers: OnceLock::new(),
            lazy_matcher: OnceLock::new(),
            separators: OnceLock::new(),
            non_empty_matcher: OnceLock::new(),
            choice_matchers: OnceLock::new(),
            relaxed_pattern: OnceLock::new(),
        })
    }

    /// Fill in `choices` from the choices of the arguments, once they are all known, and
    /// rebuild the pattern if any placeholder has choices.  The literal text of the shortest
    /// choice counts toward the quality, since every match has it.
    pub(crate) fn resolve_choices(&mut self) {
        let plain = std::mem::take(&mut self.plain);
        let var_choices = std::mem::take(&mut self.var_choices);
        if var_choices.iter().all(Vec::is_empty) {
            return;
        }
        let mut placeholder_index = 0;
        let choices: Vec<Vec<String>> = self
            .args
            .iter()
            .enumerate()
            .map(|(index, arg)| {
                let var = match arg {
                    FormatArgument::Named(_) => None,
                    FormatArgument::Positional(pos) => Some(*pos),
                    FormatArgument::Placeholder => {
                        placeholder_index += 1;
                        Some(placeholder_index - 1)
                    }
                };
                match var.and_then(|var| var_choices.get(var)) {
                    Some(choices) if plain.get(index).copied().unwrap_or(false) => choices.clone(),
                    _ => vec![],
                }
            })
            .collect();
        if choices.iter().all(Vec::is_empty) {
            return;
        }
        self.quality += choices
            .iter()
            .filter_map(|choices| choices.iter().map(|c| literal_quality(c)).min())
            .sum::<usize>();
        self.choices = choices;
        self.pattern = OnceLock::new();
        if !is_valid_pattern(&self.pattern_source()) {
            // Too big, maybe, so fall back to the pattern without the choices.
            self.choices.clear();
        }
    }

    /// A statement derived from this one, at the same location and with the same message, but
    /// without the arguments that are only needed while extracting, and with the lazily built
    /// matchers reset.  The callers change what is different, like the segments.
    fn derived(&self) -> Statement {
        Statement {
            line_no: self.line_no,
            end_line_no: self.end_line_no,
            column: self.column,
            name: self.name.clone(),
            qualified_name: self.qualified_name.clone(),
            block_id: self.block_id,
            text: self.text.clone(),
            level: self.level,
            category: self.category,
            call_name: self.call_name.clone(),
            quality: self.quality,
            args: self.args.clone(),
            arg_kinds: self.arg_kinds.clone(),
            vars: vec![],
            var_kinds: vec![],
            kinds: self.kinds.clone(),
            segments: self.segments.clone(),
            choices: self.choices.clone(),
            plain: vec![],
            var_choices: vec![],
            arg_position: None,
            call_chain: self.call_chain.clone(),
            continuations: self.continuations.clone(),
            pattern: OnceLock::new(),
            value_kinds: OnceLock::new(),
            segment_matchers: OnceLock::new(),
            lazy_matcher: OnceLock::new(),
            separators: OnceLock::new(),
            non_empty_matcher: OnceLock::new(),
            choice_matchers: OnceLock::new(),
            relaxed_pattern: OnceLock::new(),
        }
    }

    /// Derive a statement for this call from the statement that prints its message in the
    /// function it calls, by putting this call's message in place of the placeholder that
    /// prints it.  So, the `show_string(udev, "Product", udev->product)` call and
    /// `dev_info(&udev->dev, "%s: %s\n", id, string)` in `show_string()` make
    /// `"Product: %s\n"`, and `acpi_handle_info(handle, "Found %d\n", n)` and the
    /// `printk("%sACPI: %s: %pV", ...)` in `acpi_handle_printk()` make `"ACPI: %s: Found %d\n"`.
    /// That has more literal text than either one, so it is a better match for a line that
    /// came from them.  The location is this call's, since that is where the message was
    /// written, and the steps to the statement that printed it are in `call_chain`.
    pub(crate) fn splice(&self, splice: &Splice) -> Option<Statement> {
        let inner = splice.inner;
        if splice.placeholder >= inner.kinds.len()
            || inner.segments.len() != inner.kinds.len() + 1
            || self.segments.len() != self.kinds.len() + 1
        {
            return None;
        }
        let inner_args: Vec<(&str, ValueKind)> = inner.resolved_args().collect();
        let mut segments = vec![];
        let mut args = vec![];
        let mut arg_kinds = vec![];
        let mut kinds = vec![];
        let mut choices = vec![];
        let choices_of =
            |stmt: &Statement, index: usize| stmt.choices.get(index).cloned().unwrap_or_default();
        let mut current = inner.segments[0].clone();
        for (index, kind) in inner.kinds.iter().enumerate() {
            if index == splice.placeholder {
                current.push_str(&splice.prefix);
                current.push_str(&self.segments[0]);
                for (call_index, (expr, arg_kind)) in self.resolved_args().enumerate() {
                    segments.push(std::mem::take(&mut current));
                    args.push(FormatArgument::Named(expr.to_string()));
                    arg_kinds.push(arg_kind);
                    kinds.push(self.kinds[call_index]);
                    choices.push(choices_of(self, call_index));
                    current = self.segments[call_index + 1].clone();
                }
                current.push_str(&splice.suffix);
            } else if !splice.empty.contains(&index) {
                segments.push(std::mem::take(&mut current));
                let (expr, arg_kind) = inner_args
                    .get(index)
                    .copied()
                    .unwrap_or(("<unknown>", ValueKind::Any));
                let expr = splice
                    .caller_exprs
                    .get(index)
                    .and_then(Option::as_deref)
                    .unwrap_or(expr);
                args.push(FormatArgument::Named(expr.to_string()));
                arg_kinds.push(arg_kind);
                kinds.push(*kind);
                choices.push(choices_of(inner, index));
            }
            current.push_str(&inner.segments[index + 1]);
        }
        segments.push(current);
        if choices.iter().all(Vec::is_empty) {
            choices.clear();
        }
        // The call is the one that logs if it looks like logging, like `acpi_handle_info()`,
        // even when the statement that prints it does not, like a `printk()` with the level in
        // an argument.
        let (level, category) = if self.category == MessageCategory::Log {
            (self.level, self.category)
        } else {
            (inner.level, inner.category)
        };
        Some(Statement {
            level,
            category,
            quality: self.quality
                + inner.quality
                + literal_quality(&splice.prefix)
                + literal_quality(&splice.suffix),
            args,
            arg_kinds,
            kinds,
            segments,
            choices,
            call_chain: splice.frames.clone(),
            continuations: vec![],
            ..self.derived()
        })
    }

    /// Derive a statement for this call with the text that the macros it goes through add
    /// before and after its message, like `"foo: "` for `#define DBG(fmt, ...) pr_debug("foo: " fmt, ...)`.
    pub(crate) fn with_affixes(
        &self,
        prefix: &str,
        suffix: &str,
        frames: Vec<ChainFrame>,
    ) -> Statement {
        let mut segments = self.segments.clone();
        if let Some(first) = segments.first_mut() {
            first.insert_str(0, prefix);
        }
        if let Some(last) = segments.last_mut() {
            last.push_str(suffix);
        }
        let (args, arg_kinds) = self
            .resolved_args()
            .map(|(expr, kind)| (FormatArgument::Named(expr.to_string()), kind))
            .unzip();
        Statement {
            quality: self.quality + literal_quality(prefix) + literal_quality(suffix),
            args,
            arg_kinds,
            segments,
            call_chain: frames,
            ..self.derived()
        }
    }

    /// Derive a statement for the whole line printed by this statement, which starts the line,
    /// and the statements that continue it, like the
    /// `pr_cont("to %s %s %dx%d\n", ...)` after `pr_info("Console: switching ")`.  The
    /// location is this statement's, and the continuations are listed in `continuations`.
    pub(crate) fn join(&self, conts: &[&Statement]) -> Option<Statement> {
        let well_formed = |stmt: &Statement| stmt.segments.len() == stmt.kinds.len() + 1;
        if !well_formed(self) || !conts.iter().all(|cont| well_formed(cont)) {
            return None;
        }
        let mut segments = self.segments.clone();
        let (mut args, mut arg_kinds): (Vec<FormatArgument>, Vec<ValueKind>) = self
            .resolved_args()
            .map(|(expr, kind)| (FormatArgument::Named(expr.to_string()), kind))
            .unzip();
        let mut kinds = self.kinds.clone();
        let choices_of =
            |stmt: &Statement, index: usize| stmt.choices.get(index).cloned().unwrap_or_default();
        let mut choices: Vec<Vec<String>> =
            (0..self.kinds.len()).map(|i| choices_of(self, i)).collect();
        let mut quality = self.quality;
        let mut text = self.text.clone();
        let mut end_line_no = self.end_line_no;
        let mut continuations = vec![];
        for cont in conts {
            let resolved: Vec<(&str, ValueKind)> = cont.resolved_args().collect();
            // The `KERN_CONT` in `printk(KERN_CONT "...")` is a placeholder that prints
            // nothing, since printk() takes the level out.
            let skip = usize::from(
                cont.segments[0].is_empty()
                    && resolved
                        .first()
                        .is_some_and(|(expr, _)| *expr == "KERN_CONT"),
            );
            let last = segments.pop().unwrap_or_default();
            let first = if skip == 1 {
                &cont.segments[1]
            } else {
                &cont.segments[0]
            };
            segments.push(format!("{last}{first}"));
            segments.extend(cont.segments[skip + 1..].iter().cloned());
            for index in skip..cont.kinds.len() {
                let (expr, kind) = resolved
                    .get(index)
                    .copied()
                    .unwrap_or(("<unknown>", ValueKind::Any));
                args.push(FormatArgument::Named(expr.to_string()));
                arg_kinds.push(kind);
                kinds.push(cont.kinds[index]);
                choices.push(choices_of(cont, index));
            }
            quality += cont.quality;
            text.push(' ');
            text.push_str(&cont.text);
            end_line_no = end_line_no.max(cont.end_line_no);
            continuations.push(Continuation {
                line_number: cont.line_no,
                end_line_number: cont.end_line_no,
                column: cont.column,
                call_name: cont.call_name.clone().unwrap_or_default(),
                text: cont.text.clone(),
            });
        }
        if choices.iter().all(Vec::is_empty) {
            choices.clear();
        }
        let joined = Statement {
            end_line_no,
            text,
            quality,
            args,
            arg_kinds,
            kinds,
            segments,
            choices,
            continuations,
            ..self.derived()
        };
        is_valid_pattern(&joined.pattern_source()).then_some(joined)
    }

    /// Check if this statement continues the line of an earlier one, like `pr_cont(...)` or
    /// `printk(KERN_CONT ...)` in the Linux kernel.
    pub(crate) fn is_continuation(&self) -> bool {
        match self.call_name.as_deref() {
            Some("pr_cont") => true,
            Some("printk") => self.text.starts_with("KERN_CONT"),
            _ => false,
        }
    }

    /// Check if this statement continues the line of an earlier one without any literal text
    /// of its own, like `pr_cont(" %s", x)`, `pr_cont("\n")`, or `printk(KERN_CONT "\n")`.
    /// These would match any log message, so they are not matched on their own, they are only
    /// joined to the line they continue in `join_continued_lines()`.
    pub(crate) fn is_bare_continuation(&self) -> bool {
        self.quality == 0 && self.is_continuation()
    }

    /// Check if this statement is a Linux kernel print that starts a line, like `pr_info(...)`
    /// or `printk(KERN_INFO ...)`, which a later continuation can add to if the line is not
    /// ended.
    pub(crate) fn is_kernel_print(&self) -> bool {
        !self.is_continuation() && self.call_name.as_deref().is_some_and(is_kernel_print)
    }

    /// Check if the message ends with a newline in the source, which ends the line.
    pub(crate) fn ends_line(&self) -> bool {
        self.text
            .trim_end()
            .strip_suffix('"')
            .is_some_and(|text| text.ends_with("\\n"))
    }

    /// The text of the placeholders in the statement's string, like `["%s", "%pV"]`, if it is a
    /// single C or C++ string literal.
    pub(crate) fn c_placeholder_specs(&self) -> Option<Vec<&str>> {
        let language = SourceLanguage::C;
        let mut counter = ArgCounter::default();
        let specs: Vec<&str> = language
            .get_placeholder_regex()
            .captures_iter(&self.text)
            .filter_map(|cap| match counter.substitution(language, &cap) {
                Substitution::Value(_) => Some(cap.get(0).unwrap().as_str()),
                _ => None,
            })
            .collect();
        (specs.len() == self.kinds.len()).then_some(specs)
    }

    /// The arguments for the placeholders in the call that this statement's string is passed
    /// to, after the string, like `udev->product` for `show_string(udev, "Product", udev->product)`.
    pub(crate) fn trailing_args(&self) -> &[String] {
        &self.vars
    }

    pub fn captures<'a>(&self, line: &'a str) -> Option<Captures<'a>> {
        self.pattern().captures(line)
    }

    /// The regex used to match log messages to this statement.  It is compiled the first time
    /// it is needed, like after the statement is loaded from the cache.
    pub fn pattern(&self) -> &Regex {
        self.pattern.get_or_init(|| {
            // The pattern was checked when the statement was extracted, but it could still be
            // too big to compile, and then the statement cannot match anything.
            Regex::new(&self.pattern_source())
                .unwrap_or_else(|_| Regex::new(r"[^\s\S]").expect("the regex is valid"))
        })
    }

    /// `pattern()` with each run of whitespace in the literal text, like the two spaces after a
    /// sentence, matching any run of whitespace, for text whose whitespace was collapsed by
    /// `collapse_whitespace()`.  It is compiled the first time it is needed.  Most statements
    /// only have single spaces, which already match collapsed text, so `pattern()` is used for
    /// those rather than compiling another regex for every statement.
    pub fn relaxed_pattern(&self) -> &Regex {
        self.relaxed_pattern
            .get_or_init(|| {
                let segments: Vec<String> = self
                    .segments
                    .iter()
                    .map(|segment| relax_whitespace(segment))
                    .collect();
                // A single space became a `\s+`, which matches the same collapsed text.
                let same = std::iter::zip(&segments, &self.segments)
                    .all(|(relaxed, segment)| *relaxed == segment.replace(' ', "\\s+"));
                if same {
                    return None;
                }
                Regex::new(&value_kind::pattern_source(&segments, &self.choices)).ok()
            })
            .as_ref()
            .unwrap_or_else(|| self.pattern())
    }

    /// The source of `pattern()`, which does not need to compile it.  It is borrowed from the
    /// regex if that was already compiled.
    pub fn pattern_source(&self) -> Cow<'_, str> {
        match self.pattern.get() {
            Some(pattern) => Cow::Borrowed(pattern.as_str()),
            None => Cow::Owned(value_kind::pattern_source(&self.segments, &self.choices)),
        }
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

    /// Anchored regexes for the choices of each placeholder, see `choices`.
    pub(crate) fn choice_matchers(&self) -> Option<&[Option<Regex>]> {
        self.choice_matchers
            .get_or_init(|| value_kind::compile_choices(&self.choices))
            .as_deref()
    }

    /// A matcher like `pattern`, but with lazy captures.
    pub(crate) fn lazy_matcher(&self) -> Option<&Regex> {
        self.lazy_matcher
            .get_or_init(|| value_kind::compile_matcher(&self.segments, &self.choices, "(.*?)"))
            .as_ref()
    }

    /// Unanchored regexes for the literal text after each placeholder.
    pub(crate) fn separators(&self) -> Option<&[Regex]> {
        self.separators
            .get_or_init(|| value_kind::compile_separators(&self.segments))
            .as_deref()
    }

    /// Check if the values that `pattern`, this statement's pattern or `relaxed_pattern()`,
    /// captures from `text` look like the kinds of values in the format string, like a number
    /// for `%d`.  The kinds guessed from the argument expressions are not used, since they are
    /// only guesses.  Returns true if `text` does not match, since that is not the question.
    pub(crate) fn values_fit_kinds(&self, pattern: &Regex, text: &str) -> bool {
        if self.kinds.iter().all(|kind| *kind == ValueKind::Any) {
            return true;
        }
        let Some(captures) = pattern.captures(text) else {
            return true;
        };
        let values: Vec<Range<usize>> = captures
            .iter()
            .skip(1)
            .map(|value| value.map_or(0..0, |value| value.range()))
            .collect();
        if values.len() != self.kinds.len() {
            return true;
        }
        let fits = |values: &[Range<usize>]| {
            std::iter::zip(values, &self.kinds).all(|(range, kind)| {
                *kind == ValueKind::Any || kind.value_range(&text[range.clone()]).is_some()
            })
        };
        if fits(&values) {
            return true;
        }
        // The greedy captures give everything to the first of two placeholders that are next
        // to each other, so another split could fit.  The segment matchers need the exact
        // whitespace, so this only works for text that matches the pattern.
        self.pattern().is_match(text)
            && self.segment_matchers().is_some_and(|segments| {
                let choices = self.choice_matchers().unwrap_or_default();
                value_kind::split_values(
                    text,
                    segments,
                    &self.kinds,
                    choices,
                    SplitOrder::LongestFirst,
                )
                .is_some()
            })
    }

    /// Check if `body` matches this statement with a non-empty value for every placeholder.
    pub(crate) fn matches_without_empty_values(&self, body: &str) -> bool {
        if self.kinds.is_empty() {
            return self.pattern().is_match(body);
        }
        self.non_empty_matcher
            .get_or_init(|| value_kind::compile_matcher(&self.segments, &self.choices, "(.+)"))
            .as_ref()
            .is_some_and(|matcher| matcher.is_match(body))
    }
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[Line: {}, Col: {}] source `{}` name `{}` vars={:?}",
            self.line_no, self.column, self.text, self.name, self.vars
        )
    }
}

impl PartialEq for Statement {
    fn eq(&self, other: &Self) -> bool {
        self.line_no == other.line_no
            && self.column == other.column
            && self.name == other.name
            && self.text == other.text
            && self.vars == other.vars
    }
}

fn build_matcher(raw: bool, text: &str, language: SourceLanguage) -> Option<MessageMatcher> {
    build_any_matcher(raw, text, language).filter(|matcher| matcher.quality > 0)
}

/// Build the matcher for a message, even one without any literal text, like `"%s"` or `"\n"`.
fn build_any_matcher(raw: bool, text: &str, language: SourceLanguage) -> Option<MessageMatcher> {
    let mut args = Vec::new();
    let mut kinds = Vec::new();
    let mut segments = Vec::new();
    let mut plain = Vec::new();
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
        quality += literal_quality(&subtext);
        pattern.push_str(subtext.as_str());
        segments.push(subtext);
        // The kind of value is only used to split the values, so a value that does not look
        // like the format spec, such as a date for `{:%Y-%m-%d}`, still matches.
        pattern.push_str(ANY_CAPTURE);
        last_group_end = pattern.len();
        kinds.push(ValueKind::from_placeholder(language, placeholder.as_str()));
        plain.push(matches!(placeholder.as_str(), "%s" | "{}"));
        args.push(arg);
    }
    let mut subtext = pending;
    subtext.push_str(&literal_to_regex(raw, language, &text[last_end..]));
    quality += literal_quality(&subtext);
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
    debug_assert_eq!(pattern, value_kind::pattern_source(&segments, &[]));
    // A pattern that does not parse is not usable, so skip the log statement.
    is_valid_pattern(&pattern).then_some(MessageMatcher {
        matcher: pattern,
        quality,
        args,
        kinds,
        segments,
        plain,
    })
}

/// Check if a call is one of the Linux kernel's prints, which can be continued by a
/// `pr_cont()`, like `printk`, `pr_info`, or `dev_warn`.
fn is_kernel_print(call_name: &str) -> bool {
    call_name == "printk"
        || ["pr_", "dev_", "netdev_"].iter().any(|prefix| {
            call_name
                .strip_prefix(prefix)
                .is_some_and(|level| LogLevel::from_name(level).is_some())
        })
}

/// Check if a regex for a message parses, which is much cheaper than compiling it.
fn is_valid_pattern(pattern: &str) -> bool {
    regex_syntax::Parser::new().parse(pattern).is_ok()
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

/// Replace each run of whitespace in a regex built by `push_regex_literal()`, like a segment of a
/// matcher, with `\s+`, so it matches text that was wrapped or had its whitespace collapsed.  A
/// run that is only the optional trailing whitespace added by `build_matcher()` stays optional.
fn relax_whitespace(regex: &str) -> String {
    let mut retval = String::new();
    // Whether there is a run of whitespace that has not been added yet, and whether it is all
    // optional.
    let mut run: Option<bool> = None;
    let mut chars = regex.chars().peekable();
    while let Some(c) = chars.next() {
        let (space, optional, token) = match c {
            '\\' => match chars.next() {
                Some('n' | 'r' | 't') => (true, false, String::new()),
                Some('s') => {
                    chars.next_if_eq(&'*');
                    (true, true, String::new())
                }
                Some(next) => (false, false, format!("\\{next}")),
                None => (false, false, "\\".to_string()),
            },
            c if c.is_whitespace() => (true, false, String::new()),
            c => (false, false, c.to_string()),
        };
        if space {
            run = Some(run.unwrap_or(true) && optional);
            continue;
        }
        if let Some(optional) = run.take() {
            retval.push_str(if optional { "\\s*" } else { "\\s+" });
        }
        retval.push_str(&token);
    }
    if let Some(optional) = run {
        retval.push_str(if optional { "\\s*" } else { "\\s+" });
    }
    retval
}

/// The literal text matched by a regex built by `push_regex_literal()`, like a segment of a
/// matcher.  An unescaped `.`, which `literal_to_regex()` uses for a character that it could not
/// decode, matches anything, so the text is split there and the pieces are returned.
pub(crate) fn regex_literal_pieces(regex: &str) -> Vec<String> {
    let mut pieces = vec![];
    let mut piece = String::new();
    let mut chars = regex.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '\\' => match chars.next() {
                Some('n') => piece.push('\n'),
                Some('r') => piece.push('\r'),
                Some('t') => piece.push('\t'),
                // The optional trailing whitespace added by `build_matcher()`, which is not
                // literal text.  A literal `s` is never escaped by `push_regex_literal()`.
                Some('s') => {
                    chars.next_if_eq(&'*');
                    pieces.push(std::mem::take(&mut piece));
                }
                Some('x') => {
                    let hex: String = chars.by_ref().take(2).collect();
                    piece.extend(u32::from_str_radix(&hex, 16).ok().and_then(char::from_u32));
                }
                Some(c) => piece.push(c),
                None => {}
            },
            '.' => pieces.push(std::mem::take(&mut piece)),
            c => piece.push(c),
        }
    }
    pieces.push(piece);
    pieces.retain(|piece| !piece.is_empty());
    pieces
}

/// The amount of literal text matched by a regex built by `push_regex_literal()`, not counting
/// whitespace.  The characters are counted, not their escapes in the
/// regex, so `"a.b"` is 3 and the newline at the end of `"%s\n"` does not count.
fn literal_quality(regex: &str) -> usize {
    regex_literal_pieces(regex)
        .iter()
        .flat_map(|piece| piece.chars())
        .filter(|c| !c.is_whitespace())
        .count()
}

/// The names of the parameters in the signature of a C or C++ function, which is how the
/// `name` of a statement is written for those languages, like `["udev", "id", "string"]` for
/// `show_string(struct usb_device *udev, char *id, char *string)`.  A parameter without a
/// name, like the `int` in `f(int)`, is an empty string so the positions still line up.
pub(crate) fn c_parameter_names(signature: &str) -> Vec<String> {
    let Some(open) = signature.find('(') else {
        return vec![];
    };
    let mut params = vec![];
    let mut depth = 0;
    let mut start = open + 1;
    for (offset, c) in signature[open..].char_indices() {
        let pos = open + offset;
        match c {
            '(' | '[' | '<' => depth += 1,
            ')' | ']' | '>' => {
                depth -= 1;
                if depth == 0 {
                    params.push(&signature[start..pos]);
                    break;
                }
            }
            ',' if depth == 1 => {
                params.push(&signature[start..pos]);
                start = pos + 1;
            }
            _ => {}
        }
    }
    if let [param] = params[..] {
        if matches!(param.trim(), "" | "void") {
            return vec![];
        }
    }
    params
        .into_iter()
        .map(|param| {
            // Leave out a C++ default value and any array dimensions.
            let param = param.split('=').next().unwrap_or_default();
            let param = param.split('[').next().unwrap_or_default().trim_end();
            let words = param
                .split(|c: char| !(c.is_alphanumeric() || c == '_'))
                .filter(|word| !word.is_empty())
                .count();
            let name_start = param
                .rfind(|c: char| !(c.is_alphanumeric() || c == '_'))
                .map_or(0, |pos| pos + 1);
            let name = &param[name_start..];
            // A single word is the type of a parameter without a name.
            if words < 2 || name.is_empty() || name.starts_with(|c: char| c.is_ascii_digit()) {
                String::new()
            } else {
                name.to_string()
            }
        })
        .collect()
}

/// Check if the signature of a C or C++ function takes a variable number of arguments, like
/// `acpi_handle_printk(const char *level, acpi_handle handle, const char *fmt, ...)`.
pub(crate) fn c_is_variadic(signature: &str) -> bool {
    signature
        .trim_end()
        .strip_suffix(')')
        .is_some_and(|params| params.trim_end().ends_with("..."))
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
pub(crate) fn literal_to_regex(raw: bool, language: SourceLanguage, segment: &str) -> String {
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
    use super::{c_parameter_names, push_regex_literal, regex_literal_pieces, relax_whitespace};

    #[test]
    fn test_relax_whitespace() {
        assert_eq!(relax_whitespace(r"a\.  b c"), r"a\.\s+b\s+c");
        assert_eq!(relax_whitespace(r"a \n\tb"), r"a\s+b");
        // The optional trailing whitespace stays optional, unless there is other whitespace.
        assert_eq!(relax_whitespace(r"done\s*"), r"done\s*");
        assert_eq!(relax_whitespace(r"done \s*"), r"done\s+");
        // An escaped backslash is not the start of an escape.
        assert_eq!(relax_whitespace(r"a\\n b"), r"a\\n\s+b");
    }

    #[test]
    fn test_c_parameter_names() {
        assert_eq!(
            c_parameter_names("show_string(struct usb_device *udev, char *id, char *string)"),
            vec!["udev", "id", "string"]
        );
        assert_eq!(c_parameter_names("f(void)"), Vec::<String>::new());
        assert_eq!(c_parameter_names("f()"), Vec::<String>::new());
        // A parameter without a name keeps the positions of the ones after it.
        assert_eq!(
            c_parameter_names("f(int, const char *msg)"),
            vec!["", "msg"]
        );
        assert_eq!(
            c_parameter_names("*lookup(char name[16], void (*cb)(int x), ...)"),
            vec!["name", "", ""]
        );
        assert_eq!(
            c_parameter_names("Foo::log(const std::map<int, int> &m, int level = 3)"),
            vec!["m", "level"]
        );
    }

    #[test]
    fn test_regex_literal_pieces() {
        let text = "a.b (c) [d] {e} $f^ g|h *+? \\ \n\t\x01 end";
        let mut regex = String::new();
        for c in text.chars() {
            push_regex_literal(&mut regex, c);
        }
        assert_eq!(regex_literal_pieces(&regex), vec![text.to_string()]);
        // An unescaped `.` is a character that could not be decoded.
        assert_eq!(regex_literal_pieces(r"abc.def\.g"), vec!["abc", "def.g"]);
    }

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
        // The escaped newline is not literal text.
        assert!(build_matcher(false, r"%s\n", SourceLanguage::C).is_none());
    }

    #[test]
    fn test_build_matcher_quality() {
        // The quality is the amount of literal text, not the length of its escaped regex.
        let quality = |text: &str| {
            build_matcher(false, text, SourceLanguage::C)
                .unwrap()
                .quality
        };
        assert_eq!(quality("a.b"), 3);
        assert_eq!(quality(r"%s %d.%d.%d\n"), 2);
        assert_eq!(quality(r"%s [%s]\n"), 2);
        assert_eq!(quality(r"x\ty\n"), 2);
        assert_eq!(quality(r"\b%c"), 1);
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
        assert!(Regex::new(&matcher).unwrap().is_match("Headers:\nA: b\n"));
        assert!(Regex::new(&matcher).unwrap().is_match("Headers:\nA: b"));

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
        assert!(!Regex::new(&matcher).unwrap().is_match("zqx1 vwk2 jjq3"));
        assert!(Regex::new(&matcher).unwrap().is_match("\x08/"));
    }

    #[test]
    fn test_build_matcher_rust_unicode_escape() {
        let MessageMatcher { matcher, .. } =
            build_matcher(false, r"bullet \u{2022} {}", SourceLanguage::Rust).unwrap();
        assert!(Regex::new(&matcher).unwrap().is_match("bullet • 42"));
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
    fn test_build_matcher_kernel_pointer_extensions() {
        // The letters after `%p` are part of the conversion, not literal text.
        let MessageMatcher { matcher, args, .. } =
            build_matcher(false, "root bus resource %pR%s\n", SourceLanguage::C).unwrap();
        assert_eq!(matcher.as_str(), r"(?s)^root bus resource (.*)(.*?)\s*$");
        assert_eq!(
            args,
            vec![FormatArgument::Placeholder, FormatArgument::Placeholder]
        );
        assert!(Regex::new(&matcher)
            .unwrap()
            .is_match("root bus resource [io  0x0000-0x0cf7 window]"));

        // `%pm` and `%pOFn` take an argument, unlike glibc's `%m` and `%n`.
        let MessageMatcher { matcher, args, .. } =
            build_matcher(false, "mac %pm node %pOFn id %d", SourceLanguage::C).unwrap();
        assert_eq!(matcher.as_str(), r"(?s)^mac (.*) node (.*) id (.*)$");
        assert_eq!(
            args,
            vec![
                FormatArgument::Placeholder,
                FormatArgument::Placeholder,
                FormatArgument::Placeholder
            ]
        );

        // `%*ph` takes the length from an argument before the buffer.
        let MessageMatcher { args, .. } =
            build_matcher(false, "bytes %*ph", SourceLanguage::C).unwrap();
        assert_eq!(args, vec![FormatArgument::Positional(1)]);
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
