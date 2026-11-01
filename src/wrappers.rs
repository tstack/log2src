//! C and C++ macros that pass a message through to another call, like
//! `#define ohci_dbg(ohci, fmt, args...) dev_dbg(ohci_to_hcd(ohci)->self.controller, fmt, ## args)`
//! or `#define acpi_handle_info(handle, fmt, ...) acpi_handle_printk(KERN_INFO, handle, fmt, ##__VA_ARGS__)`.
//! They are followed from a call site to find the function that prints the message, which can
//! add text of its own, so the message can be matched to the call site with that text.

use crate::message_source::collapse_whitespace;
use crate::source_query::is_identifier;
use crate::source_ref::literal_to_regex;
use crate::value_kind::is_balanced;
use crate::SourceLanguage;
use serde::{Deserialize, Serialize};

/// A function-like macro whose definition is a single call or some text around a parameter.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct MacroWrapper {
    pub name: String,
    pub line_no: usize,
    pub column: usize,
    /// The definition on one line, without the line continuations.
    pub text: String,
    /// The names of the parameters.  A variadic parameter, like `args...` or `...`, is not
    /// included since it cannot hold the message.
    pub params: Vec<String>,
    pub body: MacroBody,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum MacroBody {
    /// A call, like the `dev_dbg(..., fmt, ## args)` of `ohci_dbg`.
    Call {
        /// The name of the macro or function that is called.
        callee: String,
        /// The text of the arguments of the call.
        args: Vec<String>,
    },
    /// String literals and a parameter, like the `"ACPI: " fmt` of
    /// `#define pr_fmt(fmt) "ACPI: " fmt`, which is applied to a message by another macro.
    Text(String),
    /// Another name for a macro, like the `pr_fmt` of `#define dev_fmt pr_fmt`.
    Alias(String),
}

/// Pieces of the C code for an argument that a message is passed in.
#[derive(Debug, PartialEq)]
enum Piece<'a> {
    /// The regex for a string literal.
    Literal(String),
    Ident(&'a str),
    /// A macro applied to the pieces in its parentheses, like `dev_fmt(fmt)`.
    Apply(&'a str, Vec<Piece<'a>>),
}

/// Finds the text macro with a name, like `pr_fmt`, for `MacroWrapper::forward()`.
pub type MacroLookup<'a, 'm> = dyn Fn(&str) -> Option<(&'m str, &'m MacroWrapper)> + 'a;

/// A text macro that added text to a message, and the path of the file it is defined in.
pub type Applied<'m> = (&'m str, &'m MacroWrapper);

/// Where an argument of a call to a macro ends up in the call that the macro makes.
#[derive(Debug, PartialEq)]
pub struct Forward {
    /// The position of the argument in the call made by the macro.
    pub position: usize,
    /// The regex for the string literals that the macro puts in front of the argument, like
    /// the `"foo: "` in `pr_debug("foo: " fmt, ##__VA_ARGS__)`.
    pub prefix: String,
    /// The regex for the string literals that the macro puts after the argument.
    pub suffix: String,
}

/// The most text macros to apply to an argument, which stops a runaway one, like
/// `#define pr_fmt(fmt) pr_fmt(fmt)`.
const MAX_APPLY_DEPTH: usize = 4;

impl MacroWrapper {
    /// Parse the parts of a `#define`, like `ohci_dbg`, `(ohci, fmt, args...)`, and
    /// `dev_dbg(ohci_to_hcd(ohci)->self.controller, fmt, ## args)`.  Only a definition that is a
    /// single call, optionally in a `do { ... } while (0)`, is a wrapper.
    pub fn parse(
        name: &str,
        params: &str,
        value: &str,
        line_no: usize,
        column: usize,
    ) -> Option<MacroWrapper> {
        let value = value.replace("\\\r\n", " ").replace("\\\n", " ");
        let value = collapse_whitespace(&value);
        let params_text = params.trim().strip_prefix('(')?.strip_suffix(')')?;
        let params: Vec<String> = split_args(params_text)
            .into_iter()
            .map(|param| param.trim().to_string())
            .filter(|param| !param.ends_with("..."))
            .collect();
        if params.iter().any(|param| !is_identifier(param)) {
            return None;
        }
        let mut body = value.trim();
        if let Some(inner) = body
            .strip_prefix("do")
            .map(str::trim_start)
            .and_then(|rest| rest.strip_prefix('{'))
            .and_then(|rest| {
                let rest = rest.trim_end();
                let rest = rest.strip_suffix(';').unwrap_or(rest).trim_end();
                rest.strip_suffix("while (0)")
                    .or_else(|| rest.strip_suffix("while(0)"))
            })
            .and_then(|rest| rest.trim_end().strip_suffix('}'))
        {
            body = inner.trim();
        }
        let body = body.strip_suffix(';').unwrap_or(body).trim_end();
        let text = format!(
            "#define {}{} {}",
            name.trim(),
            params_text_with_parens(params_text),
            value.trim()
        );
        // A single call, like `printk(KERN_DEBUG "drv: " fmt)`, is a call to follow, but it can
        // also be used as text, like `#define dev_fmt(fmt) pr_fmt(fmt)`, see `text_pieces()`.
        let is_text = pieces(body).is_some_and(|pieces| {
            !pieces.is_empty() && !matches!(pieces.as_slice(), [Piece::Apply(..)])
        });
        if params.len() == 1 && is_text {
            return Some(MacroWrapper {
                name: name.trim().to_string(),
                line_no,
                column,
                text,
                params,
                body: MacroBody::Text(body.to_string()),
            });
        }
        let open = body.find('(')?;
        let callee = body[..open].trim();
        if !is_identifier(callee) || !body.ends_with(')') {
            return None;
        }
        let inner = &body[open + 1..body.len() - 1];
        // The parentheses must be the ones of a single call, not `a(x) + b(y)`.
        if !is_balanced(inner) {
            return None;
        }
        let args = split_args(inner)
            .into_iter()
            .map(|arg| arg.trim().to_string())
            .collect();
        Some(MacroWrapper {
            name: name.trim().to_string(),
            line_no,
            column,
            text,
            params,
            body: MacroBody::Call {
                callee: callee.to_string(),
                args,
            },
        })
    }

    /// Parse an object-like `#define` that is another name for a macro, like
    /// `#define dev_fmt pr_fmt`.
    pub fn parse_alias(
        name: &str,
        value: &str,
        line_no: usize,
        column: usize,
    ) -> Option<MacroWrapper> {
        let (name, value) = (name.trim(), value.trim());
        (is_identifier(name) && is_identifier(value) && name != value).then(|| MacroWrapper {
            name: name.to_string(),
            line_no,
            column,
            text: format!("#define {name} {value}"),
            params: vec![],
            body: MacroBody::Alias(value.to_string()),
        })
    }

    /// The name of the macro or function that this macro calls, if it is a call.
    pub fn callee(&self) -> Option<&str> {
        match &self.body {
            MacroBody::Call { callee, .. } => Some(callee),
            MacroBody::Text(_) | MacroBody::Alias(_) => None,
        }
    }

    /// Check if this macro can be applied to a message as text, like `pr_fmt`, see
    /// `text_pieces()`.
    pub fn is_text(&self) -> bool {
        self.text_pieces().is_some()
    }

    /// The pieces of the text that this macro puts in place of a call to it, if it has one
    /// parameter and is text around it, like `"ACPI: " fmt`, or a single call with one
    /// argument, like the `pr_fmt(fmt)` of `#define dev_fmt(fmt) pr_fmt(fmt)`.
    fn text_pieces(&self) -> Option<Vec<Piece<'_>>> {
        if self.params.len() != 1 {
            return None;
        }
        match &self.body {
            MacroBody::Text(text) => pieces(text),
            MacroBody::Call { callee, args } if args.len() == 1 => {
                Some(vec![Piece::Apply(callee, pieces(&args[0])?)])
            }
            MacroBody::Call { .. } | MacroBody::Alias(_) => None,
        }
    }

    /// Where the argument at `position` of a call to this macro goes in the call it makes.
    /// The argument has to be passed as is, or with string literals around it, like
    /// `"foo: " fmt`, or in text macros, like `dev_fmt(fmt)`, which are found with `lookup`,
    /// since anything else would change the message in an unknown way.  A Linux kernel log
    /// level, like the `KERN_INFO` in `printk(KERN_INFO pr_fmt(fmt), ...)`, adds nothing,
    /// since printk() takes it out.  The text macros that added text are added to `applied`.
    pub fn forward<'m>(
        &self,
        position: usize,
        lookup: &MacroLookup<'_, 'm>,
        applied: &mut Vec<Applied<'m>>,
    ) -> Option<Forward> {
        let MacroBody::Call { args, .. } = &self.body else {
            return None;
        };
        let param = self.params.get(position)?;
        args.iter().enumerate().find_map(|(index, arg)| {
            let mut found = vec![];
            let (prefix, suffix) = around(&pieces(arg)?, param, lookup, &mut found, 0)?;
            applied.extend(found);
            Some(Forward {
                position: index,
                prefix,
                suffix,
            })
        })
    }

    /// The text of the argument at `position` in the call that the macro makes, if it does not
    /// use any of the macro's parameters, like the `KERN_INFO` in
    /// `acpi_handle_printk(KERN_INFO, handle, fmt, ##__VA_ARGS__)`.
    pub fn constant_arg(&self, position: usize) -> Option<&str> {
        let MacroBody::Call { args, .. } = &self.body else {
            return None;
        };
        let arg = args.get(position)?;
        let uses_param = tokens(arg)
            .iter()
            .any(|token| self.params.iter().any(|param| param == token));
        (!uses_param).then_some(arg.as_str())
    }
}

/// Find the `#define`s in C or C++ source that are wrappers, either function-like macros, like
/// `#define pr_fmt(fmt) "ACPI: " fmt`, or another name for a macro, like
/// `#define dev_fmt pr_fmt`.  The lines are scanned instead of parsed, joining the ones that
/// end in a line continuation and leaving out comments, even ones over several lines, and the
/// code in an `#if 0`.
pub fn scan_defines(source: &str) -> Vec<MacroWrapper> {
    let mut retval = vec![];
    let source = blank_comments(source);
    let lines: Vec<&str> = source.lines().collect();
    let mut conditionals = Conditionals::default();
    let mut index = 0;
    while index < lines.len() {
        let line_no = index + 1;
        let mut text = lines[index].to_string();
        while text.trim_end().ends_with('\\') && index + 1 < lines.len() {
            let trimmed = text.trim_end();
            text = format!("{} {}", &trimmed[..trimmed.len() - 1], lines[index + 1]);
            index += 1;
        }
        index += 1;
        let Some(directive) = text.trim_start().strip_prefix('#') else {
            continue;
        };
        let directive = directive.trim_start();
        let keyword_len = directive
            .find(|c: char| !c.is_ascii_alphabetic())
            .unwrap_or(directive.len());
        let (keyword, rest) = directive.split_at(keyword_len);
        if conditionals.update(keyword, rest.trim()) || conditionals.is_disabled() {
            continue;
        }
        if keyword != "define" || !rest.starts_with(char::is_whitespace) {
            continue;
        }
        let column = text.len() - text.trim_start().len();
        let rest = rest.trim_start();
        let name_len = rest
            .find(|c: char| !(c.is_alphanumeric() || c == '_'))
            .unwrap_or(rest.len());
        let (name, after) = rest.split_at(name_len);
        if let Some(params_and_value) = after.strip_prefix('(') {
            // A function-like macro has the `(` right after the name.
            let Some(close) = params_and_value.find(')') else {
                continue;
            };
            let params = format!("({})", &params_and_value[..close]);
            let value = &params_and_value[close + 1..];
            retval.extend(MacroWrapper::parse(name, &params, value, line_no, column));
        } else {
            retval.extend(MacroWrapper::parse_alias(name, after, line_no, column));
        }
    }
    retval
}

/// The `#if`s that the scan of a file is in, to leave out the code in an `#if 0`, which is
/// often old code, or the `#else` of an `#if 1`.  Any other condition could be true or false,
/// so both branches are scanned.
#[derive(Default)]
struct Conditionals {
    /// For each `#if`, whether the branch that the scan is in is disabled.
    stack: Vec<Branch>,
}

#[derive(Clone, Copy)]
struct Branch {
    /// The value of the condition of the `#if`, if it is a constant.
    constant: Option<bool>,
    /// Whether the scan is past the `#if` branch, in an `#elif` or `#else`.
    past_if: bool,
}

impl Conditionals {
    /// Track a preprocessor directive, returning whether it was a conditional.
    fn update(&mut self, keyword: &str, rest: &str) -> bool {
        match keyword {
            "if" => {
                let constant = match rest {
                    "0" => Some(false),
                    "1" => Some(true),
                    _ => None,
                };
                self.stack.push(Branch {
                    constant,
                    past_if: false,
                });
            }
            "ifdef" | "ifndef" => self.stack.push(Branch {
                constant: None,
                past_if: false,
            }),
            "elif" | "elifdef" | "elifndef" | "else" => {
                if let Some(branch) = self.stack.last_mut() {
                    branch.past_if = true;
                }
            }
            "endif" => {
                self.stack.pop();
            }
            _ => return false,
        }
        true
    }

    fn is_disabled(&self) -> bool {
        self.stack.iter().any(|branch| match branch.constant {
            // An `#elif` after an `#if 0` could be true.
            Some(false) => !branch.past_if,
            Some(true) => branch.past_if,
            None => false,
        })
    }
}

/// Replace the C comments in some code with spaces, outside of string and character literals,
/// keeping the newlines so that the lines stay where they are.
fn blank_comments(code: &str) -> String {
    let mut retval = String::with_capacity(code.len());
    let mut chars = code.chars().peekable();
    let mut quote = None;
    while let Some(c) = chars.next() {
        if let Some(q) = quote {
            retval.push(c);
            if c == '\\' {
                retval.extend(chars.next());
            } else if c == q || c == '\n' {
                quote = None;
            }
            continue;
        }
        match (c, chars.peek()) {
            ('/', Some('/')) => {
                retval.push(' ');
                while chars.next_if(|c| *c != '\n').is_some() {}
            }
            ('/', Some('*')) => {
                chars.next();
                retval.push(' ');
                let mut prev = ' ';
                for c in chars.by_ref() {
                    if prev == '*' && c == '/' {
                        break;
                    }
                    if c == '\n' {
                        retval.push('\n');
                    }
                    prev = c;
                }
            }
            ('"' | '\'', _) => {
                quote = Some(c);
                retval.push(c);
            }
            _ => retval.push(c),
        }
    }
    retval
}

fn params_text_with_parens(params: &str) -> String {
    format!("({})", params.trim())
}

/// Split C code into string literals, identifiers, and macros applied to them, like
/// `"foo: " dev_fmt(fmt)`, or `None` if it has anything else, like an operator.
fn pieces(code: &str) -> Option<Vec<Piece<'_>>> {
    let mut retval = vec![];
    let mut rest = code.trim();
    while !rest.is_empty() {
        if let Some(after_quote) = rest.strip_prefix('"') {
            let end = string_end(after_quote)?;
            retval.push(Piece::Literal(literal_to_regex(
                false,
                SourceLanguage::C,
                &after_quote[..end],
            )));
            rest = after_quote[end + 1..].trim_start();
            continue;
        }
        let len = rest
            .find(|c: char| !(c.is_alphanumeric() || c == '_'))
            .unwrap_or(rest.len());
        let ident = &rest[..len];
        if !is_identifier(ident) {
            return None;
        }
        rest = rest[len..].trim_start();
        if let Some(after_paren) = rest.strip_prefix('(') {
            let close = matching_paren(after_paren)?;
            retval.push(Piece::Apply(ident, pieces(&after_paren[..close])?));
            rest = after_paren[close + 1..].trim_start();
        } else {
            retval.push(Piece::Ident(ident));
        }
    }
    Some(retval)
}

/// The offset of the `)` that closes the one before the text.
fn matching_paren(text: &str) -> Option<usize> {
    let mut depth = 0;
    let mut quote = None;
    let mut escaped = false;
    for (pos, c) in text.char_indices() {
        if let Some(q) = quote {
            match c {
                _ if escaped => escaped = false,
                '\\' => escaped = true,
                _ if c == q => quote = None,
                _ => {}
            }
            continue;
        }
        match c {
            '"' | '\'' => quote = Some(c),
            '(' => depth += 1,
            ')' if depth == 0 => return Some(pos),
            ')' => depth -= 1,
            _ => {}
        }
    }
    None
}

/// The regexes for the text before and after the parameter in the pieces of an argument, if
/// the parameter is in them once and the rest is text.
fn around<'m>(
    pieces: &[Piece],
    param: &str,
    lookup: &MacroLookup<'_, 'm>,
    applied: &mut Vec<Applied<'m>>,
    depth: usize,
) -> Option<(String, String)> {
    if depth > MAX_APPLY_DEPTH {
        return None;
    }
    let mut prefix = String::new();
    let mut suffix = String::new();
    let mut seen_param = false;
    let mut push = |text: &str, seen_param: bool| {
        if seen_param {
            suffix.push_str(text);
        } else {
            prefix.push_str(text);
        }
    };
    for piece in pieces {
        match piece {
            Piece::Literal(regex) => push(regex, seen_param),
            Piece::Ident(ident) if *ident == param && !seen_param => seen_param = true,
            Piece::Ident(ident) if is_kernel_log_level(ident) => {}
            Piece::Ident(_) => return None,
            Piece::Apply(name, inner) if !seen_param => {
                let (inner_prefix, inner_suffix) =
                    around(inner, param, lookup, applied, depth + 1)?;
                let (path, wrapper) = lookup(name)?;
                let macro_pieces = wrapper.text_pieces()?;
                // This macro goes before the ones that it expands to.
                let at = applied.len();
                let (macro_prefix, macro_suffix) = around(
                    &macro_pieces,
                    &wrapper.params[0],
                    lookup,
                    applied,
                    depth + 1,
                )?;
                if !macro_prefix.is_empty() || !macro_suffix.is_empty() {
                    applied.insert(at, (path, wrapper));
                }
                push(&format!("{macro_prefix}{inner_prefix}"), false);
                seen_param = true;
                push(&format!("{inner_suffix}{macro_suffix}"), true);
            }
            Piece::Apply(..) => return None,
        }
    }
    seen_param.then_some((prefix, suffix))
}

/// Check if a C identifier is a Linux kernel log level, like `KERN_INFO`, which printk() takes
/// out of the message.
pub fn is_kernel_log_level(ident: &str) -> bool {
    ident
        .strip_prefix("KERN_")
        .is_some_and(|level| !level.is_empty() && level.chars().all(|c| c.is_ascii_uppercase()))
}

/// The offset of the `"` that ends a C string literal whose contents start the text.
fn string_end(text: &str) -> Option<usize> {
    let mut escaped = false;
    for (pos, c) in text.char_indices() {
        match c {
            _ if escaped => escaped = false,
            '\\' => escaped = true,
            '"' => return Some(pos),
            _ => {}
        }
    }
    None
}

/// The identifiers in some C code, not counting the contents of string literals.
fn tokens(code: &str) -> Vec<&str> {
    let mut retval = vec![];
    let mut rest = code;
    while let Some(c) = rest.chars().next() {
        if c == '"' {
            match string_end(&rest[1..]) {
                Some(end) => rest = &rest[end + 2..],
                None => break,
            }
        } else if c.is_alphabetic() || c == '_' {
            let len = rest
                .find(|c: char| !(c.is_alphanumeric() || c == '_'))
                .unwrap_or(rest.len());
            retval.push(&rest[..len]);
            rest = &rest[len..];
        } else {
            rest = &rest[c.len_utf8()..];
        }
    }
    retval
}

/// Split C arguments on the commas that are not nested in brackets or literals.
fn split_args(code: &str) -> Vec<&str> {
    let mut retval = vec![];
    let mut depth = 0;
    let mut quote = None;
    let mut escaped = false;
    let mut start = 0;
    for (pos, c) in code.char_indices() {
        if let Some(q) = quote {
            match c {
                _ if escaped => escaped = false,
                '\\' => escaped = true,
                _ if c == q => quote = None,
                _ => {}
            }
            continue;
        }
        match c {
            '"' | '\'' => quote = Some(c),
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            ',' if depth == 0 => {
                retval.push(&code[start..pos]);
                start = pos + 1;
            }
            _ => {}
        }
    }
    if !code[start..].trim().is_empty() || !retval.is_empty() {
        retval.push(&code[start..]);
    }
    retval
}

#[cfg(test)]
mod tests {
    use super::*;

    fn wrapper(params: &str, value: &str) -> Option<MacroWrapper> {
        MacroWrapper::parse("m", params, value, 1, 0)
    }

    fn no_macros(_name: &str) -> Option<(&'static str, &'static MacroWrapper)> {
        None
    }

    fn forward(m: &MacroWrapper, position: usize) -> Option<Forward> {
        m.forward(position, &no_macros, &mut vec![])
    }

    #[test]
    fn test_parse() {
        let m = wrapper(
            "(ohci, fmt, args...)",
            "\\\n\tdev_dbg (ohci_to_hcd(ohci)->self.controller , fmt , ## args )",
        )
        .unwrap();
        assert_eq!(m.params, vec!["ohci", "fmt"]);
        assert_eq!(m.callee(), Some("dev_dbg"));
        assert_eq!(
            m.body,
            MacroBody::Call {
                callee: "dev_dbg".to_string(),
                args: vec![
                    "ohci_to_hcd(ohci)->self.controller".to_string(),
                    "fmt".to_string(),
                    "## args".to_string()
                ]
            }
        );
        assert_eq!(
            m.text,
            "#define m(ohci, fmt, args...) dev_dbg (ohci_to_hcd(ohci)->self.controller , fmt , ## args )"
        );
        assert_eq!(
            forward(&m, 1),
            Some(Forward {
                position: 1,
                prefix: String::new(),
                suffix: String::new()
            })
        );
        assert_eq!(forward(&m, 0), None);

        let m = wrapper(
            "(handle, fmt, ...)",
            "acpi_handle_printk(KERN_INFO, handle, fmt, ##__VA_ARGS__)",
        )
        .unwrap();
        assert_eq!(forward(&m, 1).unwrap().position, 2);
        assert_eq!(m.constant_arg(0), Some("KERN_INFO"));
        assert_eq!(m.constant_arg(1), None);

        // String literals around the parameter are added to the message.
        let m = wrapper(
            "(fmt, ...)",
            r#"do { pr_debug("foo: " fmt "!\n", ##__VA_ARGS__); } while (0)"#,
        )
        .unwrap();
        assert_eq!(
            forward(&m, 0),
            Some(Forward {
                position: 0,
                prefix: "foo: ".to_string(),
                suffix: r"!\n".to_string()
            })
        );
        // Anything else around it changes the message in an unknown way.
        let m = wrapper("(fmt, ...)", "pr_debug(KBUILD_MODNAME fmt, ##__VA_ARGS__)").unwrap();
        assert_eq!(forward(&m, 0), None);

        // Text around a parameter is applied by other macros.
        let m = wrapper("(fmt)", r#""ACPI: " fmt"#).unwrap();
        assert_eq!(m.body, MacroBody::Text(r#""ACPI: " fmt"#.to_string()));
        assert_eq!(m.callee(), None);

        // Not a single call.
        assert_eq!(wrapper("(x)", "((x) * 2)"), None);
        assert_eq!(wrapper("(a, b)", "f(a) + g(b)"), None);
        assert_eq!(wrapper("(a)", "{ f(a); g(a); }"), None);
    }

    #[test]
    fn test_scan_defines() {
        let source = r#"#ifndef dev_fmt
#define dev_fmt(fmt) fmt /* the default */
#endif
 * possible use of #define dev_fmt(fmt) ...
#define dev_info(dev, fmt, ...) \
	dev_printk_index_wrap(_dev_info, KERN_INFO, dev, dev_fmt(fmt), ##__VA_ARGS__)
# define pr_fmt(fmt) "x: " fmt // comment
#define dev_fmt pr_fmt
#define LIMIT 10
#define wrap(x) ({ f(x); })
"#;
        let defines = scan_defines(source);
        let found: Vec<(usize, &str, Option<&str>)> = defines
            .iter()
            .map(|m| (m.line_no, m.name.as_str(), m.callee()))
            .collect();
        assert_eq!(
            found,
            vec![
                (2, "dev_fmt", None),
                (5, "dev_info", Some("dev_printk_index_wrap")),
                (7, "pr_fmt", None),
                (8, "dev_fmt", None),
            ]
        );
        assert_eq!(defines[0].body, MacroBody::Text("fmt".to_string()));
        assert_eq!(defines[2].body, MacroBody::Text(r#""x: " fmt"#.to_string()));
        assert_eq!(defines[3].body, MacroBody::Alias("pr_fmt".to_string()));
    }

    #[test]
    fn test_scan_defines_skips_disabled_code() {
        let source = r#"/*
#define pr_fmt(fmt) "old: " fmt
 */
#if 0
#define dbg(fmt) "zero: " fmt
#elif defined(DEBUG)
#define dbg(fmt) "elif: " fmt
#else
#define dbg(fmt) "else: " fmt
#endif
#if 1
#define info(fmt) "one: " fmt
#else
#define info(fmt) "not one: " fmt
#endif
#ifdef CONFIG_FOO
#define foo(fmt) "foo: " fmt /* one
two */
#endif
#define bar(fmt) "/* not a comment */ " fmt
"#;
        let found: Vec<(usize, String)> = scan_defines(source)
            .into_iter()
            .map(|m| (m.line_no, m.text))
            .collect();
        assert_eq!(
            found,
            vec![
                (7, r#"#define dbg(fmt) "elif: " fmt"#.to_string()),
                (9, r#"#define dbg(fmt) "else: " fmt"#.to_string()),
                (12, r#"#define info(fmt) "one: " fmt"#.to_string()),
                (17, r#"#define foo(fmt) "foo: " fmt"#.to_string()),
                (
                    20,
                    r#"#define bar(fmt) "/* not a comment */ " fmt"#.to_string()
                ),
            ]
        );
    }

    #[test]
    fn test_single_call_is_followed_and_applied() {
        // A single call is a call to follow, even with one parameter.
        let m = wrapper("(fmt)", r#"printk(KERN_DEBUG "drv: " fmt)"#).unwrap();
        assert_eq!(m.callee(), Some("printk"));
        assert_eq!(
            forward(&m, 0),
            Some(Forward {
                position: 0,
                prefix: "drv: ".to_string(),
                suffix: String::new()
            })
        );
        // It is also applied as text when another macro uses it like `pr_fmt()`.
        let pr_fmt = MacroWrapper::parse("pr_fmt", "(fmt)", r#""ACPI: " fmt"#, 1, 0).unwrap();
        let dev_fmt = MacroWrapper::parse("dev_fmt", "(fmt)", "pr_fmt(fmt)", 2, 0).unwrap();
        assert!(dev_fmt.is_text());
        let lookup = |name: &str| match name {
            "pr_fmt" => Some(("a.c", &pr_fmt)),
            "dev_fmt" => Some(("a.c", &dev_fmt)),
            _ => None,
        };
        let info = wrapper(
            "(fmt, ...)",
            "printk(KERN_INFO dev_fmt(fmt), ##__VA_ARGS__)",
        )
        .unwrap();
        let mut applied = vec![];
        assert_eq!(
            info.forward(0, &lookup, &mut applied).unwrap().prefix,
            "ACPI: "
        );
        assert_eq!(applied, vec![("a.c", &dev_fmt), ("a.c", &pr_fmt)]);
    }

    #[test]
    fn test_forward_through_text_macros() {
        let pr_fmt = MacroWrapper::parse("pr_fmt", "(fmt)", r#""ACPI: " fmt"#, 9, 0).unwrap();
        let dev_fmt = MacroWrapper::parse("dev_fmt", "(fmt)", "fmt", 3, 0).unwrap();
        let lookup = |name: &str| match name {
            "pr_fmt" => Some(("pci_root.c", &pr_fmt)),
            "dev_fmt" => Some(("dev_printk.h", &dev_fmt)),
            _ => None,
        };
        // The level is taken out by printk(), and pr_fmt() adds its text.
        let pr_info =
            wrapper("(fmt, ...)", "printk(KERN_INFO pr_fmt(fmt), ##__VA_ARGS__)").unwrap();
        let mut applied = vec![];
        assert_eq!(
            pr_info.forward(0, &lookup, &mut applied),
            Some(Forward {
                position: 0,
                prefix: "ACPI: ".to_string(),
                suffix: String::new()
            })
        );
        assert_eq!(applied, vec![("pci_root.c", &pr_fmt)]);
        // A text macro that adds nothing is not reported.
        let info = wrapper(
            "(handle, fmt, ...)",
            "acpi_handle_printk(KERN_INFO, handle, dev_fmt(fmt), ##__VA_ARGS__)",
        )
        .unwrap();
        let mut applied = vec![];
        assert_eq!(info.forward(1, &lookup, &mut applied).unwrap().position, 2);
        assert!(applied.is_empty());
        // A macro that is not known changes the message in an unknown way.
        let unknown = wrapper("(fmt, ...)", "printk(xyz_fmt(fmt), ##__VA_ARGS__)").unwrap();
        assert_eq!(unknown.forward(0, &lookup, &mut vec![]), None);
    }
}
