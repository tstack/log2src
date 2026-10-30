use std::borrow::Cow;
use std::path::Path;
use tree_sitter::{
    Language, Node, Parser, Point, Query, QueryCursor, Range as TSRange, StreamingIterator, Tree,
};

use crate::source_ref::{ArgCounter, FormatArgument, LogLevel, MessageCategory, Substitution};
use crate::value_kind::ValueKind;
use crate::{CodeSource, SourceLanguage};
use regex::Regex;
use std::sync::LazyLock;

pub struct SourceQuery<'a> {
    pub source: &'a str,
    filename: &'a str,
    tree: Tree,
    language: Language,
    source_language: SourceLanguage,
}

/// An argument for a placeholder and the kind of value its expression produces.
pub(crate) type Arg = (FormatArgument, ValueKind);

pub(crate) struct QueryResult {
    pub kind: String,
    pub range: TSRange,
    pub name: String,
    pub qualified_name: String,
    pub block_id: u32,
    pub pattern: Option<String>,
    pub args: Vec<Arg>,
    pub raw: bool,
    /// For an argument of the log call, the kind of value it produces.
    pub value_kind: ValueKind,
    /// The text of the last capture before the format string, which is the name of the logging
    /// function/macro/method being called (e.g. `log::warn`, `logger.info`).
    pub call_name: Option<String>,
    /// The text of the arguments before the format string, which might include the log level,
    /// as in `syslog(LOG_ERR, "...")`.
    pub leading_args: Vec<String>,
}

impl QueryResult {
    /// The level of the log call.  A level constant passed as an argument, like
    /// `syslog(LOG_ERR, ...)`, takes precedence over the name of the call.
    pub fn level(&self) -> LogLevel {
        self.arg_level()
            .or_else(|| self.call_name.as_deref().and_then(LogLevel::from_name))
            .unwrap_or(LogLevel::Unknown)
    }

    /// The level from a level constant passed as an argument, if there is one.
    pub fn arg_level(&self) -> Option<LogLevel> {
        self.leading_args
            .iter()
            .find_map(|arg| LogLevel::from_level_arg(arg))
    }
}

impl<'a> SourceQuery<'a> {
    pub fn new(code: &'a CodeSource) -> SourceQuery<'a> {
        // println!("{}", code.filename);
        let mut parser = Parser::new();
        let language = code.info.language.into();
        parser
            .set_language(&language)
            .unwrap_or_else(|_| panic!("Error loading {:?} grammar", language));
        let source = code.buffer.as_str();
        let mut tree = parser.parse(source, None).expect("source is parsable");
        // The text that `tree` was parsed from, which has the same byte offsets as `source`.
        let mut parsed: Cow<str> = Cow::Borrowed(source);
        if code.info.language.is_c_family() && tree.root_node().has_error() {
            if let Some(rewritten) = Self::rewrite_literal_macro_calls(source) {
                let rewritten_tree = parser.parse(&rewritten, None).expect("source is parsable");
                // A call next to a string-literal is never valid, so the rewrite is kept
                // unless it made things worse.  Some errors remain, like the ones for
                // `"x " ANSI_BOLD "%d"`, but those are handled by `concatenated_pattern()`.
                if Self::error_count(&rewritten_tree) <= Self::error_count(&tree) {
                    tree = rewritten_tree;
                    parsed = Cow::Owned(rewritten);
                }
            }
        }
        if code.info.language.is_c_family() && tree.root_node().has_error() {
            // Masking the conditionals can also break code that parses fine as-is, like
            // alternate function signatures in each branch, so it is only a fallback.
            if let Some(masked_source) = Self::mask_preproc_conditionals(&parsed, &tree) {
                let masked = parser
                    .parse(masked_source, None)
                    .expect("source is parsable");
                if Self::error_count(&masked) < Self::error_count(&tree) {
                    tree = masked;
                }
            }
        }
        SourceQuery {
            source,
            filename: code.filename.as_str(),
            tree,
            language,
            source_language: code.info.language,
        }
    }

    /// Blank out the `#if`/`#else`/`#endif` family of directives so the parser sees the code in
    /// every branch.  The grammar cannot handle a conditional that splits a statement, like an
    /// `else if` chain with one link under `#ifdef`, and its error recovery ends the function
    /// early, which leaves the rest of its log statements at file scope.  The directives are
    /// replaced with spaces so that byte offsets and line numbers still match the original
    /// source.  Directive-like text in comments and string literals, according to the original
    /// `tree`, is left alone.  Returns None if there was nothing to mask.
    fn mask_preproc_conditionals(source: &str, tree: &Tree) -> Option<String> {
        static CONDITIONAL_REGEX: LazyLock<Regex> = LazyLock::new(|| {
            Regex::new(
                r"(?m)^[ \t]*#[ \t]*(?:if|ifdef|ifndef|elif|elifdef|elifndef|else|endif)\b(?:[^\n]*\\\r?\n)*[^\n]*",
            )
            .unwrap()
        });
        let mut masked_any = false;
        let retval = CONDITIONAL_REGEX.replace_all(source, |caps: &regex::Captures| {
            let whole = caps.get(0).unwrap();
            let hash_pos = whole.start() + whole.as_str().find('#').unwrap();
            let in_literal = tree
                .root_node()
                .descendant_for_byte_range(hash_pos, hash_pos + 1)
                .is_some_and(|node| {
                    matches!(
                        node.kind(),
                        "comment"
                            | "string_literal"
                            | "string_content"
                            | "raw_string_literal"
                            | "raw_string_content"
                    )
                });
            if in_literal {
                return whole.as_str().to_string();
            }
            masked_any = true;
            // Map by byte so that multibyte characters in a trailing comment keep the
            // same length.
            caps[0]
                .bytes()
                .map(|b| {
                    if b == b'\n' || b == b'\r' {
                        b as char
                    } else {
                        ' '
                    }
                })
                .collect::<String>()
        });
        masked_any.then(|| retval.into_owned())
    }

    /// Replace the parentheses of macro calls that wrap a string-literal and are concatenated
    /// with other string-literals, like `ANSI_BOLD("%d") " rows"`, with spaces.  The grammar
    /// cannot parse these since it does not know the macro expands to a string, but it can
    /// parse `ANSI_BOLD "%d"  " rows"`, which keeps the same byte offsets.  Calls in comments
    /// and literals are left alone.  The tree is not used to find those since its error
    /// recovery for these calls can turn code into a string-literal.  Returns None if there was
    /// nothing to rewrite.
    fn rewrite_literal_macro_calls(source: &str) -> Option<String> {
        static CALL_REGEX: LazyLock<Regex> = LazyLock::new(|| {
            Regex::new(
                r#"\b[A-Za-z_][A-Za-z0-9_]*(\s*\()\s*(?:(?:u8|u|U|L)?"(?:[^"\\\n]|\\.)*"\s*)+(\))"#,
            )
            .unwrap()
        });
        let calls: Vec<_> = CALL_REGEX.captures_iter(source).collect();
        if calls.is_empty() {
            return None;
        }
        let code = Self::code_bytes(source);
        let bounds: Vec<_> = calls
            .iter()
            .map(|call| {
                let whole = call.get(0).unwrap();
                let before = source[..whole.start()].trim_end();
                let after = source[whole.end()..].trim_start();
                (
                    before.len(),
                    whole.start(),
                    whole.end(),
                    source.len() - after.len(),
                )
            })
            .collect();
        // Only rewrite calls that are next to a string-literal, or next to another call that
        // is rewritten, like `"x " A("y") B("z")`, since a call like `_("...")` is valid as-is.
        let mut rewrite: Vec<bool> = bounds
            .iter()
            .map(|&(before_end, start, _, after_start)| {
                let before = &source[..before_end];
                // The `"` of a directive, like `#include "x.h"`, is not part of an expression.
                let after_directive = before
                    .rsplit('\n')
                    .next()
                    .is_some_and(|line| line.trim_start().starts_with('#'));
                code[start]
                    && ((before.ends_with('"') && !after_directive)
                        || source[after_start..].starts_with('"'))
            })
            .collect();
        let adjacent =
            |left: usize, right: usize| code[bounds[right].1] && bounds[left].3 == bounds[right].1;
        for index in 1..calls.len() {
            if rewrite[index - 1] && adjacent(index - 1, index) {
                rewrite[index] = true;
            }
        }
        for index in (1..calls.len()).rev() {
            if rewrite[index] && adjacent(index - 1, index) {
                rewrite[index - 1] = true;
            }
        }
        let mut retval = source.as_bytes().to_vec();
        let mut rewrote_any = false;
        for (call, _) in calls.iter().zip(&rewrite).filter(|(_, rewrite)| **rewrite) {
            let open = call.get(1).unwrap();
            let close = call.get(2).unwrap();
            retval[open.end() - 1] = b' ';
            retval[close.start()] = b' ';
            rewrote_any = true;
        }
        // Only ASCII parentheses were replaced, so the result is still UTF-8.
        rewrote_any.then(|| String::from_utf8(retval).unwrap())
    }

    /// Find which bytes of C or C++ source are code, and not in a comment or a string or
    /// character literal.
    fn code_bytes(source: &str) -> Vec<bool> {
        let bytes = source.as_bytes();
        let mut retval = vec![true; bytes.len()];
        let mut index = 0;
        while index < bytes.len() {
            let start = index;
            let end = match bytes[index] {
                b'/' if bytes.get(index + 1) == Some(&b'/') => {
                    // Line comments can be continued with a backslash, like macros.
                    let mut end = index;
                    while end < bytes.len() && bytes[end] != b'\n' {
                        end += if bytes[end] == b'\\' { 2 } else { 1 };
                    }
                    end
                }
                b'/' if bytes.get(index + 1) == Some(&b'*') => source[index + 2..]
                    .find("*/")
                    .map_or(bytes.len(), |end| index + 2 + end + 2),
                // A digit separator, like `1'000`, is not a character literal.
                b'\'' if index > 0 && bytes[index - 1].is_ascii_hexdigit() => {
                    index += 1;
                    continue;
                }
                quote @ (b'"' | b'\'') => {
                    Self::raw_string_end(source, index).unwrap_or_else(|| {
                        let mut end = index + 1;
                        while end < bytes.len() && bytes[end] != quote && bytes[end] != b'\n' {
                            end += if bytes[end] == b'\\' { 2 } else { 1 };
                        }
                        end + 1
                    })
                }
                _ => {
                    index += 1;
                    continue;
                }
            };
            let end = end.min(bytes.len());
            retval[start..end].fill(false);
            index = end;
        }
        retval
    }

    /// If the `"` at `index` starts a raw string, like `R"delim(...)delim"`, returns the offset
    /// just past its end.  The `R` has to be a whole prefix, so `ANSI_CLEAR"x"` is not one.
    fn raw_string_end(source: &str, index: usize) -> Option<usize> {
        let before = &source[..index];
        let prefix_start = before
            .trim_end_matches(|c: char| c.is_ascii_alphanumeric() || c == '_')
            .len();
        if !matches!(&before[prefix_start..], "R" | "LR" | "uR" | "UR" | "u8R") {
            return None;
        }
        let delim_len = source[index + 1..].find('(')?;
        let delim = &source[index + 1..index + 1 + delim_len];
        if delim.len() > 16
            || delim.contains(|c: char| c.is_whitespace() || matches!(c, ')' | '\\' | '"'))
        {
            return None;
        }
        let terminator = format!("){delim}\"");
        let body = index + 1 + delim_len;
        Some(
            source[body..]
                .find(&terminator)
                .map_or(source.len(), |end| body + end + terminator.len()),
        )
    }

    /// Count the error and missing nodes in a tree.
    fn error_count(tree: &Tree) -> usize {
        let mut count = 0;
        let mut cursor = tree.walk();
        loop {
            let node = cursor.node();
            if node.is_error() || node.is_missing() {
                count += 1;
            }
            // Only subtrees with errors need to be visited.
            if node.has_error() && cursor.goto_first_child() {
                continue;
            }
            while !cursor.goto_next_sibling() {
                if !cursor.goto_parent() {
                    return count;
                }
            }
        }
    }

    pub(crate) fn query(&self, query: &str, node_kind: Option<&str>) -> Vec<QueryResult> {
        let query = Query::new(&self.language, query).unwrap();
        let filter_idx = node_kind.and_then(|kind| query.capture_index_for_name(kind));
        let mut cursor = QueryCursor::new();
        let mut results = Vec::new();
        let matches = cursor.matches(&query, self.tree.root_node(), self.source.as_bytes());
        matches.for_each(|m| {
            let mut got_string_literal = false;
            let mut call_name: Option<String> = None;
            for capture in m.captures {
                // captures starting with an underscore are only used for predicates
                if query.capture_names()[capture.index as usize].starts_with('_') {
                    continue;
                }
                let mut child = capture.node;
                let mut concat_pattern = None;
                let mut concat_args = vec![];
                // Computed on demand since only some captures need them.
                let mut leading_args: Option<Vec<String>> = None;
                let mut kind = child.kind();
                // The argument of the log call that holds the message, which is not the
                // message itself when it is wrapped, like `String.format("...", x)`.
                let mut outer = child;
                // The node whose following siblings are the arguments for the placeholders.
                let mut args_anchor = None;
                let mut printf = false;
                // The name of the call that formats a wrapped message, like `fmt::format`.
                let mut format_call = None;
                if let Some(lambda) = outer.parent().filter(|p| p.kind() == "lambda_expression") {
                    // A Java supplier, like `log.fine(() -> "...")`.
                    outer = lambda;
                }
                if query.capture_names()[capture.index as usize] == "message-call" {
                    // A message built by another call, like `fmt::format("...", x)`.
                    let Some(wrapped) = self.unwrap_message_call(child) else {
                        break;
                    };
                    // Only the first message of a call is used, like other captures.
                    if self.follows_message(outer, |_| true) {
                        break;
                    }
                    if wrapped.args_anchor != child {
                        // Not a translation, which only passes the message through.
                        format_call = child
                            .child_by_field_name("function")
                            .map(|function| self.source[function.byte_range()].to_string());
                    }
                    child = wrapped.literal;
                    args_anchor = Some(wrapped.args_anchor);
                    printf = wrapped.printf;
                    kind = child.kind();
                } else if self.source_language.is_c_family()
                    && self.follows_message(outer, |arg| self.unwrap_message_call(arg).is_some())
                {
                    // An argument for a wrapped message, like the `"file.txt"` in
                    // `log(fmt::runtime(_("Loaded {}")), "file.txt")`.
                    break;
                }
                // The Java query already requires a logger, but C++ strings and calls are
                // wrapped like this for all sorts of reasons, so only keep the ones passed to a
                // logging call.
                if self.source_language != SourceLanguage::Java
                    && (outer != capture.node || child != capture.node)
                {
                    // Strings and calls are wrapped like this for all sorts of reasons, so
                    // only keep the ones passed to a logging call or an error, like a C++
                    // `throw`.  A message that is formatted for some other call, like
                    // `report(fmt::format("..."))`, is kept as a message of the format call.
                    let leading = leading_args.get_or_insert_with(|| self.leading_args(outer));
                    // The message of a C or C++ call that formats or makes an error, like
                    // `snprintf(buf, n, _("..."), x)` or `throw X(_("..."))`, is kept too.
                    if !Self::has_level(call_name.as_deref(), leading)
                        && !(self.source_language.is_c_family()
                            && Self::is_c_message_call(call_name.as_deref()))
                    {
                        match format_call.take() {
                            Some(name) => call_name = Some(name),
                            None => break,
                        }
                    }
                }
                if query.capture_names()[capture.index as usize] == "message-ref" {
                    // A log message that is a constant defined elsewhere, like
                    // `log.info(Messages.LOG_STARTING, name)`.
                    if !self.is_message_ref(child) {
                        break;
                    }
                    kind = "message_ref";
                }
                let mut raw = false;
                if self.source_language == SourceLanguage::Rust && kind == "token_tree" {
                    // The arguments of a `concat!` used as the format string.
                    match self.rust_concat_pattern(child) {
                        Some(pattern) => concat_pattern = Some(pattern),
                        None => break,
                    }
                    kind = "string_literal";
                }
                if self.source_language == SourceLanguage::Cpp && kind == "raw_string_literal" {
                    // Raw strings are used for all sorts of things, like JSON and usage text,
                    // so only keep the ones passed to a logging call or used for a message.
                    let leading = leading_args.get_or_insert_with(|| self.leading_args(outer));
                    if !Self::has_level(call_name.as_deref(), leading)
                        && !Self::is_c_message_call(call_name.as_deref())
                    {
                        break;
                    }
                    // The contents of a raw string, like `R"(...)"`, are used as-is.
                    let mut cursor = child.walk();
                    let content = child
                        .named_children(&mut cursor)
                        .find(|piece| piece.kind() == "raw_string_content")
                        .map_or("", |piece| &self.source[piece.byte_range()]);
                    concat_pattern = Some(content.to_string());
                    raw = true;
                    kind = "string_literal";
                }
                if self.source_language == SourceLanguage::Python
                    && matches!(kind, "binary_operator" | "call")
                    && query.capture_names()[capture.index as usize] == "args"
                {
                    // A message that is formatted before it is logged, like `"..." % args`.
                    // Strings are built like this for all sorts of calls, so only keep the
                    // ones passed to a logging call or an exception.
                    let leading = leading_args.get_or_insert_with(|| self.leading_args(child));
                    if !Self::has_level(call_name.as_deref(), leading)
                        && !call_name
                            .as_deref()
                            .is_some_and(MessageCategory::is_exception_call)
                    {
                        break;
                    }
                    match self.python_expr_pattern(child, Self::has_python_format_args(child)) {
                        Some((pattern, args)) => {
                            concat_pattern = Some(pattern);
                            concat_args = args;
                        }
                        None => break,
                    }
                    kind = "string";
                }
                match kind {
                    "message_ref" => {
                        got_string_literal = true;
                    }
                    "string_literal" | "string" | "concatenated_string" | "binary_expression" => {
                        if self.source_language.is_c_family() && !Self::in_function_body(child) {
                            // Calls at file scope are macros like TEST_CASE("...") or
                            // _Pragma("...") and not log statements.
                            break;
                        }
                        if child.kind() == "concatenated_string"
                            && self.source_language.is_c_family()
                        {
                            match self.concatenated_pattern(child) {
                                Some((pattern, args)) => {
                                    concat_pattern = Some(pattern);
                                    concat_args = args;
                                }
                                None => break,
                            }
                        }
                        if child.kind() == "string_literal"
                            && self.source_language == SourceLanguage::Kotlin
                        {
                            match self.kotlin_pattern(child) {
                                Some((pattern, args)) => {
                                    concat_pattern = Some(pattern);
                                    concat_args = args;
                                }
                                None => break,
                            }
                        }
                        if child.kind() == "binary_expression"
                            && self.source_language.is_c_family()
                            && !Self::has_level(
                                call_name.as_deref(),
                                leading_args.get_or_insert_with(|| self.leading_args(outer)),
                            )
                            && !Self::is_c_message_call(call_name.as_deref())
                        {
                            // C++ strings are concatenated for all sorts of calls, like paths
                            // and option names, so only keep the ones passed to a logging call
                            // or used for a message.
                            break;
                        }
                        if child.kind() == "binary_expression" {
                            let concat = match self.source_language {
                                SourceLanguage::Kotlin => self.kotlin_concat_pattern(child),
                                _ => self.concat_pattern(child),
                            };
                            match concat {
                                Some((pattern, args)) => {
                                    concat_pattern = Some(pattern);
                                    concat_args = args;
                                }
                                None => break,
                            }
                        }
                        if printf {
                            // A Java `String.format()` message, so the printf-style
                            // conversions need to become placeholders.  Concatenated
                            // expressions would mix the two kinds of placeholders.
                            if concat_args
                                .iter()
                                .any(|(arg, _)| matches!(arg, FormatArgument::Named(_)))
                            {
                                break;
                            }
                            let Some(text) = concat_pattern
                                .take()
                                .map(Cow::Owned)
                                .or_else(|| self.string_contents(child))
                            else {
                                break;
                            };
                            let (pattern, args) = printf_to_placeholders(&text);
                            concat_pattern = Some(pattern);
                            concat_args = args;
                        }
                        // only return results after the format string literal, other captures
                        // are not relevant.
                        got_string_literal = true;
                    }
                    _ => {
                        if !got_string_literal {
                            // remember the name of the logging call so the log level can be
                            // derived from it.
                            let range = capture.node.byte_range();
                            call_name = Some(
                                self.special_call_name(capture.node)
                                    .unwrap_or_else(|| self.source[range].to_string()),
                            );
                            continue;
                        }
                    }
                }
                let mut arg_start: Option<(usize, Point)> = None;

                if filter_idx.is_none() || filter_idx.is_some_and(|f| f == capture.index) {
                    let anchor = Self::statement_anchor(outer);
                    let (name, qualified_name) = self.names(anchor);
                    let block_id = self.block_id(anchor);
                    let qr_index = results.len();
                    let mut range = child.range();
                    if let Some(prefix) = Self::concat_error_prefix(child) {
                        range.start_byte = prefix.start_byte();
                        range.start_point = prefix.start_position();
                    }
                    if let Some(close) = self.trailing_macro_call_paren(child) {
                        // The `)` of a macro call at the end, like `"x " ANSI_BOLD("%d")`.
                        range.end_byte = close + 1;
                        range.end_point = Point::new(
                            range.end_point.row,
                            range.end_point.column + (close + 1 - child.end_byte()),
                        );
                    }
                    results.push(QueryResult {
                        kind: kind.to_string(),
                        range,
                        name: name.clone(),
                        qualified_name: qualified_name.clone(),
                        block_id,
                        pattern: concat_pattern.take(),
                        args: std::mem::take(&mut concat_args),
                        raw,
                        value_kind: ValueKind::Any,
                        call_name: call_name.clone(),
                        leading_args: leading_args
                            .take()
                            .unwrap_or_else(|| self.leading_args(outer)),
                    });
                    if let Some(anchor) = args_anchor {
                        child = anchor;
                    }
                    if self.source_language == SourceLanguage::Python
                        && matches!(child.kind(), "string" | "concatenated_string")
                    {
                        let (pattern, args) =
                            self.python_pattern(child, Self::has_python_format_args(child));
                        results[qr_index].pattern = Some(pattern);
                        results[qr_index].args = args;
                    }
                    if let Some(parent) = child.parent().filter(|p| p.kind() == "value_argument") {
                        // Kotlin wraps each argument, so the separators are the wrapper's
                        // siblings.
                        child = parent;
                    }
                    // The expressions between the current separators.
                    let mut arg_nodes: Vec<Node> = vec![];
                    while let Some(next_child) = child.next_sibling() {
                        if matches!(next_child.kind(), "," | ")") {
                            let value_kind = match (arg_start, &arg_nodes[..]) {
                                // The arguments of a Rust macro are tokens, not expressions.
                                (Some(start), _)
                                    if next_child
                                        .parent()
                                        .is_some_and(|p| p.kind() == "token_tree") =>
                                {
                                    ValueKind::from_rust_tokens(
                                        &self.source[start.0..next_child.start_byte()],
                                    )
                                }
                                (_, [node]) => self.value_kind(*node),
                                _ => ValueKind::Any,
                            };
                            arg_nodes.clear();
                            if let Some(start) = arg_start {
                                if start.0 < next_child.start_byte() {
                                    results.push(QueryResult {
                                        kind: "args".to_string(),
                                        range: TSRange {
                                            start_byte: start.0,
                                            start_point: start.1,
                                            end_byte: next_child.start_byte(),
                                            end_point: next_child.start_position(),
                                        },
                                        name: name.clone(),
                                        qualified_name: qualified_name.clone(),
                                        block_id,
                                        pattern: None,
                                        args: vec![],
                                        raw: false,
                                        value_kind,
                                        call_name: None,
                                        leading_args: vec![],
                                    });
                                }
                            }
                            arg_start = Some((next_child.end_byte(), next_child.end_position()));
                        } else if arg_start.is_some()
                            && next_child.is_named()
                            && !next_child.kind().contains("comment")
                        {
                            arg_nodes.push(next_child);
                        }
                        child = next_child;
                    }
                }
            }
        });

        results
    }

    pub(crate) fn root_node(&self) -> Node<'_> {
        self.tree.root_node()
    }

    /// Check that a captured message argument looks like a reference to a constant, like
    /// `LOG_STARTING` or `Messages.LOG_STARTING`.  If the next argument is a string-literal,
    /// this argument is a Level or Marker and the literal is the message.
    fn is_message_ref(&self, node: Node) -> bool {
        let text = &self.source[node.start_byte()..node.end_byte()];
        let name = text.rsplit('.').next().unwrap_or(text).trim();
        let is_constant_name = name.starts_with(|c: char| c.is_ascii_uppercase())
            && name
                .chars()
                .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_');
        let next_is_literal = node
            .next_named_sibling()
            .is_some_and(|next| self.is_message_like(next));
        is_constant_name && !next_is_literal
    }

    /// Get the value of a Java string-literal or concatenation of string-literals, like the
    /// initializer for `static final String MSG = "abc " + "def";`.
    pub(crate) fn java_literal_value(&self, node: Node<'a>) -> Option<String> {
        let mut pieces = Vec::new();
        self.flatten_concat(node, &mut pieces);
        let mut retval = String::new();
        for piece in pieces {
            match piece {
                ConcatPiece::Literal(text) => retval.push_str(&text),
                ConcatPiece::Expr(_) => return None,
            }
        }
        Some(retval)
    }

    /// Join the pieces of a C or C++ concatenated string, like `"abc " "def"`, into the
    /// contents of a single string-literal.  A macro whose value is unknown, like the
    /// `ANSI_NORM` in `"%d" ANSI_NORM " rows"`, matches any text.  So does each side of a
    /// macro call, like `ANSI_BOLD("%d")`, which `rewrite_literal_macro_calls()` made parsable.
    /// If there are any macros, the returned arguments list every placeholder in order, with
    /// the macros as named arguments so that they do not use up the arguments of the call.
    /// Returns None if a piece cannot be resolved, like a function call.
    fn concatenated_pattern(&self, node: Node) -> Option<(String, Vec<Arg>)> {
        // The placeholder used for a macro, and where they are in the pattern.
        const MACRO_PLACEHOLDER: &str = "%s";
        let mut macros: Vec<(usize, &str)> = Vec::new();
        let mut pattern = String::new();
        let mut cursor = node.walk();
        let mut pieces: Vec<Node> = vec![];
        if let Some(prefix) = Self::concat_error_prefix(node) {
            let mut prefix_cursor = prefix.walk();
            pieces.extend(prefix.named_children(&mut prefix_cursor));
        }
        pieces.extend(node.named_children(&mut cursor));
        // The name of the macro call whose argument is the next piece.
        let mut call_name = None;
        for piece in pieces {
            let text = &self.source[piece.start_byte()..piece.end_byte()];
            // The C++ grammar wraps a macro that follows a string-literal in an ERROR node.
            let kind = match piece.kind() {
                "ERROR" if is_identifier(text) => "identifier",
                kind => kind,
            };
            match kind {
                "string_literal" => {
                    // Skip any prefix, like L or u8, and the quotes.
                    let start = text.find('"')? + 1;
                    let end = text.rfind('"')?;
                    pattern.push_str(text.get(start..end)?);
                    // Part of the argument of a macro call, which can be several adjacent
                    // string-literals, like `ANSI_BOLD("abc" "def")`.  The call ends after the
                    // last one.  If anything else follows, the call was not rewritten, and the
                    // next piece ends the pattern below.
                    let call_ends = self.source[piece.end_byte()..]
                        .trim_start()
                        .starts_with(')');
                    if let Some(name) = call_name.filter(|_| call_ends) {
                        call_name = None;
                        macros.push((pattern.len(), name));
                        pattern.push_str(MACRO_PLACEHOLDER);
                    }
                }
                // The <cinttypes> macros, like "%" PRIu64, finish a conversion specification.
                "identifier" if call_name.is_none() && is_inttypes_macro(text) => {
                    pattern.push('d');
                }
                // Other macros can too, like "%" G_GINT64_FORMAT, but their type is unknown.
                "identifier" if call_name.is_none() && ends_in_open_conversion(&pattern) => {
                    pattern.push('s');
                }
                "identifier" if call_name.is_none() => {
                    if self.source[piece.end_byte()..]
                        .trim_start()
                        .starts_with('(')
                    {
                        call_name = Some(text);
                    }
                    macros.push((pattern.len(), text));
                    pattern.push_str(MACRO_PLACEHOLDER);
                }
                _ => return None,
            }
        }
        if call_name.is_some() {
            // A macro call at the end that was not rewritten, like `"x" A("y", "z")`.
            return None;
        }
        if macros.is_empty() {
            // The placeholders will be found when building the matcher.
            return Some((pattern, vec![]));
        }
        let language = self.source_language;
        let mut counter = ArgCounter::default();
        let mut args = Vec::new();
        for cap in language.get_placeholder_regex().captures_iter(&pattern) {
            let start = cap.get(0).unwrap().start();
            if let Some((_, name)) = macros.iter().find(|(offset, _)| *offset == start) {
                args.push((FormatArgument::Named(name.to_string()), ValueKind::Any));
                continue;
            }
            if let Substitution::Value(arg) = counter.substitution(language, &cap) {
                args.push((arg, ValueKind::Any));
            }
        }
        let named = args
            .iter()
            .filter(|(arg, _)| matches!(arg, FormatArgument::Named(_)))
            .count();
        // A macro that was swallowed by a conversion would match its placeholder as text.
        (named >= macros.len()).then_some((pattern, args))
    }

    /// The C++ grammar cannot parse a concatenation where a macro follows the first
    /// string-literal, like `"unknown " SOME_MACRO " text"`, so it wraps the leading
    /// string-literals in an ERROR node just before the rest of the concatenation.  Returns
    /// that node, if there is one.
    pub(crate) fn concat_error_prefix(node: Node) -> Option<Node> {
        if node.kind() != "concatenated_string" {
            return None;
        }
        let prefix = node.prev_sibling().filter(|prev| prev.is_error())?;
        let mut cursor = prefix.walk();
        let only_literals = prefix.child_count() > 0
            && prefix
                .children(&mut cursor)
                .all(|piece| piece.kind() == "string_literal");
        only_literals.then_some(prefix)
    }

    /// If a concatenation ends with a macro call that `rewrite_literal_macro_calls()` made
    /// parsable, like `"x " ANSI_BOLD("%d")`, returns the offset of the call's `)`, which the
    /// tree does not include.  Only spaces are expected before it, like in the rewrite.
    fn trailing_macro_call_paren(&self, node: Node) -> Option<usize> {
        if node.kind() != "concatenated_string" {
            return None;
        }
        let literal = node.named_child(node.named_child_count().checked_sub(1)?)?;
        // The argument can be several adjacent string-literals, like `A("abc" "def")`.
        let mut first = literal;
        while let Some(prev) = first.prev_named_sibling().filter(|prev| {
            prev.kind() == "string_literal"
                && self.source[prev.end_byte()..first.start_byte()]
                    .trim()
                    .is_empty()
        }) {
            first = prev;
        }
        let name = first.prev_named_sibling()?;
        let after_name = &self.source[name.end_byte()..first.start_byte()];
        let after_literal = &self.source[literal.end_byte()..];
        let spaces = after_literal.len() - after_literal.trim_start_matches(' ').len();
        (literal.kind() == "string_literal"
            && matches!(name.kind(), "identifier" | "ERROR")
            && after_name.trim() == "("
            && after_literal[spaces..].starts_with(')'))
        .then(|| literal.end_byte() + spaces)
    }

    /// Check if a Python log message is followed by positional arguments.  The `logging` module
    /// only applies %-formatting to the message when there are arguments, and the `%` operator
    /// always has an argument.
    fn has_python_format_args(message: Node) -> bool {
        let mut next = message.next_named_sibling();
        while let Some(node) = next {
            if !matches!(
                node.kind(),
                "keyword_argument" | "dictionary_splat" | "comment"
            ) {
                return true;
            }
            next = node.next_named_sibling();
        }
        false
    }

    /// Convert a Python string, or adjacent strings like `"abc " f"{x}"`, into the contents of a
    /// single non-raw string-literal.  Interpolations are replaced with placeholders and, if
    /// there are any, the returned arguments list every placeholder in order.  If there are no
    /// `format_args`, a `%` in the string is literal text.
    fn python_pattern(&self, node: Node, format_args: bool) -> (String, Vec<Arg>) {
        let (pattern, mut args, interpolated) = self.python_template(node, format_args);
        if !interpolated {
            // The placeholders will be found when building the matcher.
            args.clear();
        }
        (pattern, args)
    }

    /// Convert a Python string into a pattern and the arguments for all of its placeholders.
    /// Also returns whether the string has any interpolations.
    fn python_template(&self, node: Node, format_args: bool) -> (String, Vec<Arg>, bool) {
        let mut pattern = String::new();
        let mut args = Vec::new();
        let mut counter = ArgCounter::default();
        let mut interpolated = false;
        let mut cursor = node.walk();
        let strings: Vec<Node> = if node.kind() == "concatenated_string" {
            node.named_children(&mut cursor)
                .filter(|n| n.kind() == "string")
                .collect()
        } else {
            vec![node]
        };
        for string in strings {
            let mut raw = false;
            let mut fstring = false;
            let mut string_cursor = string.walk();
            for string_child in string.children(&mut string_cursor) {
                let text = &self.source[string_child.start_byte()..string_child.end_byte()];
                match string_child.kind() {
                    "string_start" => {
                        let prefix = text.trim_end_matches(['"', '\'']).to_ascii_lowercase();
                        raw = prefix.contains('r');
                        fstring = prefix.contains('f');
                    }
                    "string_content" => {
                        let mut content = String::new();
                        let mut last_end = string_child.start_byte();
                        let mut content_cursor = string_child.walk();
                        for esc in string_child.children(&mut content_cursor) {
                            if fstring && esc.kind() == "escape_interpolation" {
                                // A "{{" or "}}" in an f-string is a single brace.
                                content.push_str(&self.source[last_end..esc.start_byte()]);
                                content
                                    .push_str(&self.source[esc.start_byte()..esc.start_byte() + 1]);
                                last_end = esc.end_byte();
                            }
                        }
                        content.push_str(&self.source[last_end..string_child.end_byte()]);
                        if raw {
                            // The pieces are combined into a single non-raw string, so the
                            // backslashes in a raw string need to be escaped.
                            content = content.replace('\\', "\\\\");
                        }
                        if format_args {
                            for cap in self
                                .source_language
                                .get_placeholder_regex()
                                .captures_iter(&content)
                            {
                                if let Substitution::Value(arg) =
                                    counter.substitution(self.source_language, &cap)
                                {
                                    args.push((arg, ValueKind::Any));
                                }
                            }
                        } else {
                            content = content.replace('%', "%%");
                        }
                        pattern.push_str(&content);
                    }
                    "interpolation" => {
                        // Swap in a Python placeholder for the interpolation expression.  The
                        // kind of value comes from the format spec, if there is one, and
                        // otherwise from the expression.
                        pattern.push_str("%s");
                        interpolated = true;
                        let mut spec_cursor = string_child.walk();
                        let spec_kind = string_child
                            .children(&mut spec_cursor)
                            .find(|node| node.kind() == "format_specifier")
                            .map_or(ValueKind::Any, |spec| {
                                let spec = &self.source[spec.byte_range()];
                                ValueKind::from_format_spec(spec.strip_prefix(':').unwrap_or(spec))
                            });
                        if let Some(expr) = string_child.child_by_field_name("expression") {
                            let kind = match spec_kind {
                                ValueKind::Any => self.value_kind(expr),
                                _ => spec_kind,
                            };
                            args.push((
                                FormatArgument::Named(
                                    self.source[expr.start_byte()..expr.end_byte()].to_string(),
                                ),
                                kind,
                            ));
                        }
                    }
                    _ => {}
                }
            }
        }
        (pattern, args, interpolated)
    }

    /// Convert a Python message that is formatted before being logged into a pattern, like
    /// `"user %s" % name`, `"user " + name`, or `"user {}".format(name)`.  The expressions
    /// are the arguments of the placeholders.  Returns None for anything else, like arithmetic.
    fn python_expr_pattern(&self, node: Node, format_args: bool) -> Option<(String, Vec<Arg>)> {
        match node.kind() {
            "binary_operator" => match node.child_by_field_name("operator")?.kind() {
                "%" => self.python_percent_pattern(node, format_args),
                "+" => self.python_concat_pattern(node, format_args),
                _ => None,
            },
            "call" => self.python_format_pattern(node, format_args),
            _ => None,
        }
    }

    fn is_python_string(node: Node) -> bool {
        matches!(node.kind(), "string" | "concatenated_string")
    }

    /// Convert `"user %s has %d items" % (name, count)` into a pattern.  If the logging call
    /// has its own `format_args`, the result is formatted again, so a `%%` would become a
    /// placeholder.  That is not supported.
    fn python_percent_pattern(&self, node: Node, format_args: bool) -> Option<(String, Vec<Arg>)> {
        let left = node.child_by_field_name("left")?;
        let right = Self::python_unparenthesize(node.child_by_field_name("right")?);
        let left_text = &self.source[left.byte_range()];
        // Mapping keys, like `%(name)s`, are not supported.
        if !Self::is_python_string(left)
            || left_text.contains("%(")
            || (format_args && left_text.contains("%%"))
        {
            return None;
        }
        let (pattern, placeholders, interpolated) = self.python_template(left, true);
        if interpolated {
            return None;
        }
        let values: Vec<Node> = if right.kind() == "tuple" {
            let mut cursor = right.walk();
            right
                .named_children(&mut cursor)
                .filter(|n| n.kind() != "comment")
                .collect()
        } else {
            vec![right]
        };
        if values
            .iter()
            .any(|v| matches!(v.kind(), "dictionary" | "list_splat"))
        {
            return None;
        }
        // A single value for several placeholders is a tuple, like `"(%s, %s)" % pair`.
        let tuple_var = (values.len() == 1 && right.kind() != "tuple" && placeholders.len() > 1)
            .then(|| self.source[right.byte_range()].trim());
        let mut next = 0;
        let mut args = Vec::new();
        for (arg, _) in placeholders {
            let index = match arg {
                FormatArgument::Placeholder => {
                    next += 1;
                    next - 1
                }
                FormatArgument::Positional(index) => index,
                FormatArgument::Named(_) => return None,
            };
            if let Some(var) = tuple_var {
                args.push((
                    FormatArgument::Named(format!("{var}[{index}]")),
                    ValueKind::Any,
                ));
                continue;
            }
            let value = values.get(index)?;
            args.push((self.python_arg(*value), self.value_kind(*value)));
        }
        Some((pattern, args))
    }

    /// Convert `"user " + name + " logged in"` into a pattern.
    fn python_concat_pattern(&self, node: Node, format_args: bool) -> Option<(String, Vec<Arg>)> {
        let mut operands = vec![];
        let mut pending = vec![node];
        while let Some(curr) = pending.pop() {
            let is_plus = curr.kind() == "binary_operator"
                && curr
                    .child_by_field_name("operator")
                    .is_some_and(|op| op.kind() == "+");
            if is_plus {
                pending.push(curr.child_by_field_name("right")?);
                pending.push(curr.child_by_field_name("left")?);
            } else {
                operands.push(curr);
            }
        }
        if !operands.iter().any(|n| Self::is_python_string(*n)) {
            return None;
        }
        let mut pattern = String::new();
        let mut args = Vec::new();
        let mut interpolated = false;
        for operand in operands {
            if Self::is_python_string(operand) {
                let (piece, piece_args, piece_interpolated) =
                    self.python_template(operand, format_args);
                pattern.push_str(&piece);
                args.extend(piece_args);
                interpolated |= piece_interpolated;
            } else if let Some((piece, piece_args)) = self.python_expr_pattern(operand, format_args)
            {
                // A formatted operand, like the `"b %s" % x` in `"a " + "b %s" % x`.
                pattern.push_str(&piece);
                args.extend(piece_args);
                interpolated = true;
            } else {
                pattern.push_str("%s");
                args.push((self.python_arg(operand), self.value_kind(operand)));
                interpolated = true;
            }
        }
        if !interpolated {
            args.clear();
        }
        Some((pattern, args))
    }

    /// Convert `"user {} has {count} items".format(name, count=n)` into a pattern.
    fn python_format_pattern(&self, node: Node, format_args: bool) -> Option<(String, Vec<Arg>)> {
        // Backslash escapes are skipped so the braces in a `\N{NAME}` are not a field.
        static FIELD_REGEX: LazyLock<Regex> =
            LazyLock::new(|| Regex::new(r"\\N\{[^{}]*\}|\\.|\{\{|\}\}|\{([^{}]*)\}|[{}]").unwrap());
        let function = node.child_by_field_name("function")?;
        let string = function.child_by_field_name("object")?;
        let method = function.child_by_field_name("attribute")?;
        if !Self::is_python_string(string) || &self.source[method.byte_range()] != "format" {
            return None;
        }
        let (text, placeholders, interpolated) = self.python_template(string, format_args);
        if interpolated || (format_args && !placeholders.is_empty()) {
            return None;
        }
        let mut positional = vec![];
        let mut keywords = vec![];
        let arguments = node.child_by_field_name("arguments")?;
        let mut cursor = arguments.walk();
        for arg in arguments.named_children(&mut cursor) {
            match arg.kind() {
                "comment" => {}
                "keyword_argument" => {
                    let name = arg.child_by_field_name("name")?;
                    keywords.push((
                        &self.source[name.byte_range()],
                        arg.child_by_field_name("value")?,
                    ));
                }
                "list_splat" | "dictionary_splat" => return None,
                _ => positional.push(arg),
            }
        }
        let mut pattern = String::new();
        let mut args = Vec::new();
        let mut next = 0;
        let mut last_end = 0;
        for cap in FIELD_REGEX.captures_iter(&text) {
            let whole = cap.get(0).unwrap();
            pattern.push_str(&text[last_end..whole.start()]);
            last_end = whole.end();
            let Some(field) = cap.get(1) else {
                match whole.as_str() {
                    "{{" => pattern.push('{'),
                    "}}" => pattern.push('}'),
                    // A lone brace is a nested format spec or an error.
                    "{" | "}" => return None,
                    escape => pattern.push_str(escape),
                }
                continue;
            };
            // Split off the conversion and format spec, like the `!r` and `:>10` in `{0!r:>10}`.
            let field = field.as_str();
            let (field, spec) = field.split_once(':').unwrap_or((field, ""));
            let (field, conversion) = field
                .split_once('!')
                .map_or((field, false), |(f, _)| (f, true));
            let split = field.find(['.', '[']).unwrap_or(field.len());
            let (name, rest) = field.split_at(split);
            let value = if name.is_empty() {
                next += 1;
                positional.get(next - 1).copied()
            } else if let Ok(index) = name.parse::<usize>() {
                positional.get(index).copied()
            } else {
                keywords.iter().find(|(kw, _)| *kw == name).map(|(_, v)| *v)
            }?;
            pattern.push_str("%s");
            let FormatArgument::Named(base) = self.python_arg(value) else {
                unreachable!()
            };
            let expr = format!("{base}{}", Self::python_field_accessors(rest));
            // The spec decides how the value is printed, like `{:x}` for an integer, and a
            // conversion like `!r` prints its repr().
            let kind = if conversion {
                ValueKind::Any
            } else if !spec.is_empty() {
                ValueKind::from_format_spec(spec)
            } else if !rest.is_empty() {
                ValueKind::Any
            } else {
                self.value_kind(value)
            };
            args.push((FormatArgument::Named(expr), kind));
        }
        pattern.push_str(&text[last_end..]);
        Some((pattern, args))
    }

    fn python_arg(&self, node: Node) -> FormatArgument {
        let node = Self::python_unparenthesize(node);
        FormatArgument::Named(self.source[node.byte_range()].trim().to_string())
    }

    /// Strip the parentheses around an expression, like `(x)`.
    fn python_unparenthesize(mut node: Node) -> Node {
        while node.kind() == "parenthesized_expression" {
            let mut cursor = node.walk();
            let Some(inner) = node
                .named_children(&mut cursor)
                .find(|n| n.kind() != "comment")
            else {
                break;
            };
            node = inner;
        }
        node
    }

    /// Convert the accessors of a `str.format()` field, like the `.name[key][0]` in
    /// `{0.name[key][0]}`, into Python.  An index that is not a number is a string key.
    fn python_field_accessors(accessors: &str) -> String {
        let mut retval = String::new();
        let mut rest = accessors;
        while let Some(start) = rest.find('[') {
            let Some(len) = rest[start..].find(']') else {
                break;
            };
            let key = &rest[start + 1..start + len];
            retval.push_str(&rest[..=start]);
            if key.parse::<usize>().is_ok() {
                retval.push_str(key);
            } else {
                retval.push_str(&format!("'{key}'"));
            }
            retval.push(']');
            rest = &rest[start + len + 1..];
        }
        retval.push_str(rest);
        retval
    }

    /// Convert a Kotlin string-literal, like `"Hello $name, {}"`, into the contents of a single
    /// string-literal with SLF4J placeholders.  Templates are replaced with placeholders and, if
    /// there are any, the returned arguments list every placeholder in order.  Returns None for
    /// raw strings since they are usually trimmed with `trimIndent()`.
    fn kotlin_pattern(&self, node: Node) -> Option<(String, Vec<Arg>)> {
        let (pattern, mut args, interpolated) = self.kotlin_template(node)?;
        if !interpolated {
            // The placeholders will be found when building the matcher.
            args.clear();
        }
        Some((pattern, args))
    }

    /// Convert a Kotlin string-literal into a pattern and the arguments for all of its
    /// placeholders.  Also returns whether the string has any templates.
    fn kotlin_template(&self, node: Node) -> Option<(String, Vec<Arg>, bool)> {
        static TEMPLATE_REGEX: LazyLock<Regex> =
            LazyLock::new(|| Regex::new(r#"\$([a-zA-Z_][a-zA-Z0-9_]*)|\{[^{}]*}"#).unwrap());

        if self.source[node.byte_range()].starts_with("\"\"\"") {
            return None;
        }
        let mut pattern = String::new();
        let mut args = Vec::new();
        let mut interpolated = false;
        // The grammar splits the text of a `$name` template from the name, so the adjacent
        // pieces of content are joined before looking for templates.
        let mut content = String::new();
        let flush = |content: &mut String,
                     pattern: &mut String,
                     args: &mut Vec<Arg>,
                     interpolated: &mut bool| {
            let mut last_end = 0;
            for cap in TEMPLATE_REGEX.captures_iter(content) {
                let whole = cap.get(0).unwrap();
                pattern.push_str(&content[last_end..whole.start()]);
                match cap.get(1) {
                    Some(name) => {
                        pattern.push_str("{}");
                        args.push((
                            FormatArgument::Named(name.as_str().to_string()),
                            ValueKind::Any,
                        ));
                        *interpolated = true;
                    }
                    None => {
                        pattern.push_str(whole.as_str());
                        args.push((FormatArgument::Placeholder, ValueKind::Any));
                    }
                }
                last_end = whole.end();
            }
            pattern.push_str(&content[last_end..]);
            content.clear();
        };
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            let text = &self.source[child.byte_range()];
            match child.kind() {
                "string_content" => content.push_str(text),
                "escape_sequence" => {
                    flush(&mut content, &mut pattern, &mut args, &mut interpolated);
                    // The escapes are decoded when building the matcher.
                    pattern.push_str(text);
                }
                "interpolation" => {
                    flush(&mut content, &mut pattern, &mut args, &mut interpolated);
                    pattern.push_str("{}");
                    interpolated = true;
                    let expr = child.named_child(0).unwrap_or(child);
                    args.push((
                        FormatArgument::Named(self.normalized_text(expr)),
                        self.value_kind(expr),
                    ));
                }
                _ => {}
            }
        }
        flush(&mut content, &mut pattern, &mut args, &mut interpolated);
        Some((pattern, args, interpolated))
    }

    /// Convert a Kotlin string concatenation, like `"count=$count " + "size=" + size`, into
    /// the contents of a single string-literal.  Kotlin has no `+` that takes a number on the
    /// left and a string on the right, so a concatenation always starts with a string.
    /// Returns None if the expression is not a concatenation starting with a string-literal.
    fn kotlin_concat_pattern(&self, node: Node) -> Option<(String, Vec<Arg>)> {
        let mut operands = vec![];
        let mut curr = node;
        while curr.kind() == "binary_expression"
            && curr
                .child_by_field_name("operator")
                .is_some_and(|op| op.kind() == "+")
        {
            operands.push(curr.child_by_field_name("right")?);
            curr = curr.child_by_field_name("left")?;
        }
        if curr.kind() != "string_literal" {
            return None;
        }
        operands.push(curr);
        let mut pattern = String::new();
        let mut args = vec![];
        let mut interpolated = false;
        for operand in operands.into_iter().rev() {
            if operand.kind() == "string_literal" {
                let (piece, piece_args, piece_interpolated) = self.kotlin_template(operand)?;
                pattern.push_str(&piece);
                args.extend(piece_args);
                interpolated |= piece_interpolated;
            } else {
                pattern.push_str("{}");
                args.push((
                    FormatArgument::Named(self.normalized_text(operand)),
                    self.value_kind(operand),
                ));
                interpolated = true;
            }
        }
        if !interpolated {
            args.clear();
        }
        Some((pattern, args))
    }

    /// Get the node that stands in for the log statement when finding its function and block.
    /// The message in a Kotlin lambda, like `logger.info { "..." }`, is inside a block of its
    /// own, so the lambda is used instead.
    fn statement_anchor(node: Node) -> Node {
        match node.parent() {
            Some(parent) if parent.kind() == "lambda_literal" => parent.parent().unwrap_or(parent),
            _ => node,
        }
    }

    /// Convert a Java or C++ string concatenation, like `"user " + name + " logged in"`, into
    /// the contents of a single string-literal.  The non-literal operands are replaced with
    /// placeholders whose argument is the operand's expression.  Returns None if the expression
    /// is not a concatenation involving a string-literal.
    fn concat_pattern(&self, node: Node) -> Option<(String, Vec<Arg>)> {
        // In C, adding to a string-literal is always pointer arithmetic.
        if self.source_language == SourceLanguage::C {
            return None;
        }
        let mut pieces = Vec::new();
        if !self.flatten_concat(node, &mut pieces) {
            return None;
        }
        // In C++, adding a number to a string-literal is pointer arithmetic, like `"abc" + 1`.
        if self.source_language == SourceLanguage::Cpp
            && pieces.iter().any(|piece| {
                matches!(piece, ConcatPiece::Expr(expr)
                    if matches!(expr.kind(), "number_literal" | "char_literal"))
            })
        {
            return None;
        }
        let mut pattern = String::new();
        let mut args = Vec::new();
        for piece in pieces {
            match piece {
                ConcatPiece::Literal(text) => {
                    let language = self.source_language;
                    for cap in language.get_placeholder_regex().captures_iter(&text) {
                        args.push((language.captures_to_format_arg(&cap), ValueKind::Any));
                    }
                    pattern.push_str(&text);
                }
                ConcatPiece::Expr(expr) => {
                    pattern.push_str("{}");
                    args.push((
                        FormatArgument::Named(
                            self.source[expr.start_byte()..expr.end_byte()].to_string(),
                        ),
                        self.value_kind(expr),
                    ));
                }
            }
        }
        Some((pattern, args))
    }

    /// Split a tree of `+` expressions into its pieces.  Returns true if any piece is a
    /// string-literal.
    fn flatten_concat(&self, node: Node<'a>, pieces: &mut Vec<ConcatPiece<'a>>) -> bool {
        if let Some(text) = self.string_contents(node) {
            pieces.push(ConcatPiece::Literal(text));
            return true;
        }
        let is_plus = node.kind() == "binary_expression"
            && node
                .child_by_field_name("operator")
                .is_some_and(|op| op.kind() == "+");
        if !is_plus {
            pieces.push(ConcatPiece::Expr(node));
            return false;
        }
        let (Some(left), Some(right)) = (
            node.child_by_field_name("left"),
            node.child_by_field_name("right"),
        ) else {
            pieces.push(ConcatPiece::Expr(node));
            return false;
        };
        // The '+' operator is left-associative, so anything before the first string-literal
        // could be numeric addition, like `a + b + " total"`.  In that case, the left side has
        // to be treated as a single value.
        let mut left_pieces = Vec::new();
        if self.flatten_concat(left, &mut left_pieces) {
            pieces.append(&mut left_pieces);
        } else {
            pieces.push(ConcatPiece::Expr(left));
            if self.string_contents(right).is_none() {
                // Neither side is a string, so this is just addition.
                pieces.pop();
                pieces.push(ConcatPiece::Expr(node));
                return false;
            }
        }
        match self.string_contents(right) {
            Some(text) => pieces.push(ConcatPiece::Literal(text)),
            None => pieces.push(ConcatPiece::Expr(right)),
        }
        true
    }

    /// The contents of a regular Java string-literal, without the quotes.  Text blocks are not
    /// supported since their indentation is stripped by the compiler.  For C++, this is a
    /// string-literal without its prefix, like `u8`, or adjacent string-literals.
    fn string_contents(&self, node: Node) -> Option<Cow<'a, str>> {
        let text = &self.source[node.start_byte()..node.end_byte()];
        match (self.source_language, node.kind()) {
            (SourceLanguage::C | SourceLanguage::Cpp, "string_literal") => {
                let start = text.find('"')? + 1;
                let end = text.rfind('"')?;
                text.get(start..end).map(Cow::Borrowed)
            }
            (SourceLanguage::C | SourceLanguage::Cpp, "concatenated_string") => {
                // Only the contents are returned, so the arguments for any macros would be
                // lost.
                match self.concatenated_pattern(node)? {
                    (pattern, args) if args.is_empty() => Some(Cow::Owned(pattern)),
                    _ => None,
                }
            }
            (_, "string_literal") if !text.starts_with("\"\"\"") && text.len() >= 2 => {
                Some(Cow::Borrowed(&text[1..text.len() - 1]))
            }
            _ => None,
        }
    }

    /// Check if an argument of a log call looks like a message, so that only the first one is
    /// used.
    fn is_message_like(&self, node: Node<'a>) -> bool {
        matches!(
            node.kind(),
            "string_literal" | "concatenated_string" | "raw_string_literal"
        ) || (node.kind() == "binary_expression" && self.concat_pattern(node).is_some())
            || self.unwrap_message_call(node).is_some()
    }

    /// Check if an argument before `arg` is a message that matches `predicate`.
    fn follows_message(&self, arg: Node<'a>, predicate: impl Fn(Node<'a>) -> bool) -> bool {
        let mut prev = arg.prev_named_sibling();
        while let Some(node) = prev {
            if self.is_message_like(node) && predicate(node) {
                return true;
            }
            prev = node.prev_named_sibling();
        }
        false
    }

    /// Find the string-literal in a message that is built by another call, like
    /// `String.format("...", x)` in Java, or `fmt::format("...", x)` and gettext's `_("...")` in
    /// C++.  Returns None if the call is not one of those or its message is not a literal.
    fn unwrap_message_call(&self, call: Node<'a>) -> Option<WrappedMessage<'a>> {
        let (kind, args) = match (self.source_language, call.kind()) {
            (SourceLanguage::Java, "method_invocation") => {
                let object = call.child_by_field_name("object")?;
                let name = &self.source[call.child_by_field_name("name")?.byte_range()];
                let kind = match (&self.source[object.byte_range()], name) {
                    ("String" | "java.lang.String", "format") => MessageCall::Printf,
                    ("MessageFormat" | "java.text.MessageFormat", "format") => MessageCall::Format,
                    _ => return None,
                };
                (kind, call.child_by_field_name("arguments")?)
            }
            (SourceLanguage::C | SourceLanguage::Cpp, "call_expression") => {
                let function = &self.source[call.child_by_field_name("function")?.byte_range()];
                let kind = match function {
                    "format" | "fmt::format" | "std::format" => MessageCall::Format,
                    "_" | "N_" | "gettext" | "tr" | "fmt::runtime" => MessageCall::Passthrough,
                    _ => return None,
                };
                (kind, call.child_by_field_name("arguments")?)
            }
            _ => return None,
        };
        let mut cursor = args.walk();
        let mut named = args
            .named_children(&mut cursor)
            .filter(|arg| !arg.kind().contains("comment"));
        let mut first = named.next()?;
        if kind == MessageCall::Printf
            && matches!(
                first.kind(),
                "identifier" | "field_access" | "method_invocation"
            )
            && self.source[first.byte_range()]
                .to_ascii_lowercase()
                .contains("locale")
        {
            // The Locale, like `String.format(Locale.ROOT, "...", x)`.  Otherwise, the format
            // string is not a literal, like `String.format(FORMAT, x)`.
            first = named.next()?;
        }
        let literal_kinds: &[&str] = match self.source_language {
            SourceLanguage::C | SourceLanguage::Cpp => &[
                "string_literal",
                "concatenated_string",
                "raw_string_literal",
                "binary_expression",
            ],
            _ => &["string_literal", "binary_expression"],
        };
        let literal = if literal_kinds.contains(&first.kind()) {
            first
        } else {
            // A translated format string, like `fmt::format(_("..."), x)`.
            let inner = self.unwrap_message_call(first)?;
            if inner.args_anchor != first {
                return None;
            }
            inner.literal
        };
        Some(WrappedMessage {
            literal,
            // A translation does not do any formatting, so the arguments for the placeholders
            // follow the call itself.
            args_anchor: if kind == MessageCall::Passthrough {
                call
            } else {
                first
            },
            printf: kind == MessageCall::Printf,
        })
    }

    /// Check if a call has a log level, either from the name of the call or from one of the
    /// `leading_args` before the message.
    fn has_level(call_name: Option<&str>, leading_args: &[String]) -> bool {
        leading_args
            .iter()
            .any(|arg| LogLevel::from_level_arg(arg).is_some())
            || call_name.and_then(LogLevel::from_name).is_some()
    }

    /// Check if a C or C++ call is known to use its argument as a message, like a `throw` or
    /// `snprintf()`, although it is not logging.
    fn is_c_message_call(call_name: Option<&str>) -> bool {
        call_name.is_some_and(|name| MessageCategory::from_c_call(name).is_some())
    }

    fn in_function_body(node: Node) -> bool {
        let mut curr = node.parent();
        while let Some(parent) = curr {
            if parent.kind() == "compound_statement" {
                return true;
            }
            curr = parent.parent();
        }
        false
    }

    /// Collect the arguments before the format string that might be a log level, like the
    /// `LOG_ERR` in `syslog(LOG_ERR, "...")` or the `Level::Warn` in `log!(Level::Warn, "...")`.
    fn leading_args(&self, node: Node) -> Vec<String> {
        let mut args = Vec::new();
        match node.parent().map(|p| p.kind()) {
            Some("argument_list") => {
                let mut prev = node.prev_named_sibling();
                while let Some(arg) = prev {
                    // Only names can be level constants, other arguments like string literals
                    // could contain level words that aren't relevant.
                    if matches!(
                        arg.kind(),
                        "identifier"
                            | "qualified_identifier"
                            | "field_expression"
                            | "field_access"
                            | "attribute"
                    ) {
                        args.push(self.source[arg.byte_range()].to_string());
                    }
                    prev = arg.prev_named_sibling();
                }
                args.reverse();
            }
            Some("token_tree") => {
                // Macro arguments are a flat list of tokens, so split the text before the
                // format string on commas.
                let parent = node.parent().unwrap();
                let start = parent.start_byte() + 1;
                if start < node.start_byte() {
                    args.extend(
                        self.source[start..node.start_byte()]
                            .split(',')
                            .map(str::trim)
                            .filter(|arg| !arg.is_empty() && !arg.contains('"'))
                            .map(str::to_string),
                    );
                }
            }
            _ => {}
        }
        args
    }

    /// Get an ID for the innermost lexical block enclosing the given node, which is the block's
    /// start byte.  A statement that is the body of an `if`, loop, etc. without braces is
    /// treated as its own block.  A `finally` block gets the ID of its `try` body.  A node that
    /// is not in a block gets the root's ID of zero.
    fn block_id(&self, node: Node) -> u32 {
        let block_kinds: &[&str] = match self.source_language {
            SourceLanguage::Rust => &["block", "match_arm"],
            SourceLanguage::Java => &[
                "block",
                "constructor_body",
                "switch_block_statement_group",
                "switch_rule",
                "lambda_expression",
            ],
            SourceLanguage::C | SourceLanguage::Cpp => &["compound_statement", "case_statement"],
            SourceLanguage::Python => &["block"],
            SourceLanguage::Kotlin => &["block", "lambda_literal", "when_entry"],
        };
        let mut curr = node.parent();
        while let Some(candidate) = curr {
            if block_kinds.contains(&candidate.kind()) {
                // A `finally` runs whenever the `try` body does, so it shares the body's ID.
                let try_body = candidate
                    .parent()
                    .filter(|parent| {
                        matches!(
                            parent.kind(),
                            "finally_clause" | "seh_finally_clause" | "finally_block"
                        )
                    })
                    .and_then(|finally| finally.parent())
                    .and_then(|try_stmt| {
                        // Kotlin's grammar has no field for the body.
                        try_stmt.child_by_field_name("body").or_else(|| {
                            let mut cursor = try_stmt.walk();
                            let body = try_stmt
                                .named_children(&mut cursor)
                                .find(|child| child.kind() == "block");
                            body
                        })
                    });
                return try_body.unwrap_or(candidate).start_byte() as u32;
            }
            let parent = candidate.parent();
            // The branches of `#if`/`#else` are not blocks, so a statement in either one
            // belongs to the enclosing block.
            let is_unbraced_body = parent.is_some_and(|parent| {
                if self.source_language == SourceLanguage::Kotlin {
                    // Kotlin's grammar has no fields for the bodies, just the condition.
                    return matches!(
                        parent.kind(),
                        "if_expression"
                            | "for_statement"
                            | "while_statement"
                            | "do_while_statement"
                    ) && parent.child_by_field_name("condition") != Some(candidate);
                }
                !parent.kind().starts_with("preproc_")
                    && ["consequence", "alternative", "body"]
                        .iter()
                        .any(|field| parent.child_by_field_name(field) == Some(candidate))
            });
            if is_unbraced_body {
                return candidate.start_byte() as u32;
            }
            curr = parent;
        }
        0
    }

    /// Get the name of the function, or other item, that contains the given node, along with
    /// its name qualified by the namespaces, classes, and modules that contain it, like
    /// `net::Server::handle` in C++ or `com.example.Server.handle` in Java.  The name is the
    /// innermost component of the qualified name, except for C++ functions, which are named by
    /// their whole declarator.
    fn names(&self, node: Node) -> (String, String) {
        let field = |node: Node, name: &str| {
            node.child_by_field_name(name)
                .map(|child| self.normalized_text(child))
        };
        // The components from the innermost outward.
        let mut components = Vec::new();
        let mut name = None;
        let mut in_class = false;
        let mut curr = node.parent();
        while let Some(parent) = curr {
            if parent.kind() == "attribute_item" {
                // An attribute is a sibling of the item it is attached to.
                let mut item = parent.next_named_sibling();
                while let Some(next) = item.filter(|next| {
                    matches!(
                        next.kind(),
                        "attribute_item" | "line_comment" | "block_comment"
                    )
                }) {
                    item = next.next_named_sibling();
                }
                if item.is_some() {
                    curr = item;
                    continue;
                }
            }
            let component = match (self.source_language, parent.kind()) {
                (
                    SourceLanguage::Rust,
                    "function_item" | "mod_item" | "trait_item" | "static_item" | "const_item",
                ) => field(parent, "name"),
                (SourceLanguage::Rust, "impl_item") => {
                    let ty = field(parent, "type");
                    match (ty, field(parent, "trait")) {
                        (Some(ty), Some(tr)) => Some(format!("<{} as {}>", ty, tr)),
                        (ty, _) => ty,
                    }
                }
                (
                    SourceLanguage::Java,
                    "method_declaration"
                    | "constructor_declaration"
                    | "compact_constructor_declaration",
                ) => field(parent, "name"),
                (
                    SourceLanguage::Java,
                    "class_declaration"
                    | "interface_declaration"
                    | "enum_declaration"
                    | "record_declaration"
                    | "annotation_type_declaration",
                ) => {
                    in_class = true;
                    field(parent, "name")
                }
                (SourceLanguage::C | SourceLanguage::Cpp, "function_definition") => {
                    self.cpp_function_name(parent)
                }
                // A variable at namespace scope, like one initialized by a lambda.
                (SourceLanguage::C | SourceLanguage::Cpp, "declaration")
                    if parent.parent().is_some_and(|scope| {
                        matches!(scope.kind(), "translation_unit" | "declaration_list")
                    }) =>
                {
                    self.cpp_declaration_name(parent)
                }
                (SourceLanguage::Cpp, "namespace_definition") => Some(
                    field(parent, "name").unwrap_or_else(|| "(anonymous namespace)".to_string()),
                ),
                (
                    SourceLanguage::Cpp,
                    "class_specifier" | "struct_specifier" | "union_specifier",
                ) => field(parent, "name"),
                (SourceLanguage::Python, "function_definition") => {
                    // Follow __qualname__, which marks names defined inside a function.
                    if !components.is_empty() {
                        components.push("<locals>".to_string());
                    }
                    field(parent, "name")
                }
                (SourceLanguage::Python, "class_definition") => field(parent, "name"),
                (SourceLanguage::Kotlin, "function_declaration") => field(parent, "name"),
                (SourceLanguage::Kotlin, "class_declaration" | "object_declaration") => {
                    in_class = true;
                    field(parent, "name")
                }
                (SourceLanguage::Kotlin, "companion_object") => {
                    Some(field(parent, "name").unwrap_or_else(|| "Companion".to_string()))
                }
                (SourceLanguage::Kotlin, "secondary_constructor" | "anonymous_initializer") => {
                    // Named after the class, like a Java constructor.
                    parent
                        .parent()
                        .and_then(|body| body.parent())
                        .and_then(|class| field(class, "name"))
                }
                _ => None,
            };
            if name.is_none() {
                name = match (self.source_language, parent.kind()) {
                    // Named by the function declarator, without the pointer or reference for the
                    // return type, like the `*` in `struct node *insert(...)`.
                    (SourceLanguage::C | SourceLanguage::Cpp, "function_definition") => {
                        let decl = parent.child_by_field_name("declarator");
                        decl.map(|decl| {
                            self.normalized_text(
                                Self::cpp_function_declarator(decl).unwrap_or(decl),
                            )
                        })
                    }
                    _ => component.clone(),
                };
            }
            components.extend(component);
            curr = parent.parent();
        }
        match self.source_language {
            SourceLanguage::Java => {
                if !in_class && !components.is_empty() {
                    // A method in an implicitly declared class, which is named after the file.
                    components.extend(
                        Path::new(self.filename)
                            .file_stem()
                            .map(|stem| stem.to_string_lossy().to_string()),
                    );
                }
                components.extend(self.java_package());
            }
            SourceLanguage::Kotlin => {
                if !in_class && !components.is_empty() {
                    // A top-level function is in the class generated for the file.
                    components.push(self.kotlin_file_class());
                }
                components.extend(self.java_package());
            }
            SourceLanguage::Python if components.is_empty() => {
                components.push("<module>".to_string())
            }
            _ => {}
        }
        components.reverse();
        let separator = match self.source_language {
            SourceLanguage::Rust | SourceLanguage::C | SourceLanguage::Cpp => "::",
            SourceLanguage::Java | SourceLanguage::Python | SourceLanguage::Kotlin => ".",
        };
        let name = name.unwrap_or_else(|| match self.source_language {
            SourceLanguage::Python => "<module>".to_string(),
            // Nothing encloses the statement, so name it after the file.
            _ => Path::new(self.filename)
                .file_stem()
                .map_or(String::new(), |stem| stem.to_string_lossy().to_string()),
        });
        (name, components.join(separator))
    }

    /// Get the name of the variable declared by a C++ declaration, like `init` in
    /// `auto init = [] { ... };`.
    fn cpp_declaration_name(&self, node: Node) -> Option<String> {
        let mut curr = node.child_by_field_name("declarator")?;
        while let Some(next) = curr.child_by_field_name("declarator") {
            curr = next;
        }
        Some(self.normalized_text(curr))
    }

    /// The name to use for a call whose name is not the name in the source, see
    /// `rust_call_name()` and `exception_call_name()`.
    fn special_call_name(&self, name: Node) -> Option<String> {
        match self.source_language {
            SourceLanguage::Rust => self.rust_call_name(name),
            SourceLanguage::Cpp | SourceLanguage::Java | SourceLanguage::Python => {
                self.exception_call_name(name)
            }
            _ => None,
        }
    }

    /// The name to use for a call whose message is used for an exception, like
    /// `throw std::runtime_error("...")` in C++, `throw new IllegalStateException("...")` in
    /// Java, or `raise ValueError("...")` in Python, which are named `throw std::runtime_error`,
    /// `throw IllegalStateException`, and `raise ValueError`, so they are not mistaken for a
    /// logging call with an error level.
    fn exception_call_name(&self, name: Node) -> Option<String> {
        let (call_kind, field, statement, keyword) = match self.source_language {
            SourceLanguage::Cpp => ("call_expression", "function", "throw_statement", "throw"),
            SourceLanguage::Java => (
                "object_creation_expression",
                "type",
                "throw_statement",
                "throw",
            ),
            SourceLanguage::Python => ("call", "function", "raise_statement", "raise"),
            _ => return None,
        };
        let call = name.parent().filter(|call| call.kind() == call_kind)?;
        if call.child_by_field_name(field)? != name || call.parent()?.kind() != statement {
            return None;
        }
        Some(format!("{keyword} {}", &self.source[name.byte_range()]))
    }

    /// The name to use for a Rust call whose name is not the name in the source.  An attribute,
    /// like thiserror's `#[error("...")]`, is named `#[error]` so it is not mistaken for the
    /// `error!` macro.  A `format!` that is the first argument of an error call, like
    /// `.context(format!("..."))` or `.with_context(|| format!("..."))`, is named after the call
    /// that consumes the message.  Any other `format!`, like the one in
    /// `names.push(format!("..."))`, keeps its name, since the message is only formatted.
    fn rust_call_name(&self, name: Node) -> Option<String> {
        let text = &self.source[name.byte_range()];
        let parent = name.parent()?;
        if parent.kind() == "attribute" {
            return Some(format!("#[{text}]"));
        }
        if text != "format" || parent.kind() != "macro_invocation" {
            return None;
        }
        let mut node = parent;
        let mut outer = node.parent()?;
        if outer.kind() == "block" && outer.parent()?.kind() == "closure_expression" {
            node = outer;
            outer = node.parent()?;
        }
        if outer.kind() == "closure_expression" {
            node = outer;
            outer = node.parent()?;
        }
        if outer.kind() != "arguments" || outer.named_child(0)? != node {
            return None;
        }
        let function = outer.parent()?.child_by_field_name("function")?;
        let consumer = match function.kind() {
            "field_expression" => function.child_by_field_name("field")?,
            "scoped_identifier" => function.child_by_field_name("name")?,
            "identifier" => function,
            _ => return None,
        };
        let consumer = &self.source[consumer.byte_range()];
        MessageCategory::is_rust_error_call(consumer).then(|| consumer.to_string())
    }

    /// Combine the string literals passed to `concat!`, like `("a ", "{}")`, into the contents
    /// of a single string literal.  Returns None if there is anything other than literals.
    fn rust_concat_pattern(&self, token_tree: Node) -> Option<String> {
        let mut retval = String::new();
        let mut cursor = token_tree.walk();
        for token in token_tree.children(&mut cursor) {
            match token.kind() {
                "(" | ")" | "," => {}
                "string_literal" => {
                    let text = &self.source[token.byte_range()];
                    retval.push_str(text.strip_prefix('"')?.strip_suffix('"')?);
                }
                _ => return None,
            }
        }
        Some(retval)
    }

    /// Get the name of a C++ function from its declarator, without the parameters or
    /// qualifiers, like `Foo::bar` from `*Foo::bar(int x) const`.
    fn cpp_function_name(&self, node: Node) -> Option<String> {
        let decl = node.child_by_field_name("declarator")?;
        if let Some(func) = Self::cpp_function_declarator(decl) {
            return func
                .child_by_field_name("declarator")
                .map(|name| self.normalized_text(name));
        }
        // Something unusual, like a conversion operator, so use everything before the parameters.
        let text = self.normalized_text(decl);
        Some(text.split('(').next().unwrap_or(&text).trim().to_string())
    }

    /// Find the function declarator in the declarator of a function definition.  Pointer and
    /// reference declarators for the return type wrap it.
    fn cpp_function_declarator(decl: Node) -> Option<Node> {
        let mut curr = decl;
        loop {
            if curr.kind() == "function_declarator" {
                return Some(curr);
            }
            curr = curr
                .child_by_field_name("declarator")
                .or_else(|| curr.named_child(curr.named_child_count().checked_sub(1)?))?;
        }
    }

    /// Get the package declared in a Java or Kotlin file, like `com.example`.
    fn java_package(&self) -> Option<String> {
        let root = self.tree.root_node();
        let mut cursor = root.walk();
        let package = root
            .named_children(&mut cursor)
            .find(|child| matches!(child.kind(), "package_declaration" | "package_header"))?;
        let mut cursor = package.walk();
        let name = package.named_children(&mut cursor).find(|child| {
            matches!(
                child.kind(),
                "scoped_identifier" | "identifier" | "qualified_identifier"
            )
        })?;
        Some(self.source[name.byte_range()].split_whitespace().collect())
    }

    /// Get the name of the class that holds the top-level functions in a Kotlin file, which is
    /// set by `@file:JvmName("...")` or is derived from the file name, like `MainKt` for
    /// `main.kt`.
    fn kotlin_file_class(&self) -> String {
        let root = self.tree.root_node();
        let mut cursor = root.walk();
        let jvm_name = root
            .named_children(&mut cursor)
            .filter(|child| child.kind() == "file_annotation")
            .find_map(|annotation| {
                let text = &self.source[annotation.byte_range()];
                let args = text
                    .split_once("JvmName")?
                    .1
                    .trim_start()
                    .strip_prefix('(')?;
                let name = args.trim_start().strip_prefix('"')?;
                Some(name.split('"').next()?.to_string())
            });
        if let Some(name) = jvm_name {
            return name;
        }
        let stem = Path::new(self.filename)
            .file_stem()
            .map(|stem| stem.to_string_lossy().to_string())
            .unwrap_or_default();
        let mut retval: String = stem
            .chars()
            .enumerate()
            .map(|(index, c)| match c {
                _ if index == 0 => c.to_ascii_uppercase(),
                _ if c.is_alphanumeric() || c == '_' => c,
                _ => '_',
            })
            .collect();
        retval.push_str("Kt");
        retval
    }

    /// Get the text of a node with runs of whitespace collapsed into a single space, since a
    /// name can be split across lines.
    fn value_kind(&self, node: Node) -> ValueKind {
        ValueKind::from_node(self.source_language, node, self.source)
    }

    fn normalized_text(&self, node: Node) -> String {
        self.source[node.byte_range()]
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    }
}

#[derive(Copy, Clone, PartialEq)]
enum MessageCall {
    /// `String.format()`, which uses printf-style conversions.
    Printf,
    /// A call that formats with the language's usual placeholders, like `fmt::format()`.
    Format,
    /// A call that returns the message as-is for formatting elsewhere, like gettext's `_()` or
    /// `fmt::runtime()`.
    Passthrough,
}

/// A message that is built by another call, like `String.format("...", x)`.
struct WrappedMessage<'a> {
    /// The format string.
    literal: Node<'a>,
    /// The node whose following siblings are the arguments for the placeholders.
    args_anchor: Node<'a>,
    /// True if the placeholders are printf-style conversions in a Java message.
    printf: bool,
}

/// Convert the printf-style conversions in a Java `String.format()` message, like `%s` or
/// `%.2f`, into the `{}` placeholders that are used for the other Java messages.  The returned
/// arguments give the index of the value for each placeholder, since conversions can refer to
/// them out of order, like `%2$s` or `%<s`.
fn printf_to_placeholders(text: &str) -> (String, Vec<Arg>) {
    static CONVERSION_REGEX: LazyLock<Regex> = LazyLock::new(|| {
        Regex::new(r"%(?:(\d+)\$)?([-#+ 0,(<]*)\d*(?:\.\d+)?(?:[tT][a-zA-Z]|[a-zA-Z%])|[{}]")
            .unwrap()
    });
    let mut args = Vec::new();
    // The index of the next ordinary conversion and of the last value used.
    let mut next = 0;
    let mut last = None;
    let pattern = CONVERSION_REGEX.replace_all(text, |caps: &regex::Captures| {
        let index = match &caps[0] {
            "%%" => return "%".to_string(),
            "%n" => return "\\n".to_string(),
            // A literal brace would otherwise look like a placeholder, so use an escape.
            "{" => return "\\u007b".to_string(),
            "}" => return "\\u007d".to_string(),
            _ if caps[2].contains('<') => last,
            _ => match caps.get(1) {
                Some(index) => index
                    .as_str()
                    .parse::<usize>()
                    .ok()
                    .and_then(|i| i.checked_sub(1)),
                None => {
                    next += 1;
                    Some(next - 1)
                }
            },
        };
        last = index;
        args.push((
            index.map_or(FormatArgument::Placeholder, FormatArgument::Positional),
            ValueKind::Any,
        ));
        "{}".to_string()
    });
    (pattern.into_owned(), args)
}

enum ConcatPiece<'a> {
    Literal(Cow<'a, str>),
    Expr(Node<'a>),
}

/// Check for a format macro from <cinttypes>, like PRIu64 or SCNd32.
fn is_inttypes_macro(text: &str) -> bool {
    (text.starts_with("PRI") || text.starts_with("SCN")) && is_identifier(text)
}

/// Check if a printf-style format ends in a conversion specification that is not finished,
/// like the `%-10` in `"%-10" G_GINT64_FORMAT`.
fn ends_in_open_conversion(format: &str) -> bool {
    let mut open = false;
    for c in format.chars() {
        if open {
            open = matches!(c, '-' | '+' | ' ' | '#' | '0'..='9' | '\'' | '.' | '*');
        } else if c == '%' {
            open = true;
        }
    }
    open
}

fn is_identifier(text: &str) -> bool {
    text.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_')
        && text.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
}

#[cfg(test)]
mod test {
    use super::SourceQuery;
    use tree_sitter::Parser;

    fn mask(source: &str) -> Option<String> {
        let mut parser = Parser::new();
        parser
            .set_language(&tree_sitter_cpp::LANGUAGE.into())
            .unwrap();
        let tree = parser.parse(source, None).unwrap();
        SourceQuery::mask_preproc_conditionals(source, &tree)
    }

    #[test]
    fn test_mask_preproc_conditionals() {
        let source = "int f() {\n#ifdef A\n  return 1;\n#endif\n}\n";
        assert_eq!(
            mask(source).as_deref(),
            Some("int f() {\n        \n  return 1;\n      \n}\n")
        );
        assert_eq!(mask("int f() { return 1; }\n"), None);
    }

    #[test]
    fn test_rewrite_literal_macro_calls() {
        let rewrite = SourceQuery::rewrite_literal_macro_calls;
        assert_eq!(
            rewrite(r#"f(A("%d") " rows " B( "x" ) "y");"#).as_deref(),
            Some(r#"f(A "%d"  " rows " B  "x"   "y");"#)
        );
        // Chains of calls next to a string-literal.
        assert_eq!(
            rewrite(r#"f(A("a") B("b") "c");"#).as_deref(),
            Some(r#"f(A "a"  B "b"  "c");"#)
        );
        assert_eq!(
            rewrite(r#"f("a" A("b") B("c"));"#).as_deref(),
            Some(r#"f("a" A "b"  B "c" );"#)
        );
        // Calls that are valid as-is, or that are in a comment or literal.
        assert_eq!(rewrite(r#"f(_("a"), "b");"#), None);
        assert_eq!(
            rewrite("#include \"a.h\"\nTEST(\"a\")\nTEST(\"b\")\n"),
            None
        );
        assert_eq!(rewrite(r#"f("x A(\"a\") y"); // "a" B("b")"#), None);
        assert_eq!(
            rewrite(r#"/* "a" A("b") */ f('"', 1'000, R"(" B("c"))");"#),
            None
        );
        // An identifier that ends with an `R` is not the prefix of a raw string.
        assert_eq!(
            rewrite(r#"f(ANSI_CLEAR"x", c); g("a" A("b"));"#).as_deref(),
            Some(r#"f(ANSI_CLEAR"x", c); g("a" A "b" );"#)
        );
    }

    #[test]
    fn test_mask_preproc_conditionals_skips_literals() {
        let source = r#"/* note
#if FOO
*/
const char *s = R"(
#else
)";
"#;
        assert_eq!(mask(source), None);
    }
}
