use std::ops::Range;
use tree_sitter::{
    Language, Node, Parser, Point, Query, QueryCursor, Range as TSRange, StreamingIterator, Tree,
};

use crate::source_ref::FormatArgument;
use crate::CodeSource;

pub struct SourceQuery<'a> {
    pub source: &'a str,
    tree: Tree,
    language: Language,
}

pub(crate) struct QueryResult {
    pub kind: String,
    pub range: TSRange,
    pub name_range: Range<usize>,
    pub pattern: Option<String>,
    pub args: Vec<FormatArgument>,
    pub raw: bool,
    /// The text of the last capture before the format string, which is the name of the logging
    /// function/macro/method being called (e.g. `log::warn`, `logger.info`).
    pub call_name: Option<String>,
    /// The text of the arguments before the format string, which might include the log level,
    /// as in `syslog(LOG_ERR, "...")`.
    pub leading_args: Vec<String>,
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
        let tree = parser.parse(source, None).expect("source is parsable");
        SourceQuery {
            source,
            tree,
            language,
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
                match child.kind() {
                    "string_literal" | "string" => {
                        // only return results after the format string literal, other captures
                        // are not relevant.
                        got_string_literal = true;
                    }
                    _ => {
                        if !got_string_literal {
                            // remember the name of the logging call so the log level can be
                            // derived from it.
                            let range = capture.node.byte_range();
                            call_name = Some(self.source[range].to_string());
                            continue;
                        }
                    }
                }
                let mut arg_start: Option<(usize, Point)> = None;

                if filter_idx.is_none() || filter_idx.is_some_and(|f| f == capture.index) {
                    let qr_index = results.len();
                    results.push(QueryResult {
                        kind: capture.node.kind().to_string(),
                        range: capture.node.range(),
                        name_range: Self::find_fn_range(child),
                        pattern: None,
                        args: vec![],
                        raw: false,
                        call_name: call_name.clone(),
                        leading_args: self.leading_args(child),
                    });
                    let mut pattern = String::new();
                    if child.kind() == "string" {
                        // The Python tree-sitter outputs string nodes that contain details about
                        // the string, like interpolation expressions.
                        let mut child_cursor = child.walk();
                        for string_child in child.children(&mut child_cursor) {
                            let range = string_child.start_byte()..string_child.end_byte();
                            match string_child.kind() {
                                "string_start" => {
                                    // Check for a python raw string literal.
                                    if self.source[range].contains("r") {
                                        results[qr_index].raw = true;
                                    }
                                }
                                "string_content" => pattern.push_str(self.source[range].as_ref()),
                                "interpolation" => {
                                    // Swap in a Python placeholder for the interpolation
                                    // expression.
                                    pattern.push_str("%s");
                                    let expr =
                                        string_child.child_by_field_name("expression").unwrap();
                                    results[qr_index].args.push(FormatArgument::Named(
                                        self.source[expr.start_byte()..expr.end_byte()].to_string(),
                                    ))
                                }
                                _ => {}
                            }
                        }
                        results[qr_index].pattern = Some(pattern);
                    }
                    while let Some(next_child) = child.next_sibling() {
                        if matches!(next_child.kind(), "," | ")") {
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
                                        name_range: Self::find_fn_range(child),
                                        pattern: None,
                                        args: vec![],
                                        raw: false,
                                        call_name: None,
                                        leading_args: vec![],
                                    });
                                }
                            }
                            arg_start = Some((next_child.end_byte(), next_child.end_position()));
                        }
                        child = next_child;
                    }
                }
            }
        });

        results
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

    fn find_fn_range(node: Node) -> Range<usize> {
        // println!("node.kind()={:?}", node.kind());
        match node.kind() {
            "function_item" => {
                let range = node.child_by_field_name("name").unwrap().range();
                range.start_byte..range.end_byte
            }
            "function_definition" => {
                let range = if let Some(decl) = node.child_by_field_name("declarator") {
                    decl.range()
                } else if let Some(name) = node.child_by_field_name("name") {
                    name.range()
                } else {
                    unreachable!();
                };
                range.start_byte..range.end_byte
            }
            "method_declaration" => {
                let range = node.child_by_field_name("name").unwrap().range();
                range.start_byte..range.end_byte
            }
            "constructor_declaration" => {
                let range = node.child_by_field_name("name").unwrap().range();
                range.start_byte..range.end_byte
            }
            "class_declaration" => {
                let range = node.child_by_field_name("name").unwrap().range();
                range.start_byte..range.end_byte
            }
            "declaration_list" | "static_item" | "attribute_item" => {
                let range = node.range();
                range.start_byte..range.end_byte
            }
            _ => {
                if let Some(parent) = node.parent() {
                    if parent.kind() == "translation_unit" {
                        let range = parent.range();
                        return range.start_byte..range.end_byte;
                    }
                    Self::find_fn_range(parent)
                } else {
                    let range = node.range();

                    range.start_byte..range.end_byte
                }
            }
        }
    }
}
