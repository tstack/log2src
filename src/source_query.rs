use std::ops::Range;
use std::path::Path;
use tree_sitter::{
    Language, Node, Parser, Point, Query, QueryCursor, Range as TSRange, StreamingIterator, Tree,
};

use crate::source_ref::FormatArgument;
use crate::{CodeSource, SourceLanguage};

pub struct SourceQuery<'a> {
    pub source: &'a str,
    filename: &'a str,
    tree: Tree,
    language: Language,
    source_language: SourceLanguage,
}

pub(crate) struct QueryResult {
    pub kind: String,
    pub range: TSRange,
    pub name_range: Range<usize>,
    pub qualified_name: String,
    pub pattern: Option<String>,
    pub args: Vec<FormatArgument>,
    pub raw: bool,
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
            filename: code.filename.as_str(),
            tree,
            language,
            source_language: code.info.language,
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
            for capture in m.captures {
                let mut child = capture.node;
                let mut concat_pattern = None;
                let mut concat_args = vec![];
                let mut kind = child.kind();
                if query.capture_names()[capture.index as usize] == "message-ref" {
                    // A log message that is a constant defined elsewhere, like
                    // `log.info(Messages.LOG_STARTING, name)`.
                    if !self.is_message_ref(child) {
                        break;
                    }
                    kind = "message_ref";
                }
                match kind {
                    "message_ref" => {
                        got_string_literal = true;
                    }
                    "string_literal" | "string" | "concatenated_string" | "binary_expression" => {
                        if self.source_language == SourceLanguage::Cpp
                            && !Self::in_function_body(child)
                        {
                            // Calls at file scope are macros like TEST_CASE("...") or
                            // _Pragma("...") and not log statements.
                            break;
                        }
                        if child.kind() == "concatenated_string"
                            && self.source_language == SourceLanguage::Cpp
                        {
                            match self.concatenated_pattern(child) {
                                Some(pattern) => concat_pattern = Some(pattern),
                                None => break,
                            }
                        }
                        if child.kind() == "binary_expression" {
                            match self.java_concat_pattern(child) {
                                Some((pattern, args)) => {
                                    concat_pattern = Some(pattern);
                                    concat_args = args;
                                }
                                None => break,
                            }
                        }
                        // only return results after the format string literal, other captures
                        // are not relevant.
                        got_string_literal = true;
                    }
                    _ => {
                        if !got_string_literal {
                            continue;
                        }
                    }
                }
                let mut arg_start: Option<(usize, Point)> = None;

                if filter_idx.is_none() || filter_idx.is_some_and(|f| f == capture.index) {
                    let qr_index = results.len();
                    results.push(QueryResult {
                        kind: kind.to_string(),
                        range: capture.node.range(),
                        name_range: Self::find_fn_range(child),
                        qualified_name: self.qualified_name(child),
                        pattern: concat_pattern.take(),
                        args: std::mem::take(&mut concat_args),
                        raw: false,
                    });
                    if self.source_language == SourceLanguage::Python
                        && matches!(child.kind(), "string" | "concatenated_string")
                    {
                        let (pattern, args) = self.python_pattern(child);
                        results[qr_index].pattern = Some(pattern);
                        results[qr_index].args = args;
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
                                        qualified_name: self.qualified_name(child),
                                        pattern: None,
                                        args: vec![],
                                        raw: false,
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
            .is_some_and(|next| match next.kind() {
                "string_literal" => true,
                // Only a concatenation with a string, not arithmetic like `MAX - count`.
                "binary_expression" => self.java_concat_pattern(next).is_some(),
                _ => false,
            });
        is_constant_name && !next_is_literal
    }

    /// Get the value of a Java string-literal or concatenation of string-literals, like the
    /// initializer for `static final String MSG = "abc " + "def";`.
    pub(crate) fn java_literal_value(&self, node: Node<'a>) -> Option<String> {
        let mut pieces = Vec::new();
        self.flatten_java_concat(node, &mut pieces);
        let mut retval = String::new();
        for piece in pieces {
            match piece {
                ConcatPiece::Literal(text) => retval.push_str(text),
                ConcatPiece::Expr(_) => return None,
            }
        }
        Some(retval)
    }

    /// Join the pieces of a C++ concatenated string, like `"abc " "def"`, into the contents of
    /// a single string-literal.  Returns None if a piece cannot be resolved, like a macro.
    fn concatenated_pattern(&self, node: Node) -> Option<String> {
        let mut pattern = String::new();
        let mut cursor = node.walk();
        for piece in node.named_children(&mut cursor) {
            let text = &self.source[piece.start_byte()..piece.end_byte()];
            match piece.kind() {
                "string_literal" => {
                    // Skip any prefix, like L or u8, and the quotes.
                    let start = text.find('"')? + 1;
                    let end = text.rfind('"')?;
                    pattern.push_str(text.get(start..end)?);
                }
                // The <cinttypes> macros, like "%" PRIu64, finish a conversion specification.
                // Some grammar versions wrap the macro name in an ERROR node.
                "identifier" | "ERROR" if is_inttypes_macro(text) => {
                    pattern.push('d');
                }
                _ => return None,
            }
        }
        Some(pattern)
    }

    /// Convert a Python string, or adjacent strings like `"abc " f"{x}"`, into the contents of a
    /// single non-raw string-literal.  Interpolations are replaced with placeholders and, if
    /// there are any, the returned arguments list every placeholder in order.
    fn python_pattern(&self, node: Node) -> (String, Vec<FormatArgument>) {
        let mut pattern = String::new();
        let mut args = Vec::new();
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
                        for cap in self
                            .source_language
                            .get_placeholder_regex()
                            .captures_iter(&content)
                        {
                            args.push(self.source_language.captures_to_format_arg(&cap));
                        }
                        pattern.push_str(&content);
                    }
                    "interpolation" => {
                        // Swap in a Python placeholder for the interpolation expression.
                        pattern.push_str("%s");
                        interpolated = true;
                        if let Some(expr) = string_child.child_by_field_name("expression") {
                            args.push(FormatArgument::Named(
                                self.source[expr.start_byte()..expr.end_byte()].to_string(),
                            ));
                        }
                    }
                    _ => {}
                }
            }
        }
        if !interpolated {
            // The placeholders will be found when building the matcher.
            args.clear();
        }
        (pattern, args)
    }

    /// Convert a Java string concatenation, like `"user " + name + " logged in"`, into the
    /// contents of a single string-literal.  The non-literal operands are replaced with
    /// placeholders whose argument is the operand's expression.  Returns None if the expression
    /// is not a concatenation involving a string-literal.
    fn java_concat_pattern(&self, node: Node) -> Option<(String, Vec<FormatArgument>)> {
        let mut pieces = Vec::new();
        if !self.flatten_java_concat(node, &mut pieces) {
            return None;
        }
        let mut pattern = String::new();
        let mut args = Vec::new();
        for piece in pieces {
            match piece {
                ConcatPiece::Literal(text) => {
                    let language = self.source_language;
                    for cap in language.get_placeholder_regex().captures_iter(text) {
                        args.push(language.captures_to_format_arg(&cap));
                    }
                    pattern.push_str(text);
                }
                ConcatPiece::Expr(expr) => {
                    pattern.push_str("{}");
                    args.push(FormatArgument::Named(
                        self.source[expr.start_byte()..expr.end_byte()].to_string(),
                    ));
                }
            }
        }
        Some((pattern, args))
    }

    /// Split a tree of `+` expressions into its pieces.  Returns true if any piece is a
    /// string-literal.
    fn flatten_java_concat(&self, node: Node<'a>, pieces: &mut Vec<ConcatPiece<'a>>) -> bool {
        if let Some(text) = self.java_string_contents(node) {
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
        if self.flatten_java_concat(left, &mut left_pieces) {
            pieces.append(&mut left_pieces);
        } else {
            pieces.push(ConcatPiece::Expr(left));
            if self.java_string_contents(right).is_none() {
                // Neither side is a string, so this is just addition.
                pieces.pop();
                pieces.push(ConcatPiece::Expr(node));
                return false;
            }
        }
        match self.java_string_contents(right) {
            Some(text) => pieces.push(ConcatPiece::Literal(text)),
            None => pieces.push(ConcatPiece::Expr(right)),
        }
        true
    }

    /// The contents of a regular Java string-literal, without the quotes.  Text blocks are not
    /// supported since their indentation is stripped by the compiler.
    fn java_string_contents(&self, node: Node) -> Option<&'a str> {
        if node.kind() != "string_literal" {
            return None;
        }
        let text = &self.source[node.start_byte()..node.end_byte()];
        if text.starts_with("\"\"\"") || text.len() < 2 {
            return None;
        }
        Some(&text[1..text.len() - 1])
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

    /// Get the name of the function enclosing the given node, qualified by the namespaces,
    /// classes, and modules that contain it, like `net::Server::handle` in C++ or
    /// `com.example.Server.handle` in Java.
    fn qualified_name(&self, node: Node) -> String {
        let field = |node: Node, name: &str| {
            node.child_by_field_name(name)
                .map(|child| self.normalized_text(child))
        };
        // The components from the innermost outward.
        let mut components = Vec::new();
        let mut in_class = false;
        let mut curr = node.parent();
        while let Some(parent) = curr {
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
                (SourceLanguage::Cpp, "function_definition") => self.cpp_function_name(parent),
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
                _ => None,
            };
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
            SourceLanguage::Python if components.is_empty() => {
                components.push("<module>".to_string())
            }
            _ => {}
        }
        components.reverse();
        let separator = match self.source_language {
            SourceLanguage::Rust | SourceLanguage::Cpp => "::",
            SourceLanguage::Java | SourceLanguage::Python => ".",
        };
        components.join(separator)
    }

    /// Get the name of a C++ function from its declarator, without the parameters or
    /// qualifiers, like `Foo::bar` from `*Foo::bar(int x) const`.
    fn cpp_function_name(&self, node: Node) -> Option<String> {
        let decl = node.child_by_field_name("declarator")?;
        let mut curr = decl;
        loop {
            if curr.kind() == "function_declarator" {
                return curr
                    .child_by_field_name("declarator")
                    .map(|name| self.normalized_text(name));
            }
            // Pointer and reference declarators wrap the function declarator.
            match curr
                .child_by_field_name("declarator")
                .or_else(|| curr.named_child(curr.named_child_count().checked_sub(1)?))
            {
                Some(next) => curr = next,
                None => break,
            }
        }
        // Something unusual, like a conversion operator, so use everything before the parameters.
        let text = self.normalized_text(decl);
        Some(text.split('(').next().unwrap_or(&text).trim().to_string())
    }

    /// Get the package declared in a Java file, like `com.example`.
    fn java_package(&self) -> Option<String> {
        let root = self.tree.root_node();
        let mut cursor = root.walk();
        let package = root
            .named_children(&mut cursor)
            .find(|child| child.kind() == "package_declaration")?;
        let mut cursor = package.walk();
        let name = package
            .named_children(&mut cursor)
            .find(|child| matches!(child.kind(), "scoped_identifier" | "identifier"))?;
        Some(self.source[name.byte_range()].split_whitespace().collect())
    }

    /// Get the text of a node with runs of whitespace collapsed into a single space, since a
    /// name can be split across lines.
    fn normalized_text(&self, node: Node) -> String {
        self.source[node.byte_range()]
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    }
}

enum ConcatPiece<'a> {
    Literal(&'a str),
    Expr(Node<'a>),
}

/// Check for a format macro from <cinttypes>, like PRIu64 or SCNd32.
fn is_inttypes_macro(text: &str) -> bool {
    (text.starts_with("PRI") || text.starts_with("SCN"))
        && text.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
}
