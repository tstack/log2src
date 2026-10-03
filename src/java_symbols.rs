//! Support for Java code that keeps its log messages in constants, like:
//!
//! ```java
//! class Messages {
//!     static final String LOG_STARTING = "Starting {} with " +
//!             "{} threads";
//! }
//! ...
//! log.info(Messages.LOG_STARTING, name, count);
//! ```
//!
//! The constants are usually in a different file from the log calls, so each file records the
//! constants it defines and, for each log call, the fully-qualified names the constant might
//! have.  After all the files are extracted, the references are resolved across the whole tree.

use crate::source_query::SourceQuery;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::ops::Range;
use tree_sitter::Node;

/// A `static final String` constant with a value that is known at compile time.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub(crate) struct StringConstant {
    /// The fully-qualified name, like `com.example.Messages.LOG_STARTING`.
    pub fqn: String,
    /// The contents of the string-literal(s), still in source form (e.g. escapes are intact).
    pub value: String,
}

/// A log call whose message is a reference to a constant.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub(crate) struct MessageRef {
    pub line_no: usize,
    pub end_line_no: usize,
    pub column: usize,
    /// The name of the enclosing function.
    pub name: String,
    /// The name of the enclosing function qualified by its package and classes.
    pub qualified_name: String,
    /// The reference as written in the source, like `Messages.LOG_STARTING`.
    pub text: String,
    pub vars: Vec<String>,
    /// The fully-qualified names the reference could refer to, in the order Java checks them.
    pub candidates: Vec<String>,
}

#[derive(Debug, PartialEq)]
struct Import {
    path: String,
    is_static: bool,
    wildcard: bool,
}

/// The names declared in, or imported into, a single Java file.
#[derive(Debug, Default)]
pub(crate) struct JavaSymbols {
    package: String,
    imports: Vec<Import>,
    /// The fully-qualified name of each class in the file and the bytes it covers.
    classes: Vec<(Range<usize>, String)>,
    pub constants: Vec<StringConstant>,
}

/// Remove whitespace from a qualified name since it is allowed between the components.
fn compact(text: &str) -> String {
    text.chars().filter(|c| !c.is_whitespace()).collect()
}

impl JavaSymbols {
    pub(crate) fn extract(query: &SourceQuery) -> Self {
        let mut retval = JavaSymbols::default();
        let root = query.root_node();
        let mut cursor = root.walk();
        for child in root.named_children(&mut cursor) {
            let text = &query.source[child.byte_range()];
            match child.kind() {
                "package_declaration" => {
                    retval.package =
                        compact(text.trim_start_matches("package").trim_end_matches(';'));
                }
                "import_declaration" => {
                    let body = text
                        .trim()
                        .trim_start_matches("import")
                        .trim_end_matches(';')
                        .trim();
                    let (is_static, body) = match body.strip_prefix("static") {
                        Some(rest) if rest.starts_with(char::is_whitespace) => (true, rest),
                        _ => (false, body),
                    };
                    let path = compact(body);
                    let (path, wildcard) = match path.strip_suffix(".*") {
                        Some(path) => (path.to_string(), true),
                        None => (path, false),
                    };
                    retval.imports.push(Import {
                        path,
                        is_static,
                        wildcard,
                    });
                }
                _ => {
                    let prefix = retval.package.clone();
                    retval.visit_type(query, child, &prefix);
                }
            }
        }
        retval
    }

    /// Record a class, interface, enum or record, its string constants, and its nested types.
    fn visit_type(&mut self, query: &SourceQuery, node: Node, prefix: &str) {
        let is_interface = match node.kind() {
            "class_declaration" | "enum_declaration" | "record_declaration" => false,
            "interface_declaration" => true,
            _ => return,
        };
        let (Some(name), Some(body)) = (
            node.child_by_field_name("name"),
            node.child_by_field_name("body"),
        ) else {
            return;
        };
        let name = &query.source[name.byte_range()];
        let fqn = if prefix.is_empty() {
            name.to_string()
        } else {
            format!("{}.{}", prefix, name)
        };
        self.classes.push((node.byte_range(), fqn.clone()));

        let mut members = vec![body];
        // The members of an enum come after the constants.
        let mut cursor = body.walk();
        members.extend(
            body.named_children(&mut cursor)
                .filter(|child| child.kind() == "enum_body_declarations"),
        );
        for member_list in members {
            let mut cursor = member_list.walk();
            for member in member_list.named_children(&mut cursor) {
                match member.kind() {
                    "field_declaration" => self.visit_field(query, member, &fqn, false),
                    // Fields in an interface are implicitly static and final.
                    "constant_declaration" => self.visit_field(query, member, &fqn, is_interface),
                    _ => self.visit_type(query, member, &fqn),
                }
            }
        }
    }

    fn visit_field(&mut self, query: &SourceQuery, node: Node, class: &str, implicit: bool) {
        let is_static_final = implicit
            || node
                .named_children(&mut node.walk())
                .find(|child| child.kind() == "modifiers")
                .is_some_and(|mods| {
                    let words: Vec<&str> =
                        query.source[mods.byte_range()].split_whitespace().collect();
                    words.contains(&"static") && words.contains(&"final")
                });
        let is_string = node.child_by_field_name("type").is_some_and(|ty| {
            matches!(
                compact(&query.source[ty.byte_range()]).as_str(),
                "String" | "java.lang.String"
            )
        });
        if !is_static_final || !is_string {
            return;
        }
        let mut cursor = node.walk();
        for declarator in node.children_by_field_name("declarator", &mut cursor) {
            let (Some(name), Some(value)) = (
                declarator.child_by_field_name("name"),
                declarator.child_by_field_name("value"),
            ) else {
                continue;
            };
            if let Some(value) = query.java_literal_value(value) {
                self.constants.push(StringConstant {
                    fqn: format!("{}.{}", class, &query.source[name.byte_range()]),
                    value,
                });
            }
        }
    }

    /// Get the fully-qualified names that a reference to a constant at the given location
    /// could have, in the order that Java would check them.  The constants that are inherited
    /// from a superclass or interface are not considered.
    pub(crate) fn candidates(&self, reference: &str, at_byte: usize) -> Vec<String> {
        let reference = compact(reference);
        let mut retval = Vec::new();
        match reference.split_once('.') {
            None => {
                // A bare name is a member of an enclosing class or is statically imported.
                let mut enclosing: Vec<&(Range<usize>, String)> = self
                    .classes
                    .iter()
                    .filter(|(range, _)| range.contains(&at_byte))
                    .collect();
                enclosing.sort_by_key(|(range, _)| range.len());
                retval.extend(
                    enclosing
                        .iter()
                        .map(|(_, fqn)| format!("{}.{}", fqn, reference)),
                );
                let suffix = format!(".{}", reference);
                retval.extend(
                    self.imports
                        .iter()
                        .filter(|imp| imp.is_static && !imp.wildcard && imp.path.ends_with(&suffix))
                        .map(|imp| imp.path.clone()),
                );
                retval.extend(
                    self.imports
                        .iter()
                        .filter(|imp| imp.is_static && imp.wildcard)
                        .map(|imp| format!("{}.{}", imp.path, reference)),
                );
            }
            Some((first, rest)) => {
                // The first component is a class, so resolve it like Java would and then the
                // remainder is a nested class and/or the constant name.
                for class in self.resolve_class(first) {
                    retval.push(format!("{}.{}", class, rest));
                }
                // It might also be a fully-qualified name.
                retval.push(reference.clone());
            }
        }
        let mut seen = std::collections::HashSet::new();
        retval.retain(|fqn| seen.insert(fqn.clone()));
        retval
    }

    /// Get the possible fully-qualified names for a simple class name used in this file.
    fn resolve_class(&self, name: &str) -> Vec<String> {
        let suffix = format!(".{}", name);
        let mut retval: Vec<String> = self
            .classes
            .iter()
            .filter(|(_, fqn)| fqn == name || fqn.ends_with(&suffix))
            .map(|(_, fqn)| fqn.clone())
            .collect();
        retval.extend(
            self.imports
                .iter()
                .filter(|imp| !imp.wildcard && (imp.path == name || imp.path.ends_with(&suffix)))
                .map(|imp| imp.path.clone()),
        );
        retval.push(if self.package.is_empty() {
            name.to_string()
        } else {
            format!("{}.{}", self.package, name)
        });
        retval.extend(
            self.imports
                .iter()
                .filter(|imp| imp.wildcard && !imp.is_static)
                .map(|imp| format!("{}.{}", imp.path, name)),
        );
        retval
    }
}

/// Map each constant's fully-qualified name to its value.  If a name is defined more than
/// once, the first definition wins, so callers should pass the constants in a stable order.
pub(crate) fn constants_by_name<'a>(
    constants: impl Iterator<Item = &'a StringConstant>,
) -> HashMap<String, String> {
    let mut retval = HashMap::new();
    for constant in constants {
        retval
            .entry(constant.fqn.clone())
            .or_insert_with(|| constant.value.clone());
    }
    retval
}

/// Find the value of the first candidate that is a known constant.
pub(crate) fn resolve<'a>(
    message_ref: &MessageRef,
    constants: &'a HashMap<String, String>,
) -> Option<&'a str> {
    message_ref
        .candidates
        .iter()
        .find_map(|fqn| constants.get(fqn))
        .map(String::as_str)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CodeSource;
    use std::path::PathBuf;

    fn symbols_for(src: &str) -> JavaSymbols {
        let code = CodeSource::from_string(&PathBuf::from("Test.java"), src);
        JavaSymbols::extract(&SourceQuery::new(&code))
    }

    #[test]
    fn test_extract_constants() {
        let symbols = symbols_for(
            r#"
package com.example;

class Messages {
    static final String LOG_STARTING = "Starting {} with " +
            "{} threads";
    public static final java.lang.String QUOTED = "say \"hi\"";
    static final String A = "a", B = "b";
    static final String DYNAMIC = "prefix " + System.getProperty("x");
    static String NOT_FINAL = "nope";
    final String NOT_STATIC = "nope";
    static final int NOT_STRING = 1;

    static class Nested {
        static final String INNER = "inner";
    }
}

interface Keys {
    String IMPLICIT = "implicit";
}
"#,
        );
        let constants: Vec<(&str, &str)> = symbols
            .constants
            .iter()
            .map(|c| (c.fqn.as_str(), c.value.as_str()))
            .collect();
        assert_eq!(
            constants,
            vec![
                (
                    "com.example.Messages.LOG_STARTING",
                    "Starting {} with {} threads"
                ),
                ("com.example.Messages.QUOTED", r#"say \"hi\""#),
                ("com.example.Messages.A", "a"),
                ("com.example.Messages.B", "b"),
                ("com.example.Messages.Nested.INNER", "inner"),
                ("com.example.Keys.IMPLICIT", "implicit"),
            ]
        );
    }

    const CALLER_SRC: &str = r#"
package com.example.cc;

import com.example.common.Messages;
import com.example.util.*;
import static com.example.config.Messages.LOG_KEY;
import static com.example.feed.Messages.*;

class Caller {
    private static final String LOCAL = "local";

    void run() {
        log.info(LOCAL);
    }
}
"#;

    #[test]
    fn test_candidates() {
        let symbols = symbols_for(CALLER_SRC);
        let at = CALLER_SRC.find("log.info").unwrap();
        assert_eq!(
            symbols.candidates("Messages.LOG_X", at),
            vec![
                "com.example.common.Messages.LOG_X",
                "com.example.cc.Messages.LOG_X",
                "com.example.util.Messages.LOG_X",
                "Messages.LOG_X",
            ]
        );
        assert_eq!(
            symbols.candidates("com.other.Messages.LOG_X", at),
            vec![
                "com.example.cc.com.other.Messages.LOG_X",
                "com.example.util.com.other.Messages.LOG_X",
                "com.other.Messages.LOG_X",
            ]
        );
        assert_eq!(
            symbols.candidates("LOCAL", at),
            vec![
                "com.example.cc.Caller.LOCAL",
                "com.example.feed.Messages.LOCAL",
            ]
        );
        assert_eq!(
            symbols.candidates("LOG_KEY", at),
            vec![
                "com.example.cc.Caller.LOG_KEY",
                "com.example.config.Messages.LOG_KEY",
                "com.example.feed.Messages.LOG_KEY",
            ]
        );
        // Outside of the class, its members are not in scope.
        assert_eq!(
            symbols.candidates("LOCAL", 0),
            vec!["com.example.feed.Messages.LOCAL"]
        );
    }

    #[test]
    fn test_candidates_nested_class() {
        let src = r#"
package com.example;

class Outer {
    static class Messages {
        static final String LOG_X = "x";
    }

    void run() {
        log.info(Messages.LOG_X);
    }
}
"#;
        let symbols = symbols_for(src);
        let at = src.find("log.info").unwrap();
        assert_eq!(
            symbols.candidates("Messages.LOG_X", at)[0],
            "com.example.Outer.Messages.LOG_X"
        );
    }

    #[test]
    fn constants_by_name_first_wins() {
        let constant = |value: &str| StringConstant {
            fqn: "com.example.Messages.LOG_X".to_string(),
            value: value.to_string(),
        };
        let constants = [constant("first"), constant("second")];
        let by_name = constants_by_name(constants.iter());
        assert_eq!(by_name["com.example.Messages.LOG_X"], "first");
    }
}
