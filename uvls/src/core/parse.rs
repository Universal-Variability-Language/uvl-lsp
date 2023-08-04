use crate::core::*;

use log::info;
use ropey::Rope;
use std::borrow::Cow;
use std::cell::RefCell;
use tokio::time::Instant;
use tree_sitter::*;
use ustr::Ustr;
thread_local! {
    static PARSER_UVL:RefCell<Parser> = RefCell::new(Parser::new());
    static PARSER_JSON:RefCell<Parser> = RefCell::new(Parser::new());
}
pub fn parse(src: &Rope, old_tree: Option<&Tree>) -> Tree {
    let t = Instant::now();
    let tree = PARSER_UVL
        .with(|parser| {
            if parser.borrow().language().is_none() {
                let _ = parser.borrow_mut().set_language(TS.uvl);
            }

            parser.borrow_mut().parse_with(
                &mut |byte_offset: usize, _: Point| {
                    if byte_offset > src.len_bytes() {
                        ""
                    } else {
                        src.byte_slice(byte_offset..).chunks().next().unwrap_or("")
                    }
                },
                old_tree,
            )
        })
        .unwrap();
    info!("Parsed in {:?}", t.elapsed());
    tree
}

pub fn parse_json(src: &Rope, old_tree: Option<&Tree>) -> Tree {
    let t = Instant::now();
    let tree = PARSER_JSON
        .with(|parser| {
            if parser.borrow().language().is_none() {
                let _ = parser.borrow_mut().set_language(TS.json);
            }
            parser.borrow_mut().parse_with(
                &mut |byte_offset: usize, _: Point| {
                    if byte_offset > src.len_bytes() {
                        ""
                    } else {
                        src.byte_slice(byte_offset..).chunks().next().unwrap_or("")
                    }
                },
                old_tree,
            )
        })
        .unwrap();
    info!("Parsed in {:?}", t.elapsed());
    tree
}
pub trait SymbolSlice {
    fn slice(&self, node: Node) -> Cow<str> {
        self.slice_raw(node.byte_range())
    }
    fn name(&self, node: Node) -> Ustr {
        Ustr::from(&self.slice_raw(node.byte_range()))
    }
    fn slice_raw(&self, node: Span) -> Cow<'_, str>;
}

impl SymbolSlice for str {
    fn slice_raw(&self, node: Span) -> Cow<str> {
        Cow::Borrowed(&self[node])
    }
}

impl SymbolSlice for String {
    fn slice_raw(&self, node: Span) -> Cow<str> {
        Cow::Borrowed(&self[node])
    }
}

impl SymbolSlice for Rope {
    fn slice_raw(&self, node: Span) -> Cow<str> {
        self.byte_slice(node).into()
    }
}

pub fn parse_name<S: SymbolSlice>(node: Node, source: &S) -> Option<SymbolSpan> {
    if node.is_missing() {
        Some(SymbolSpan {
            name: Ustr::from("__MISSING_NAME__"),
            span: node.byte_range(),
        })
    } else {
        match node.kind() {
            "name" => Some(SymbolSpan {
                name: source.name(node),
                span: node.byte_range(),
            }),
            _ => None,
        }
    }
}

pub fn parse_path<S: SymbolSlice>(node: Node, source: &S) -> Option<Path> {
    if let Some(name) = parse_name(node, source) {
        Some(Path {
            names: vec![name.name],
            spans: vec![name.span],
        })
    } else if node.kind() == "path" {
        let mut cursor = node.walk();
        cursor.goto_first_child();
        let mut path = Path::default();
        loop {
            if let Some(name) = parse_name(cursor.node(), source) {
                path.names.push(name.name);
                path.spans.push(name.span);
            }
            if !cursor.goto_next_sibling() {
                break;
            }
        }
        Some(path)
    } else {
        None
    }
}
pub fn parse_lang_lvl<S: SymbolSlice>(node: Node, source: &S) -> Option<SymbolSpan> {
    if node.is_missing() {
        Some(SymbolSpan {
            name: Ustr::from("__MISSING_NAME__"),
            span: node.byte_range(),
        })
    } else {
        match node.kind() {
            "major_lvl" | "minor_lvl" | "name" => Some(SymbolSpan {
                name: source.name(node),
                span: node.byte_range(),
            }),
            _ => None,
        }
    }
}
pub fn parse_lang_lvl_path<S: SymbolSlice>(node: Node, source: &S) -> Option<Path> {
    if let Some(name) = parse_lang_lvl(node, source) {
        Some(Path {
            names: vec![name.name],
            spans: vec![name.span],
        })
    } else if node.kind() == "lang_lvl" {
        let mut cursor = node.walk();
        cursor.goto_first_child();
        let mut path = Path::default();
        loop {
            if let Some(name) = parse_lang_lvl(cursor.node(), source) {
                path.names.push(name.name);
                path.spans.push(name.span);
            }

            if !cursor.goto_next_sibling() {
                break;
            }
        }
        Some(path)
    } else {
        None
    }
}
pub fn parse_or_lang_lvl<S: SymbolSlice>(node: Node, source: &S) -> Option<Path> {
    parse_path(node, source).or_else(|| parse_lang_lvl_path(node, source))
}

pub fn move_span(span: Span, offset: usize) -> Span {
    span.start + offset..span.end + offset
}
