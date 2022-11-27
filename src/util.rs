use ropey::Rope;

use tree_sitter::{Language,Node};

use crate::query::Queries;
use tower_lsp::lsp_types::{Range,Position};

pub struct ParseConstants {
    pub queries: Queries,
    pub lang: Language,
}

impl ParseConstants {
    pub fn new() -> ParseConstants {
        let lang = tree_sitter_uvl::language();
        let queries = Queries::new(&lang);
        ParseConstants { queries, lang }
    }
}
pub fn node_source<'a>(source: &'a Rope) -> impl tree_sitter::TextProvider<'a> {
    |node: tree_sitter::Node| {
        source
            .byte_slice(node.byte_range())
            .chunks()
            .map(|i: &str| i.as_bytes())
    }
}
pub fn node_range(node: Node) -> Range {
    Range {
        start: tower_lsp::lsp_types::Position {
            line: node.start_position().row as u32,
            character: node.start_position().column as u32,
        },
        end: tower_lsp::lsp_types::Position {
            line: node.end_position().row as u32,
            character: node.end_position().column as u32,
        },
    }
}

pub fn lsp_position(byte: usize, source: &Rope) -> Option<Position> {
    if byte == source.len_bytes() {
        Some(Position {
            line: (source.len_lines() - 1) as u32,
            character: source.line(source.len_lines() - 1).len_utf16_cu() as u32,
        })
    } else if byte > source.len_bytes() {
        None
    } else {
        let line = source.byte_to_line(byte);
        let col = source.byte_to_char(byte) - source.line_to_char(line);
        let col16 = source.line(line).char_to_utf16_cu(col);
        Some(Position {
            line: line as u32,
            character: col16 as u32,
        })
    }
}
pub fn lsp_range(span: std::ops::Range<usize>, source: &Rope) -> Option<Range> {
    lsp_position(span.start, source)
        .map(|start| lsp_position(span.end, source).map(|end| Range { start, end }))
        .flatten()
}

