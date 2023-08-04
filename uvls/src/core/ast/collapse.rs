use crate::core::*;
use ast::visitor::Visitor;
use ast::visitor::*;
use check::ErrorInfo;
use parse::*;
use ropey::Rope;
use std::borrow::Cow;
use tower_lsp::lsp_types::{FoldingRange, Url};
use tree_sitter::{Node, Tree, TreeCursor};

#[derive(Debug)]
pub struct Collapse {
    pub ranges: Vec<FoldingRange>,
    pub uri: Url,
}
impl Collapse {
    pub fn new(source: Rope, tree: Tree, uri: Url) -> Self {
        visit_root(source, tree, uri)
    }
}

//Transform a tree-sitter tree into the Ast ECS via recursive decent
//While parsing we keep a mutable state to store entities and errors
#[derive(Clone)]
struct VisitorCollapse<'a> {
    cursor: TreeCursor<'a>,
    ranges: Vec<FoldingRange>,
    source: &'a Rope,
    root_name: Option<String>,
    current_level: usize,
    levels: Vec<usize>,
}
impl<'a> Visitor<'a> for VisitorCollapse<'a> {
    fn cursor(&self) -> &TreeCursor<'a> {
        &self.cursor
    }
    fn cursor_mut(&mut self) -> &mut TreeCursor<'a> {
        &mut self.cursor
    }
    fn source(&self) -> &Rope {
        self.source
    }
    fn push_err_raw(&mut self, _: ErrorInfo) {}
}

impl<'a> VisitorCollapse<'a> {
    fn add_range(&mut self, start: usize, end: usize) -> () {
        self.ranges.push(FoldingRange {
            start_line: start as u32,
            start_character: None,
            end_line: end as u32,
            end_character: None,
            kind: None,
            collapsed_text: None,
        });
    }

    //get the current block header
    fn header(&self) -> Option<Node<'a>> {
        self.node().child_by_field_name("header")
    }

    fn set_line_level(&mut self) -> () {
        let line = self.line();
        self.levels[line] = self.current_level;
    }

    // Add ranges based on self.levels vec
    fn calculate_ranges(&mut self) -> () {
        // Skip comments
        let first_nonzero_line = self
            .levels
            .iter()
            .enumerate()
            .find(|(_, e)| e != &&0)
            .unwrap_or((0, &0))
            .0;
        for line in (0..self.levels.len() - 1).rev() {
            if self.levels[line] != 0 || line < first_nonzero_line {
                continue;
            }
            self.levels[line] = self.levels[line + 1];
        }

        let mut range_stack: Vec<(usize, usize)> = vec![];
        for line in 0..self.levels.len() {
            let level = self.levels[line];
            let next = *self.levels.get(line + 1).unwrap_or(&0);
            if level < next {
                range_stack.push((line, level));
            } else if level > next {
                while range_stack.len() > next {
                    let (start_line, _) = range_stack.pop().unwrap();
                    self.add_range(start_line, line);
                }
            }
        }
    }

    fn line(&self) -> usize {
        self.source.byte_to_line(self.node().byte_range().start)
    }
}
impl<'b> SymbolSlice for VisitorCollapse<'b> {
    fn slice_raw(&self, node: Span) -> Cow<'_, str> {
        self.source.byte_slice(node).into()
    }
}

fn visit_feature(collapse: &mut VisitorCollapse) {
    loop {
        if collapse.cursor().node().kind() == "blk" {
            visit_children(collapse, visit_blk_decl);
        }
        if !collapse.goto_next_sibling() {
            break;
        }
    }
}
fn visit_group(collapse: &mut VisitorCollapse) {
    loop {
        if collapse.kind() == "blk" {
            visit_children(collapse, visit_blk_decl);
        }
        if !collapse.goto_next_sibling() {
            break;
        }
    }
}
fn visit_blk_decl(collapse: &mut VisitorCollapse) {
    collapse.current_level += 1;
    collapse.set_line_level();
    collapse.goto_field("header");
    match collapse.kind() {
        "name" | "typed_feature" => {
            visit_feature(collapse);
        }
        "group_mode" | "cardinality" => {
            visit_group(collapse);
        }
        _ => {}
    }
    collapse.current_level -= 1;
}

fn visit_features(collapse: &mut VisitorCollapse) {
    collapse.set_line_level();
    loop {
        if collapse.kind() == "blk" {
            visit_children(collapse, visit_blk_decl);
        }
        if !collapse.goto_next_sibling() {
            break;
        }
    }
    collapse.calculate_ranges();
}

fn add_range_of_current_level(collapse: &mut VisitorCollapse) {
    let start = collapse.line();
    while collapse.goto_next_sibling() {}
    collapse.add_range(start, collapse.line());
}

fn visit_top_lvl(collapse: &mut VisitorCollapse) {
    let mut top_level_order: Vec<Node> = Vec::new();
    loop {
        if collapse.kind() == "blk" {
            let header = collapse.header().unwrap();
            top_level_order.push(header);
            match header.kind() {
                "include" | "imports" | "constraints" => {
                    visit_children(collapse, add_range_of_current_level)
                }
                "features" => visit_children(collapse, visit_features),
                _ => {}
            }
        }
        if !collapse.goto_next_sibling() {
            break;
        }
    }
}
//visits all valid children of a tree-sitter (red tree) recursively to translate them into the
//Collapse struct
pub fn visit_root(source: Rope, tree: Tree, uri: Url) -> Collapse {
    let mut c = VisitorCollapse {
        cursor: tree.walk(),
        ranges: vec![],
        source: &source,
        root_name: None,
        current_level: 0,
        levels: vec![0; source.lines().len()],
    };
    visit_children(&mut c, visit_top_lvl);
    Collapse {
        ranges: c.ranges,
        uri,
    }
}
