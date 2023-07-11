use crate::core::*;
use log::info;
use ropey::Rope;
use tower_lsp::lsp_types::DiagnosticSeverity;
use tree_sitter::{Node, TreeCursor};
use util::node_range;
//This trait makes the tree-sitter cursor api easier to use.
pub trait Visitor<'a> {
    fn cursor(&self) -> &TreeCursor<'a>;
    fn cursor_mut(&mut self) -> &mut TreeCursor<'a>;
    fn source(&self) -> &Rope;
    fn push_err_raw(&mut self, err: ErrorInfo);
    //ignore comments and errors
    fn skip_extra(&mut self) -> bool {
        loop {
            if !self.node().is_extra() && !self.node().is_error() {
                return true;
            }
            if !self.cursor_mut().goto_next_sibling() {
                return false;
            }
        }
    }
    //try to go down
    fn goto_first_child(&mut self) -> bool {
        if self.cursor_mut().goto_first_child() {
            if self.skip_extra() {
                true
            } else {
                self.goto_parent();
                false
            }
        } else {
            false
        }
    }
    //try to goto a named node on the current layer
    fn goto_named(&mut self) -> bool {
        loop {
            if self.node().is_named() {
                return true;
            }
            if !self.goto_next_sibling() {
                return false;
            }
        }
    }
    fn goto_next_sibling(&mut self) -> bool {
        self.cursor_mut().goto_next_sibling() && self.skip_extra()
    }
    fn goto_parent(&mut self) {
        self.cursor_mut().goto_parent();
    }
    fn kind(&self) -> &str {
        self.cursor().node().kind()
    }
    fn node(&self) -> Node<'a> {
        self.cursor().node()
    }
    fn child_by_name(&self, name: &str) -> Option<Node<'a>> {
        self.node().child_by_field_name(name)
    }
    //try to go forward at least once until we find a node of kind
    fn goto_next_kind(&mut self, kind: &str) -> bool {
        loop {
            if !self.goto_next_sibling() {
                return false;
            }
            if self.kind() == kind {
                return true;
            }
        }
    }
    //try to go forward until we find a node as a field name
    fn goto_field(&mut self, name: &str) -> bool {
        loop {
            if self
                .cursor()
                .field_name()
                .map(|f| f == name)
                .unwrap_or(false)
            {
                return true;
            }
            if !self.goto_next_sibling() {
                return false;
            }
        }
    }
    //try to go forward until we find a node of kind name
    fn goto_kind(&mut self, name: &str) -> bool {
        loop {
            if self.kind() == name {
                return true;
            }
            if !self.goto_next_sibling() {
                return false;
            }
        }
    }
    fn push_error<T: Into<String>>(&mut self, w: u32, error: T) {
        self.push_err_raw(ErrorInfo {
            location: node_range(self.node(), self.source()),
            severity: DiagnosticSeverity::ERROR,
            weight: w,
            msg: error.into(),
            error_type: ErrorType::Any,
        });
    }
    fn push_error_with_type<T: Into<String>>(&mut self, w: u32, error: T, error_type: ErrorType) {
        self.push_err_raw(ErrorInfo {
            location: node_range(self.node(), self.source()),
            severity: DiagnosticSeverity::ERROR,
            weight: w,
            msg: error.into(),
            error_type,
        });
    }
    fn push_error_node<T: Into<String>>(&mut self, node: Node, w: u32, error: T) {
        self.push_err_raw(ErrorInfo {
            location: node_range(node, self.source()),
            severity: DiagnosticSeverity::ERROR,
            weight: w,
            msg: error.into(),
            error_type: ErrorType::Any,
        });
    }
}
//Utility function, tree-sitter uses cursor to traverse trees, this creates a scope that
//guarantees to "go down", call f and later "go up" one level. It also protects against stack
//overflow
pub fn visit_children<'a, F, T, V>(state: &mut V, mut f: F) -> T
where
    V: Visitor<'a>,
    F: FnMut(&mut V) -> T,
    T: Default,
{
    if state.goto_first_child() {
        if stacker::remaining_stack().unwrap() <= 32 * 1024 {
            info!("In the red zone");
        }
        let out = stacker::maybe_grow(32 * 1024, 1024 * 1024, || f(state));
        state.goto_parent();
        out
    } else {
        T::default()
    }
}

pub fn visit_children_arg<'a, A, F, T, V>(state: &mut V, arg: A, duplicate: &bool, mut f: F) -> T
where
    V: Visitor<'a>,
    F: FnMut(&mut V, A, &bool) -> T,
    T: Default,
{
    if state.goto_first_child() {
        let out = stacker::maybe_grow(32 * 1024, 1024 * 1024, || f(state, arg, duplicate));
        state.goto_parent();
        out
    } else {
        T::default()
    }
}
//loop over all siblings
pub fn visit_siblings<'a, F: FnMut(&mut V), V: Visitor<'a>>(state: &mut V, mut f: F) {
    loop {
        f(state);
        if !state.goto_next_sibling() {
            break;
        }
    }
}
