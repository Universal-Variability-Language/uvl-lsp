use crate::core::*;
use ast::visitor::Visitor;
use ast::visitor::*;
use ast::Ast;
use check::ErrorInfo;
use log::info;
use parse::*;
use ropey::Rope;
use semantic::FileID;
use std::borrow::{Borrow, Cow};
use tokio::time::Instant;
use tower_lsp::lsp_types::{DiagnosticSeverity, Url};
use tree_sitter::{Node, Tree, TreeCursor};
use util::node_range;
//Transform a tree-sitter tree into the Ast ECS via recursive decent
//While parsing we keep a mutable state to store entities and errors
#[derive(Clone)]
struct VisitorState<'a> {
    errors: Vec<ErrorInfo>,
    cursor: TreeCursor<'a>,
    ast: Ast,
    source: &'a Rope,
}
impl<'a> Visitor<'a> for VisitorState<'a> {
    fn cursor(&self) -> &TreeCursor<'a> {
        &self.cursor
    }
    fn cursor_mut(&mut self) -> &mut TreeCursor<'a> {
        &mut self.cursor
    }
    fn source(&self) -> &Rope {
        self.source
    }
    fn push_err_raw(&mut self, err: ErrorInfo) {
        self.errors.push(err);
    }
}
impl<'a> VisitorState<'a> {
    fn add_constraint(&mut self, constraint: ConstraintDecl, scope: Symbol) -> Symbol {
        self.ast.constraints.push(constraint);
        let sym = Symbol::Constraint(self.ast.constraints.len() - 1);
        self.push_child(scope, sym);
        sym
    }
    fn add_ref(&mut self, path: Path, scope: Symbol) -> Symbol {
        self.ast.references.push(Reference { path });
        let sym = Symbol::Reference(self.ast.references.len() - 1);
        self.push_child(scope, sym);
        sym
    }
    fn add_ref_direct(&mut self, path: Path) -> Symbol {
        self.ast.references.push(Reference { path });

        Symbol::Reference(self.ast.references.len() - 1)
    }
    //create the import tree map and the general search index for name resolution
    fn connect(&mut self) {
        //create the import index inside the radix tree
        for i in self.ast.all_imports() {
            let path = self.ast.import_prefix(i).to_vec();
            let mut node = Symbol::Root;
            for k in 0..path.len() - 1 {
                let dir_name = path[k];
                if let Some(dir) = self.ast.index.get(&(node, dir_name, SymbolKind::Dir)) {
                    node = *dir;
                } else {
                    let sym = Symbol::Dir(self.ast.dirs.len());
                    self.ast.dirs.push(Dir {
                        name: dir_name,
                        depth: k as u32 + 1,
                    });
                    self.push_child(node, sym);
                    self.ast
                        .index
                        .insert((node, dir_name, SymbolKind::Dir), sym);
                    node = sym;
                }
            }
            self.push_child(node, i);
            if let Some(old) = self
                .ast
                .index
                .insert((node, *path.last().unwrap(), SymbolKind::Import), i)
            {
                self.errors.push(ErrorInfo {
                    location: self.ast.lsp_range(i, self.source).unwrap(),
                    severity: DiagnosticSeverity::ERROR,
                    weight: 20,
                    msg: format!(
                        "duplicate import already defined in line {}",
                        self.ast.lsp_range(old, self.source).unwrap().start.line
                    ),
                    error_type: ErrorType::Any,
                });
            }
        }
        //Create name index for features and attributes inside the radix tree
        let mut stack = vec![(Symbol::Root, Symbol::Root, 0)];
        while let Some((node, scope, depth)) = stack.pop() {
            let new_scope = if let Some(name) = self.ast.name(node) {
                match node {
                    Symbol::Feature(i) => {
                        // removes duplicate feature error for cardinality
                        if !self.ast.get_feature(i).unwrap().duplicate {
                            if let Some(old) = self
                                .ast
                                .index
                                .insert((Symbol::Root, name, SymbolKind::Feature), node)
                            {
                                self.errors.push(ErrorInfo {
                                    location: self.ast.lsp_range(node, self.source).unwrap(),
                                    severity: DiagnosticSeverity::ERROR,
                                    weight: 20,
                                    msg: "duplicate feature".to_string(),
                                    error_type: ErrorType::Any,
                                });
                                self.errors.push(ErrorInfo {
                                    location: self.ast.lsp_range(old, self.source).unwrap(),
                                    severity: DiagnosticSeverity::ERROR,
                                    weight: 20,
                                    msg: "duplicate feature".to_string(),
                                    error_type: ErrorType::Any,
                                })
                            }
                        }
                        node
                    }
                    Symbol::Attribute(i) => {
                        if let Some(old) = self
                            .ast
                            .index
                            .insert((scope, name, SymbolKind::Attribute), node)
                        {
                            self.errors.push(ErrorInfo {
                                location: self.ast.lsp_range(node, self.source).unwrap(),
                                severity: DiagnosticSeverity::ERROR,
                                weight: 20,
                                msg: "duplicate attribute".to_string(),
                                error_type: ErrorType::Any,
                            });
                            self.errors.push(ErrorInfo {
                                location: self.ast.lsp_range(old, self.source).unwrap(),
                                severity: DiagnosticSeverity::ERROR,
                                weight: 20,
                                msg: "duplicate attribute".to_string(),
                                error_type: ErrorType::Any,
                            });
                        }
                        self.ast.attributes[i].depth = depth;
                        node
                    }
                    _ => scope,
                }
            } else {
                scope
            };
            for i in self.ast.children(node) {
                stack.push((i, new_scope, depth + 1));
            }
        }
        //find alias for different symbols and report them
        for i in self.ast.children(Symbol::Root) {
            if matches!(i, Symbol::Feature(..)) {
                if self
                    .ast
                    .index
                    .get(&(Symbol::Root, self.ast.name(i).unwrap(), SymbolKind::Dir))
                    .is_some()
                {
                    self.errors.push(ErrorInfo {
                        location: self.ast.lsp_range(i, self.source).unwrap(),
                        severity: DiagnosticSeverity::ERROR,
                        weight: 20,
                        msg: "name already defined as import directory".to_string(),
                        error_type: ErrorType::Any,
                    });
                }
                if self
                    .ast
                    .index
                    .get(&(Symbol::Root, self.ast.name(i).unwrap(), SymbolKind::Import))
                    .is_some()
                {
                    self.errors.push(ErrorInfo {
                        location: self.ast.lsp_range(i, self.source).unwrap(),
                        severity: DiagnosticSeverity::ERROR,
                        weight: 20,
                        msg: "name already defined as import".to_string(),
                        error_type: ErrorType::Any,
                    });
                }
            }
        }
    }
    //Add a child to parent
    fn push_child(&mut self, parent: Symbol, child: Symbol) {
        self.ast.structure.insert(parent, child);
    }
    //get the current block header
    fn header(&self) -> Option<Node<'a>> {
        self.node().child_by_field_name("header")
    }
    //Push an error with location of the current block header
    fn push_error_blk<T: Into<String>>(&mut self, w: u32, error: T) {
        self.errors.push(ErrorInfo {
            location: node_range(self.header().unwrap(), self.source),
            severity: DiagnosticSeverity::ERROR,
            weight: w,
            msg: error.into(),
            error_type: ErrorType::Any,
        });
    }
}
impl<'b> SymbolSlice for VisitorState<'b> {
    fn slice_raw(&self, node: Span) -> Cow<'_, str> {
        self.source.byte_slice(node).into()
    }
}
fn opt_name(state: &mut VisitorState) -> Option<SymbolSpan> {
    if state.kind() == "name" {
        if state.node().is_missing() {
            Some(SymbolSpan {
                name: "__MISSING__".into(),
                span: state.node().byte_range(),
            })
        } else {
            Some(SymbolSpan {
                name: state.name(state.node()),
                span: state.node().byte_range(),
            })
        }
    } else {
        None
    }
}
fn opt_path(state: &mut VisitorState) -> Option<Path> {
    if state.kind() == "name" {
        opt_name(state).map(|name| Path {
            names: vec![name.name],
            spans: vec![name.span],
        })
    } else if state.kind() == "path" {
        if state.child_by_name("tail").is_some() {
            state.push_error(10, "tailing dot not supported");
        }
        visit_children(state, |state| {
            let mut p = Path::default();
            loop {
                if let Some(name) = opt_name(state) {
                    p.names.push(name.name);
                    p.spans.push(name.span);
                }
                if !state.goto_next_sibling() {
                    break;
                }
            }
            Some(p)
        })
    } else {
        None
    }
}
//Report error if a node has children,cardinality or attributes
fn check_simple_blk(state: &mut VisitorState, kind: &str) {
    match state.cursor.field_name() {
        Some("cardinality") => state.push_error(30, format!("{} may not have a cardinality", kind)),
        Some("attribs") => state.push_error(30, format!("{} may not have a any attributes", kind)),
        Some("child") => state.push_error(30, format!("{} may not have a any children", kind)),
        _ => {}
    }
}

//report error if a node has cardinality or attributes
fn check_no_extra_blk(state: &mut VisitorState, kind: &str) {
    match state.cursor.field_name() {
        Some("cardinality") => state.push_error(30, format!("{} may not have a cardinality", kind)),
        Some("attribs") => state.push_error(30, format!("{} may not have a any attributes", kind)),
        _ => {}
    }
}
//parse a namespace
fn visit_namespace(state: &mut VisitorState) {
    loop {
        check_simple_blk(state, "namespace");
        if state.kind() == "namespace" {
            visit_children(state, |state| {
                state.goto_field("name");
                if state.ast.namespace.is_none() {
                    state.ast.namespace = opt_path(state);
                }
            });
        }
        if !state.goto_next_sibling() {
            break;
        }
    }
}

fn opt_arithmetic_minor(state: &mut VisitorState) -> Option<LanguageLevelArithmetic> {
    match state.kind() {
        "*" => Some(LanguageLevelArithmetic::Any),
        "feature-cardinality" => Some(LanguageLevelArithmetic::FeatureCardinality),
        "aggregate-function" => Some(LanguageLevelArithmetic::Aggregate),
        "group-cardinality" | "string-constraints" | "numeric-constraints" => {
            state.push_error(30, "not allowed under Arithmetic");
            None
        }
        _ => {
            state.push_error(30, "unknown Arithmetic level");
            None
        }
    }
}
fn opt_boolean_minor(state: &mut VisitorState) -> Option<LanguageLevelBoolean> {
    match state.kind() {
        "*" => Some(LanguageLevelBoolean::Any),
        "group-cardinality" => Some(LanguageLevelBoolean::GroupCardinality),
        "feature-cardinality"
        | "aggregate-function"
        | "string-constraints"
        | "numeric-constraints" => {
            state.push_error(30, "not allowed under Boolean");
            None
        }
        _ => {
            state.push_error(30, "unknown Boolean level");
            None
        }
    }
}
fn opt_type_minor(state: &mut VisitorState) -> Option<LanguageLevelType> {
    match state.kind() {
        "*" => Some(LanguageLevelType::Any),
        "numeric-constraints" => Some(LanguageLevelType::NumericConstraints),
        "string-constraints" => Some(LanguageLevelType::StringConstraints),
        "feature-cardinality" | "aggregate-function" | "group-cardinality" => {
            state.push_error(30, "not allowed under Type");
            None
        }
        _ => {
            state.push_error(30, "unknown Type level");
            None
        }
    }
}
fn opt_major_lang_lvl(state: &mut VisitorState) -> Option<LanguageLevel> {
    match state.node().kind() {
        "Boolean" => Some(LanguageLevel::Boolean(vec![])),
        "Arithmetic" => Some(LanguageLevel::Arithmetic(vec![])),
        "Type" => Some(LanguageLevel::Type(vec![])),
        _ => {
            state.push_error(30, "unknown major language level");
            None
        }
    }
}
fn opt_lang_lvl(state: &mut VisitorState) -> Option<LanguageLevel> {
    let mut out = None;
    loop {
        if state.kind() == "major_lvl" {
            if out.is_some() {
                state.push_error(30, "duplicate major level, please pick a minor level");
                return None;
            } else {
                out = Some(visit_children(state, opt_major_lang_lvl)?);
            }
        }
        if state.kind() == "minor_lvl" {
            if let Some(major) = out.as_mut() {
                match major {
                    LanguageLevel::Arithmetic(v) => {
                        if let Some(lvl) = visit_children(state, opt_arithmetic_minor) {
                            v.push(lvl);
                        } else {
                            return None;
                        }
                    }
                    LanguageLevel::Boolean(v) => {
                        if let Some(lvl) = visit_children(state, opt_boolean_minor) {
                            v.push(lvl);
                        } else {
                            return None;
                        }
                    }
                    LanguageLevel::Type(v) => {
                        if let Some(lvl) = visit_children(state, opt_type_minor) {
                            v.push(lvl);
                        } else {
                            return None;
                        }
                    }
                }
            } else {
                state.push_error(
                    30,
                    "missing major level, please specify Arithmetic, Boolean or Type level",
                );
                return None;
            }
        }
        if state.kind() == "name" {
            state.push_error(30, "unknown language level");
            return None;
        }
        if !state.goto_next_sibling() {
            break;
        }
    }
    out
}
fn visit_lang_lvl(state: &mut VisitorState) {
    loop {
        check_simple_blk(state, "");
        if state.kind() == "lang_lvl" {
            if let Some(lvl) = visit_children(state, opt_lang_lvl) {
                state.ast.includes.push(LanguageLevelDecl {
                    lang_lvl: lvl,
                    span: state.node().byte_range(),
                });
            }
        }
        if !state.goto_next_sibling() {
            break;
        }
    }
}
fn visit_include(state: &mut VisitorState) {
    loop {
        check_no_extra_blk(state, "include");
        if state.kind() == "blk" {
            match state.header().unwrap().kind() {
                "lang_lvl" => visit_children(state, visit_lang_lvl),
                "ref" => state.push_error_blk(
                    30,
                    "unknown language level start with Arithmetic, Boolean or Type",
                ),
                _ => {
                    state.push_error_blk(40, "expected a language level");
                }
            }
        }
        if !state.goto_next_sibling() {
            break;
        }
    }
}
fn visit_import_decl(state: &mut VisitorState) {
    loop {
        check_simple_blk(state, "import");
        if let Some(name) = opt_path(state) {
            state.ast.import.push(Import {
                path: name,
                alias: None,
            })
        } else if state.kind() == "ref" {
            visit_children(state, |state| {
                state.goto_field("path");
                let path = opt_path(state)?;
                let alias = if state.goto_field("alias") {
                    opt_name(state)
                } else {
                    None
                };
                state.ast.import.push(Import { path, alias });
                Some(())
            });
        }

        if !state.goto_next_sibling() {
            break;
        }
    }
}
fn visit_import(state: &mut VisitorState) {
    loop {
        check_no_extra_blk(state, "imports");
        if state.kind() == "blk" {
            match state.header().unwrap().kind() {
                "name" | "ref" => visit_children(state, visit_import_decl),
                "incomplete_ref" => {
                    state.push_error_blk(40, "incomplete import, please specify an alias");
                }
                _ => {
                    state.push_error_blk(40, "expected a import declaration");
                }
            }
        }
        if !state.goto_next_sibling() {
            break;
        }
    }
}

fn opt_int(node: Node, state: &mut VisitorState) -> Option<usize> {
    if let Ok(i) = state.slice(node).parse() {
        Some(i)
    } else {
        state.push_error_node(node, 20, "cant parse integer");
        None
    }
}
fn opt_cardinality(node: Node, state: &mut VisitorState) -> Option<Cardinality> {
    let begin = node.child_by_field_name("begin");
    let end = node.child_by_field_name("end");
    match (begin, end.map(|n| n.kind())) {
        (Some(begin), Some("int")) => Some(Cardinality::Range(
            opt_int(begin, state)?,
            opt_int(end.unwrap(), state)?,
        )),
        (None, Some("int")) => Some(Cardinality::Range(
            opt_int(end.unwrap(), state)?,
            opt_int(end.unwrap(), state)?,
        )),
        (_, _) => Some(Cardinality::Range(0, 1)),
    }
}

fn opt_number(state: &mut VisitorState) -> Option<f64> {
    if let Ok(num) = state.slice(state.node()).parse() {
        Some(num)
    } else {
        state.push_error(40, "failed to parse number");
        None
    }
}
fn opt_numeric_op(node: Node) -> Option<NumericOP> {
    match node.kind() {
        "+" => Some(NumericOP::Add),
        "-" => Some(NumericOP::Sub),
        "*" => Some(NumericOP::Mul),
        "/" => Some(NumericOP::Div),
        _ => None,
    }
}
fn opt_aggreate_op(state: &mut VisitorState) -> Option<AggregateOP> {
    match state.slice(state.child_by_name("op")?).borrow() {
        "sum" => Some(AggregateOP::Sum),
        "avg" => Some(AggregateOP::Avg),
        _ => {
            state.push_error(30, "unknown aggregate function");
            None
        }
    }
}
fn opt_integer_op(state: &mut VisitorState) -> Option<IntegerOP> {
    match state.slice(state.child_by_name("op")?).borrow() {
        "floor" => Some(IntegerOP::Floor),
        "ceil" => Some(IntegerOP::Ceil),
        _ => {
            state.push_error(30, "unknown integer function");
            None
        }
    }
}
fn opt_function_args(state: &mut VisitorState) -> Option<Vec<Path>> {
    visit_children(state, |state| {
        let mut args = Vec::new();
        loop {
            match state.kind() {
                "name" => {}
                "path" => args.push(opt_path(state).unwrap()),
                _ => {
                    if state.node().is_named() {
                        state.push_error(30, "expected a reference");
                        return None;
                    }
                }
            }
            if !state.goto_next_sibling() {
                break;
            }
        }
        Some(args)
    })
}

fn check_langlvls(state: &mut VisitorState, searched_lang_lvl: LanguageLevel) {
    if state.ast.includes.is_empty() {
        // no includes means, that implicitly everything is included
        return ();
    }

    let includes: Vec<LanguageLevel> = state
        .ast
        .includes
        .clone()
        .into_iter()
        .map(|x| x.lang_lvl)
        .collect();

    fn check_sub_lang_lvls<'a, F, G, L: PartialEq>(
        mut m: F,
        mut get: G,
        sub_lang_lvls: Vec<L>,
        includes: Vec<LanguageLevel>,
        any: L,
    ) -> bool
    where
        F: FnMut(&LanguageLevel) -> bool,
        G: FnMut(&LanguageLevel) -> Option<Vec<L>>,
    {
        sub_lang_lvls.is_empty() && includes.iter().any(|x| m(x))
            || sub_lang_lvls
                .iter()
                .fold(false, |mut res, val: &L| -> bool {
                    for i in includes.iter() {
                        let x = get(i).unwrap_or(vec![]);
                        if x.contains(&any) || x.contains(&val) {
                            res = true;
                            break;
                        }
                    }
                    res
                })
    }

    if !match searched_lang_lvl.borrow() {
        LanguageLevel::Arithmetic(s) => check_sub_lang_lvls(
            |x| matches!(x, LanguageLevel::Arithmetic(_)),
            |x| -> Option<Vec<LanguageLevelArithmetic>> {
                match x {
                    LanguageLevel::Arithmetic(l) => Some(l.to_vec()),
                    _ => None,
                }
            },
            s.clone(),
            includes,
            LanguageLevelArithmetic::Any,
        ),
        LanguageLevel::Boolean(s) => check_sub_lang_lvls(
            |x| matches!(x, LanguageLevel::Boolean(_)),
            |x| -> Option<Vec<LanguageLevelBoolean>> {
                match x {
                    LanguageLevel::Boolean(l) => Some(l.to_vec()),
                    _ => None,
                }
            },
            s.clone(),
            includes,
            LanguageLevelBoolean::Any,
        ),
        LanguageLevel::Type(s) => check_sub_lang_lvls(
            |x| matches!(x, LanguageLevel::Type(_)),
            |x| -> Option<Vec<LanguageLevelType>> {
                match x {
                    LanguageLevel::Type(l) => Some(l.to_vec()),
                    _ => None,
                }
            },
            s.clone(),
            includes,
            LanguageLevelType::Any,
        ),
    } {
        state.push_error(
            10,
            format!(
                "Operation does not correspond includes. Please include {:?}",
                searched_lang_lvl
            ),
        )
    }
}

fn opt_aggregate(state: &mut VisitorState) -> Option<Expr> {
    let op = opt_aggreate_op(state)?;
    if state.child_by_name("tail").is_some() {
        state.push_error(10, "tailing comma not allowed");
    }
    let args = opt_function_args(state)?;
    match args.len() {
        0 => {
            state.push_error(30, "missing arguments");
            None
        }
        1 => Some(Expr::Aggregate {
            op,
            query: args[0].clone(),
            context: None,
        }),
        2 => Some(Expr::Aggregate {
            op,
            query: args[1].clone(),
            context: Some(state.add_ref_direct(args[0].clone())),
        }),
        _ => {
            state.push_error(30, "to many arguments");
            None
        }
    }
}
fn opt_integer(state: &mut VisitorState) -> Option<Expr> {
    if state.child_by_name("tail").is_some() {
        state.push_error(10, "tailing comma not allowed");
    }
    let op = opt_integer_op(state)?;
    visit_children(state, |state| {
        if state.goto_field("arg") {
            let n: Box<ExprDecl> = opt_numeric(state)?.into();
            let out = Some(Expr::Integer { op: op.clone(), n });
            if state.goto_next_sibling() && state.goto_field("arg") {
                state.push_error(30, "expected exactly one argument");
            }
            out
        } else {
            state.push_error(30, "missing argument");
            None
        }
    })
}
fn opt_numeric(state: &mut VisitorState) -> Option<ExprDecl> {
    let span = state.node().byte_range();
    state.goto_named();
    match state.kind() {
        "path" => {
            let path = opt_path(state)?;
            Some(Expr::Ref(state.add_ref_direct(path)))
        }

        "number" => Some(Expr::Number(opt_number(state)?)),
        "string" => Some(Expr::String(opt_string(state)?)),
        "binary_expr" => {
            check_langlvls(state, LanguageLevel::Arithmetic(vec![]));
            let op = state.child_by_name("op").unwrap();
            visit_children(state, |state| {
                if let Some(op) = opt_numeric_op(op) {
                    state.goto_field("lhs");
                    let lhs = opt_numeric(state)?;
                    state.goto_field("rhs");
                    let rhs = opt_numeric(state)?;
                    Some(Expr::Binary {
                        op,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    })
                } else {
                    state.push_error_node(
                        state.node().parent().unwrap(),
                        40,
                        "found a constraint, expected an expression",
                    );
                    None
                }
            })
        }
        "nested_expr" => visit_children(state, opt_numeric).map(|c| c.content),
        "function" => match state.slice(state.child_by_name("op")?).borrow() {
            "sum" | "avg" => {
                check_langlvls(
                    state,
                    LanguageLevel::Arithmetic(vec![LanguageLevelArithmetic::Aggregate]),
                );
                opt_aggregate(state)
            }
            "len" => {
                check_langlvls(
                    state,
                    LanguageLevel::Type(vec![LanguageLevelType::StringConstraints]),
                );
                if state.child_by_name("tail").is_some() {
                    state.push_error(10, "tailing comma not allowed");
                }
                visit_children(state, |state| {
                    if state.goto_field("arg") {
                        info!("{:?}", state.node());
                        let out = Some(Expr::Len(opt_numeric(state)?.into()));
                        if state.goto_next_sibling() && state.goto_field("arg") {
                            state.push_error(30, "expected exactly one argument");
                        }

                        out
                    } else {
                        state.push_error(30, "missing argument");
                        None
                    }
                })
            }
            "floor" | "ceil" => {
                check_langlvls(
                    state,
                    LanguageLevel::Type(vec![LanguageLevelType::NumericConstraints]),
                );
                opt_integer(state)
            }
            _ => {
                state.push_error(30, "unknown function");
                None
            }
        },
        _ => {
            state.push_error(40, "found a constraint, expected a expression");
            None
        }
    }
    .map(|content| ExprDecl { span, content })
}
fn opt_logic_op(node: Node) -> Option<LogicOP> {
    match node.kind() {
        "&" => Some(LogicOP::And),
        "|" => Some(LogicOP::Or),
        "=>" => Some(LogicOP::Implies),
        "<=>" => Some(LogicOP::Equiv),
        _ => None,
    }
}

fn opt_equation(node: Node) -> Option<EquationOP> {
    match node.kind() {
        "==" => Some(EquationOP::Equal),
        ">" => Some(EquationOP::Greater),
        "<" => Some(EquationOP::Smaller),
        _ => None,
    }
}

fn opt_constraint(state: &mut VisitorState) -> Option<ConstraintDecl> {
    let span = state.node().byte_range();
    state.goto_named();
    match state.kind() {
        "path" | "name" => {
            let path = opt_path(state)?;
            Some(Constraint::Ref(state.add_ref_direct(path)))
        }
        "bool" => Some(Constraint::Constant(visit_children(state, opt_bool))),
        "unary_expr" => {
            let op = state.child_by_name("op").unwrap().kind();
            visit_children(state, |state| {
                state.goto_field("lhs");
                match op {
                    "!" => opt_constraint(state).map(|c| Constraint::Not(Box::new(c))),
                    _ => None,
                }
            })
        }
        "nested_expr" => visit_children(state, opt_constraint).map(|c| c.content),
        "binary_expr" => {
            check_langlvls(state, LanguageLevel::Arithmetic(vec![]));
            let op = state.child_by_name("op").unwrap();
            visit_children(state, |state| {
                if let Some(op) = opt_logic_op(op) {
                    state.goto_field("lhs");
                    let lhs = opt_constraint(state)?;
                    state.goto_field("rhs");
                    let rhs = opt_constraint(state)?;
                    Some(Constraint::Logic {
                        op,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    })
                } else if let Some(op) = opt_equation(op) {
                    state.goto_field("lhs");
                    let lhs = opt_numeric(state)?;
                    state.goto_field("rhs");
                    let rhs = opt_numeric(state)?;
                    Some(Constraint::Equation {
                        op,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    })
                } else {
                    state.push_error_node(
                        state.node().parent().unwrap(),
                        40,
                        "expected a constraint found a expression",
                    );
                    None
                }
            })
        }
        _ => {
            state.push_error(40, "expected a constraint found a expression");
            None
        }
    }
    .map(|content| ConstraintDecl { span, content })
}
fn visit_constraint(state: &mut VisitorState, parent: Symbol, _duplicate: &bool) {
    if let Some(cons) = opt_constraint(state) {
        state.add_constraint(cons, parent);
    }
}
fn opt_bool(state: &mut VisitorState) -> bool {
    match state.kind() {
        "true" => true,
        "false" => false,
        _ => false,
    }
}
fn opt_string(state: &mut VisitorState) -> Option<String> {
    if state.kind() == "string" {
        visit_children(state, |state| {
            state.goto_kind("string_content");
            Some(
                state
                    .source
                    .slice_raw(state.node().byte_range())
                    .to_string(),
            )
        })
    } else {
        None
    }
}
fn opt_attrib_expr(state: &mut VisitorState) -> Option<Value> {
    state.goto_named();
    match state.kind() {
        "number" => Some(Value::Number(opt_number(state)?)),
        "bool" => Some(Value::Bool(visit_children(state, opt_bool))),
        "string" => Some(Value::String(opt_string(state)?)),
        "path" => {
            state.push_error(30, "attribute references are not supported");
            None
        }
        "binary_expr" | "nested_expr" | "aggregate" | "unary_expr" => {
            state.push_error(30, "composit atttribute values are not supported");
            None
        }
        _ => None,
    }
}
fn opt_value(state: &mut VisitorState) -> Value {
    match state.kind() {
        "vector" => Value::Vector, //We dont parse vectors since they seem unsed
        "attributes" => Value::Attributes,
        "attrib_expr" => visit_children(state, opt_attrib_expr).unwrap_or_default(),
        _ => Value::Void,
    }
}

fn visit_attribute_value(state: &mut VisitorState, parent: Symbol, duplicate: &bool) {
    state.goto_field("name");
    let name = opt_name(state).unwrap();
    let sym = Symbol::Attribute(state.ast.attributes.len());
    state.push_child(parent, sym);
    state.goto_field("value");
    let value = opt_value(state);
    let has_children = matches!(&value, Value::Attributes);
    state.ast.attributes.push(Attribute {
        name,
        value: ValueDecl {
            value,
            span: state.node().byte_range(),
        },
        depth: 0,
        duplicate: duplicate.clone(),
    });
    if has_children {
        visit_children_arg(state, sym, &duplicate, visit_attributes);
    }
}
fn visit_constraint_list(state: &mut VisitorState, parent: Symbol, duplicate: &bool) {
    loop {
        if state.kind() == "constraint" {
            visit_children_arg(state, parent, duplicate, visit_constraint);
        }
        if !state.goto_next_sibling() {
            break;
        }
    }
}
fn visit_attributes(state: &mut VisitorState, parent: Symbol, duplicate: &bool) {
    loop {
        match state.kind() {
            "attribute_constraints" => {
                if state.child_by_name("tail").is_some() {
                    state.push_error(10, "tailing comma unsupported");
                }
                visit_children_arg(state, parent, duplicate, visit_constraint_list);
            }
            "attribute_constraint" => {
                visit_children(state, |state| {
                    debug_assert!(state.goto_kind("constraint"));
                    visit_children_arg(state, parent, duplicate, visit_constraint);
                });
            }
            "attribute_value" => {
                visit_children_arg(state, parent, duplicate, visit_attribute_value);
            }
            _ => {}
        }
        if !state.goto_next_sibling() {
            break;
        }
    }
}

fn visit_feature(
    state: &mut VisitorState,
    parent: Symbol,
    name: SymbolSpan,
    ty: Type,
    duplicate: bool,
) {
    match parent {
        Symbol::Feature(..) => {
            state.push_error(40, "features have to be separated by groups");
        }
        _ => {}
    }
    let feature = Feature {
        name,
        ty,
        cardinality: state
            .node()
            .parent()
            .unwrap()
            .child_by_field_name("cardinality")
            .and_then(|n| {
                check_langlvls(
                    state,
                    LanguageLevel::Arithmetic(vec![LanguageLevelArithmetic::FeatureCardinality]),
                );
                opt_cardinality(n, state)
            })
            .or_else(|| Some(Cardinality::Fixed)),
        duplicate: duplicate.clone(),
        first_cardinality_child: true,
    };

    // remaps feature to different entities of the cardinality
    let mut sym = vec![];

    match feature.clone().cardinality.unwrap() {
        Cardinality::Fixed => {
            sym.push(Symbol::Feature(state.ast.features.len()));
            state.ast.features.push(feature.clone());
            state.push_child(parent, sym.get(0).unwrap().clone());
        }
        Cardinality::Range(_, max) => {
            for i in 0..max {
                let mut dup_feature = feature.clone();
                sym.push(Symbol::Feature(state.ast.features.len()));
                if i != 0 {
                    dup_feature.duplicate = true;
                    dup_feature.first_cardinality_child = false;
                }
                state.ast.features.push(dup_feature);
                state.push_child(parent, sym.get(i).unwrap().clone());
            }
        }
    }
    loop {
        for index in 0..sym.len() {
            let mut duplicate_par = false;
            if let Symbol::Feature(id) = sym.get(index).unwrap() {
                duplicate_par = state.ast.get_feature(*id).unwrap().duplicate;
            }
            match state.kind() {
                "attributes" => {
                    visit_children_arg(
                        state,
                        sym.get(index).unwrap().clone(),
                        &duplicate_par,
                        visit_attributes,
                    );
                }
                "blk" => {
                    visit_children_arg(
                        state,
                        sym.get(index).unwrap().clone(),
                        &&duplicate_par,
                        visit_blk_decl,
                    );
                }
                _ => {}
            }
        }
        if !state.goto_next_sibling() {
            break;
        }
    }
}

fn visit_ref(state: &mut VisitorState, parent: Symbol, path: Path) {
    match parent {
        Symbol::Feature(..) => {
            state.push_error(40, "features have to be separated by groups");
        }
        _ => {}
    }
    state.add_ref(path, parent);
    loop {
        check_simple_blk(state, "references");
        if !state.goto_next_sibling() {
            break;
        }
    }
}
fn visit_group(state: &mut VisitorState, parent: Symbol, mode: GroupMode, duplicate: &bool) {
    match parent {
        Symbol::Group(..) => {
            state.push_error(40, "groups have to be separated by features");
        }
        Symbol::Root => {
            state.push_error(40, "groups have to be contained by features");
        }
        _ => {}
    }
    let sym = Symbol::Group(state.ast.groups.len());
    state.push_child(parent, sym);
    state.ast.groups.push(Group {
        mode,
        span: state.node().byte_range(),
    });
    loop {
        check_no_extra_blk(state, "group");
        if state.kind() == "blk" {
            visit_children_arg(state, sym, duplicate, visit_blk_decl);
        }
        if !state.goto_next_sibling() {
            break;
        }
    }
}
fn visit_blk_decl(state: &mut VisitorState, parent: Symbol, duplicate: &bool) {
    state.goto_field("header");
    match state.kind() {
        "name" => {
            let name = opt_name(state).unwrap();
            visit_feature(state, parent, name, Type::Bool, *duplicate);
        }
        "typed_feature" => {
            check_langlvls(state, LanguageLevel::Type(vec![]));
            let (name, ty) = visit_children(state, |state| {
                state.goto_field("type");
                let ty = match &*state.slice_raw(state.node().byte_range()) {
                    "Integer" | "Real" => Type::Real,
                    "String" => Type::String,
                    "Boolean" => Type::Bool,
                    _ => {
                        state.push_error(30, "unknown type, interpreting as boolean");
                        Type::Bool
                    }
                };
                state.goto_field("name");
                Some((opt_name(state).unwrap(), ty))
            })
            .unwrap();
            visit_feature(state, parent, name, ty, *duplicate);
        }
        "ref" => {
            let path = visit_children(state, |state| {
                state.goto_field("path");
                let path = opt_path(state);
                if state.goto_field("alias") {
                    state.push_error(30, "imported features may not have an alias");
                }
                path
            })
            .unwrap();
            visit_ref(state, parent, path);
        }
        "group_mode" => {
            let mode = match state.node().child(0).unwrap().kind() {
                "mandatory" => GroupMode::Mandatory,
                "or" => GroupMode::Or,
                "optional" => GroupMode::Optional,
                "alternative" => GroupMode::Alternative,
                _ => GroupMode::Mandatory,
            };
            visit_group(state, parent, mode, duplicate);
        }
        "cardinality" => {
            check_langlvls(
                state,
                LanguageLevel::Boolean(vec![LanguageLevelBoolean::GroupCardinality]),
            );
            let card = opt_cardinality(state.node(), state).unwrap_or(Cardinality::Fixed);
            visit_group(state, parent, GroupMode::Cardinality(card), duplicate);
        }
        _ => {
            if state.kind() == "constraint" && state.name(state.cursor().node()).contains("-") {
                // todo check if also for groups
                state.push_error_with_type(
                    40,
                    "name contains a dash (-)",
                    ErrorType::FeatureNameContainsDashes,
                )
            } else {
                state.push_error(40, "expected a feature or group declaration");
            }
        }
    }
}
fn visit_features(state: &mut VisitorState) {
    let keyword = Keyword {
        name: state.name(state.node()),
        span: state.node().byte_range(),
    };
    state.ast.keywords.push(keyword);
    loop {
        check_no_extra_blk(state, "features");
        if state.kind() == "blk" {
            visit_children_arg(state, Symbol::Root, &false, visit_blk_decl);
        }
        if !state.goto_next_sibling() {
            break;
        }
    }
}
fn visit_constraint_decl(state: &mut VisitorState) {
    loop {
        check_simple_blk(state, "constraints");
        match state.kind() {
            "constraint" | "ref" => {
                visit_children_arg(state, Symbol::Root, &false, visit_constraint)
            }
            "name" => visit_constraint(state, Symbol::Root, &false),
            _ => {}
        }
        if state.kind() == "ref" {
            if let Some(alias) = state.child_by_name("alias") {
                state.push_error_node(alias, 30, "alias not allowed here");
            }
        }
        if !state.goto_next_sibling() {
            break;
        }
    }
}
fn visit_constraints(state: &mut VisitorState) {
    loop {
        check_no_extra_blk(state, "constraints");
        if state.kind() == "blk" {
            let header = state.header().unwrap();
            match header.kind() {
                "constraint" | "name" | "ref" => {
                    visit_children(state, visit_constraint_decl);
                }
                _ => {
                    state.push_error(40, "expected a constraint");
                }
            }
        }
        if !state.goto_next_sibling() {
            break;
        }
    }
}
fn visit_top_lvl(state: &mut VisitorState) {
    let mut top_level_order: Vec<Node> = Vec::new();
    loop {
        if state.kind() == "blk" {
            let header = state.header().unwrap();
            top_level_order.push(header);
            match header.kind() {
                "namespace" => visit_children(state, visit_namespace),
                "include" => visit_children(state, visit_include),
                "imports" => visit_children(state, visit_import),
                "features" => visit_children(state, visit_features),
                "constraints" => visit_children(state, visit_constraints),
                "incomplete_namespace" => {
                    state.push_error_blk(60, "incomplete namespace");
                    top_level_order.pop();
                }
                _ => {
                    state.push_error_blk(60,"only namspaces, imports, includes, features and constraints are allowed here");
                    visit_children(state, visit_features);
                    top_level_order.pop();
                }
            }
        }
        if !state.goto_next_sibling() {
            break;
        }
    }
    let fixed_order = ["namespace", "include", "imports", "features", "constraints"];
    for i in 1..top_level_order.iter().len() {
        let k = fixed_order
            .iter()
            .enumerate()
            .find(|name| name.1 == &top_level_order[i - 1].kind())
            .unwrap()
            .0;
        let w = fixed_order
            .iter()
            .enumerate()
            .find(|name| name.1 == &top_level_order[i].kind())
            .unwrap()
            .0;
        if k == w {
            state.push_error_node(
                top_level_order[i],
                50,
                format!("duplicate {} section", top_level_order[i].kind()),
            );
        }
        if k > w {
            state.push_error_node(
                top_level_order[i],
                50,
                format!(
                    "{} section comes before the {} section",
                    top_level_order[i - 1].kind(),
                    top_level_order[i].kind()
                ),
            );
        }
    }
}
//visits all valid children of a tree-sitter (green tree) recursively to translate them into the
//AST(red tree)
pub fn visit_root(source: Rope, tree: Tree, uri: Url, timestamp: Instant) -> AstDocument {
    let (ast, errors) = {
        let mut state = VisitorState {
            errors: Vec::new(),
            cursor: tree.walk(),
            ast: Default::default(),
            source: &source,
        };
        visit_children(&mut state, visit_top_lvl);
        state.connect();
        (state.ast, state.errors)
    };
    let mut path = uri_to_path(&uri).unwrap();
    if let Some(ns) = ast.namespace.as_ref() {
        let len = path.len().saturating_sub(ns.names.len());
        path.truncate(len);
        path.extend_from_slice(&ns.names);
    }
    AstDocument {
        id: FileID::from_uri(&uri),
        path,
        uri,
        ast,
        source,
        tree,
        timestamp,
        errors,
    }
}
