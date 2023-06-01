use std::borrow::{Cow, Borrow};

use crate::core::*;
use ast::visitor::*;
use check::ErrorInfo;
use parse::*;
use util::{node_range};
use ropey::Rope;
use tower_lsp::lsp_types::{DiagnosticSeverity, Url};
use tree_sitter::{Node, Tree, TreeCursor};
use ast::visitor::Visitor;

const FEATURE_COLOR: &str = "#576EA1";

// Defined by https://graphviz.org/docs/attr-types/arrowType/
enum ArrowEnd {
    None,
    Arrow,
    ArrowEmpty,
    ArrowInversed,
    ArrowPointed,
    ArrowPointedInversed,
    DotFilled,
    DotEmpty,
    Diamond,
    DiamondEmpty,
    Box,
    BoxEmpty,
    Tee
}
impl ArrowEnd {
    fn as_str(&self) -> &str {
        match *self {
            ArrowEnd::None => "none",
            ArrowEnd::Arrow => "normal",
            ArrowEnd::ArrowEmpty => "empty",
            ArrowEnd::ArrowInversed => "inv",
            ArrowEnd::ArrowPointed => "open",
            ArrowEnd::ArrowPointedInversed => "crow",
            ArrowEnd::DotFilled => "dot",
            ArrowEnd::DotEmpty => "odot",
            ArrowEnd::Diamond => "diamond",
            ArrowEnd::DiamondEmpty => "ediamond",
            ArrowEnd::Box => "box",
            ArrowEnd::BoxEmpty => "obox",
            ArrowEnd::Tee => "tee",
        }
    }
    fn head(mode: GroupMode) -> Self {
        match mode {
            GroupMode::Or => Self::DotFilled,
            GroupMode::Alternative => Self::DotEmpty,
            _ => Self::None
        }
    }
    fn tail(mode: GroupMode) -> Self {
        match mode {
            GroupMode::Optional => Self::DotEmpty,
            GroupMode::Mandatory => Self::DotFilled,
            _ => Self::None
        }
    }
}
// Defined by https://graphviz.org/doc/info/shapes.html#polygon
enum Shape {
    Box,
    Polygon,
    Ellipse,
    Oval,
    Circle,
    HouseInverted
}
impl Shape {
    fn as_str(&self) -> &str {
        match *self {
            Shape::Box => "box",
            Shape::Polygon => "polygon",
            Shape::Ellipse => "ellipse",
            Shape::Oval => "oval",
            Shape::Circle => "circle",
            Shape::HouseInverted => "invhouse",
        }
    }
    fn by_mode(mode: GroupMode) -> Self {
        match mode {
            GroupMode::Alternative | GroupMode::Or => Self::HouseInverted,
            _ => Self::Box
        }
    }
}

#[derive(Debug)]
pub struct Graph {
    pub dot: String,
    pub uri: Url
}
impl Graph {
    pub fn new(source: Rope, tree: Tree, uri: Url) -> Self {
        visit_root(source, tree, uri)
    }
}

#[derive(Clone, Debug)]
pub enum GraphSymbol {
    Feature(String, String, Option<GroupMode>, Option<Type>), // name, description
    Group(String, String, GroupMode),  // name, description
    Root(String), // name
}

#[derive(Clone, Debug)]
pub struct GraphNode {
    pub name: String,
    pub description: Option<String>,
    pub r#type: Option<Type>,
    pub group_mode: Option<GroupMode>,
    pub cardinality: Option<Cardinality>,
    pub parent: Option<Box<GraphNode>>
}

impl GraphNode {
    fn is_root(&self) -> bool {
        self.parent.is_none()
    }
    fn root(name: Option<String>) -> Self {
        let mut root = GraphNode::default();
        root.name = name.unwrap_or("Root".to_string());
        root
    }
}
impl Default for GraphNode {
    fn default() -> Self {
        GraphNode { name: String::default(), description: None, r#type: None, group_mode: None, cardinality: None, parent: None }
    }
}

//Transform a tree-sitter tree into the Ast ECS via recursive decent
//While parsing we keep a mutable state to store entities and errors
#[derive(Clone)]
struct VisitorGraph<'a> {
    errors: Vec<ErrorInfo>,
    cursor: TreeCursor<'a>,
    dot: String,
    source: &'a Rope,
    root_name: Option<String>
}
impl<'a> Visitor<'a> for VisitorGraph<'a> {
    fn cursor(&self) -> &TreeCursor<'a> {
        &self.cursor
    }
    fn cursor_mut(&mut self) -> &mut TreeCursor<'a> {
        &mut self.cursor
    }
    fn push_err_raw(&mut self, err: ErrorInfo) {
        self.errors.push(err);
    }
    fn source(&self) -> &Rope {
        self.source
    }
}

impl<'a> VisitorGraph<'a> {
    fn add_constraint(&mut self, _: ConstraintDecl, _: GraphNode) {
        self.dot.push_str("a constraint!");
    }
    //get the current block header
    fn header(&self) -> Option<Node<'a>> {
        self.node().child_by_field_name("header")
    }
    //Push an error with location of the current block header
    fn push_error_blk<T: Into<String>>(&mut self, w: u32, error: T) {
        self.errors.push(ErrorInfo {
            location: node_range(self.header().unwrap(), self.source()),
            severity: DiagnosticSeverity::ERROR,
            weight: w,
            msg: error.into(),
        });
    }
}
impl<'b> SymbolSlice for VisitorGraph<'b> {
    fn slice_raw(&self, node: Span) -> Cow<'_, str> {
        self.source.byte_slice(node).into()
    }
}

//parse a namespace
fn visit_namespace(graph: &mut VisitorGraph) {
    loop {
        if graph.kind() == "namespace" {
            visit_children(graph, |state| {
                state.goto_field("name");
                if state.root_name.is_none() {
                    state.root_name = opt_path(state).map(|p|p.names[0].to_string());
                }
            });
        }
        if !graph.goto_next_sibling() {
            break;
        }
    }
}

fn visit_lang_lvl(graph: &mut VisitorGraph) {
    loop {
        if !graph.goto_next_sibling() {
            break;
        }
    }
}
fn visit_include(graph: &mut VisitorGraph) {
    loop {
        if graph.kind() == "blk" {
            match graph.header().unwrap().kind() {
                "lang_lvl" => visit_children(graph, visit_lang_lvl),
                "ref" => graph.push_error_blk(
                    30,
                    "unknown language level start with SMT-level, SAT-level or TYPE-level",
                ),
                _ => {
                    graph.push_error_blk(40, "expected a language level");
                }
            }
        }
        if !graph.goto_next_sibling() {
            break;
        }
    }
}
fn visit_import_decl(graph: &mut VisitorGraph) {
    loop {
        if graph.kind() == "ref" {
            visit_children(graph, |graph| {
                graph.goto_field("path");
                Some(())
            });
        }

        if !graph.goto_next_sibling() {
            break;
        }
    }
}
fn visit_import(graph: &mut VisitorGraph) {
    loop {
        if graph.kind() == "blk" {
            match graph.header().unwrap().kind() {
                "name" | "ref" => visit_children(graph, visit_import_decl),
                "incomplete_ref" => {
                    graph.push_error_blk(40, "incomplete import, please specify an alias");
                }
                _ => {
                    graph.push_error_blk(40, "expected a import declaration");
                }
            }
        }
        if !graph.goto_next_sibling() {
            break;
        }
    }
}
fn opt_name(graph: &mut VisitorGraph) -> Option<SymbolSpan> {
    if graph.kind() == "name" {
        if graph.node().is_missing() {
            Some(SymbolSpan {
                name: "__MISSING__".into(),
                span: graph.node().byte_range(),
            })
        } else {
            Some(SymbolSpan {
                name: graph.name(graph.node()),
                span: graph.node().byte_range(),
            })
        }
    } else {
        None
    }
}
fn opt_path(graph: &mut VisitorGraph) -> Option<Path> {
    if graph.kind() == "name" {
        opt_name(graph).map(|name| Path {
            names: vec![name.name],
            spans: vec![name.span],
        })
    } else if graph.kind() == "path" {
        if graph.child_by_name("tail").is_some() {
            graph.push_error(10, "tailing dot not supported");
        }
        visit_children(graph, |state| {
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
fn opt_int(node: Node, state: &mut VisitorGraph) -> Option<usize> {
    if let Ok(i) = state.slice(node).parse() {
        Some(i)
    } else {
        state.push_error_node(node, 20, "cant parse integer");
        None
    }
}
fn opt_cardinality(node: Node, state: &mut VisitorGraph) -> Option<Cardinality> {
    let begin = node.child_by_field_name("begin");
    let end = node.child_by_field_name("end");
    match (begin, end.map(|n| n.kind())) {
        (Some(begin), Some("int")) => Some(Cardinality::Range(
            opt_int(begin, state)?,
            opt_int(end.unwrap(), state)?,
        )),
        (Some(begin), Some("*")) => Some(Cardinality::From(opt_int(begin, state)?)),
        (None, Some("int")) => Some(Cardinality::Max(opt_int(end.unwrap(), state)?)),
        (_, _) => Some(Cardinality::Any),
    }
}

fn opt_number(state: &mut VisitorGraph) -> Option<f64> {
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
fn opt_aggreate_op(state: &mut VisitorGraph) -> Option<AggregateOP> {
    match state.slice(state.child_by_name("op")?).borrow() {
        "sum" => Some(AggregateOP::Sum),
        "avg" => Some(AggregateOP::Avg),
        _ => {
            state.push_error(30, "unknown aggregate function");
            None
        }
    }
}
fn opt_integer_op(state: &mut VisitorGraph) -> Option<IntegerOP> {
    match state.slice(state.child_by_name("op")?).borrow() {
        "floor" => Some(IntegerOP::Floor),
        "ceil" => Some(IntegerOP::Ceil),
        _ => {
            state.push_error(30, "unknown integer function");
            None
        }
    }
}
fn opt_function_args(state: &mut VisitorGraph) -> Option<Vec<Path>> {
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

fn opt_aggregate(state: &mut VisitorGraph) -> Option<Expr> {
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
            context: None,
        }),
        _ => {
            state.push_error(30, "to many arguments");
            None
        }
    }
}
fn opt_integer(state: &mut VisitorGraph) -> Option<Expr> {
    if state.child_by_name("tail").is_some() {
        state.push_error(10, "tailing comma not allowed");
    }
    let op = opt_integer_op(state)?;
    visit_children(state, |state| {
        if state.goto_field("arg") {
            let n: Box<ExprDecl> = opt_numeric(state)?.into();
            let out = Some(Expr::Integer{op: op.clone(), n});
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
fn opt_numeric(state: &mut VisitorGraph) -> Option<ExprDecl> {
    let span = state.node().byte_range();
    state.goto_named();
    match state.kind() {
        "path" => {
            let _ = opt_path(state)?;
            None
        }

        "number" => Some(Expr::Number(opt_number(state)?)),
        "string" => Some(Expr::String(opt_string(state)?)),
        "binary_expr" => {
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
        "function" => {match state.slice(state.child_by_name("op")?).borrow() {
            "sum" | "avg" => {
                opt_aggregate(state)
            },
            "len" => {
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
            },
            "floor" | "ceil" => {
                opt_integer(state)
            },
            _ => {
                state.push_error(30, "unknown function");
                None
            }
        }},
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

fn opt_constraint(state: &mut VisitorGraph) -> Option<ConstraintDecl> {
    let span = state.node().byte_range();
    state.goto_named();
    match state.kind() {
        "path" | "name" => {
            let _ = opt_path(state)?;
            None
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
fn visit_constraint(graph: &mut VisitorGraph, parent: GraphNode) {
    if let Some(cons) = opt_constraint(graph) {
        graph.add_constraint(cons, parent);
    }
}
fn opt_bool(graph: &mut VisitorGraph) -> bool {
    match graph.kind() {
        "true" => true,
        "false" => false,
        _ => false,
    }
}
fn opt_string(graph: &mut VisitorGraph) -> Option<String> {
    if graph.kind() == "string" {
        visit_children(graph, |state| {
            state.goto_kind("string_content");
            Some(
                state
                    .source()
                    .slice_raw(state.node().byte_range())
                    .to_string(),
            )
        })
    } else {
        None
    }
}

fn opt_attrib_expr(graph: &mut VisitorGraph) -> Option<Value> {
    graph.goto_named();
    match graph.kind() {
        "number" => Some(Value::Number(opt_number(graph)?)),
        "bool" => Some(Value::Bool(visit_children(graph, opt_bool))),
        "string" => Some(Value::String(opt_string(graph)?)),
        "path" => {
            graph.push_error(30, "attribute references are not supported");
            None
        }
        "binary_expr" | "nested_expr" | "aggregate" | "unary_expr" => {
            graph.push_error(30, "composit atttribute values are not supported");
            None
        }
        _ => None,
    }
}

fn opt_value(graph: &mut VisitorGraph) -> Value {
    match graph.kind() {
        "vector" => Value::Vector, //We dont parse vectors since they seem unsed
        "attributes" => Value::Attributes,
        "attrib_expr" => visit_children(graph, opt_attrib_expr).unwrap_or_default(),
        _ => Value::Void,
    }
}

fn visit_attribute_value(graph: &mut VisitorGraph, _: GraphNode) {
    graph.goto_field("name");
    let _ = opt_name(graph).unwrap();
    /*let sym = Symbol::Attribute(graph.ast.attributes.len());
    graph.push_child(parent, sym);
    graph.goto_field("value");
    let value = opt_value(graph);
    let has_children = matches!(&value, Value::Attributes);
    // TODO: push attribute
    if has_children {
        visit_children_arg(graph, sym, visit_attributes);
    }*/
}
fn visit_constraint_list(graph: &mut VisitorGraph, parent: GraphNode) {
    loop {
        if graph.kind() == "constraint" {
            visit_children_arg(graph, parent.clone(), visit_constraint);
        }
        if !graph.goto_next_sibling() {
            break;
        }
    }
}
fn visit_attributes(graph: &mut VisitorGraph, parent: &GraphNode) {
    // TODO: push attribute
    loop {
        match graph.kind() {
            "attribute_constraints" => {
                if graph.child_by_name("tail").is_some() {
                    graph.push_error(10, "tailing comma unsupported");
                }
                visit_children_arg(graph, parent.clone(), visit_constraint_list);
            }
            "attribute_constraint" => {
                visit_children(graph, |state| {
                    debug_assert!(state.goto_kind("constraint"));
                    visit_children_arg(state, parent.clone(), visit_constraint);
                });
            }
            "attribute_value" => {
                visit_children_arg(graph, parent.clone(), visit_attribute_value);
            }
            _ => {}
        }
        if !graph.goto_next_sibling() {
            break;
        }
    }
}

fn visit_feature(graph: &mut VisitorGraph, parent: &mut GraphNode, name: SymbolSpan, ty: Type) {
    let mut feature = GraphNode {
        name: name.name.to_string(),
        description: None,
        r#type: Some(ty),
        group_mode: None,
        cardinality: graph
            .node()
            .parent()
            .unwrap()
            .child_by_field_name("cardinality")
            .and_then(|n| {
                opt_cardinality(n, graph)
            }),
        parent: Some(Box::new(parent.clone()))
    };

    loop {
        match graph.cursor().node().kind() {
            "attributes" => {
                visit_children_arg(graph, &feature, visit_attributes);
            }
            "blk" => {
                visit_children_arg(graph, &mut feature, visit_blk_decl);
            }
            _ => {}
        }
        if !graph.goto_next_sibling() {
            break;
        }
    }

    let shape = Shape::by_mode(feature.group_mode.clone().unwrap_or(GroupMode::Optional));
    graph.dot.push_str(format!("{} [fillcolor=\"{}\" tooltip=\"Additional information\" shape=\"{}\"]\n", feature.name, FEATURE_COLOR, shape.as_str()).as_str());
    info!("[GRAPH] add Feature '{}'", feature.name);

    if !parent.group_mode.is_none() {
        let arrow_tail = ArrowEnd::tail(parent.group_mode.clone().unwrap());
        let arrow_head = ArrowEnd::head(parent.group_mode.clone().unwrap());
        
        graph.dot.push_str(format!("{} -> {} [arrowhead=\"{}\", arrowtail=\"{}\", dir=\"both\"]\n", parent.name, feature.name, arrow_tail.as_str(), arrow_head.as_str()).as_str());
        info!("[GRAPH] add link Feature->Feature from '{:?}'", parent.name);
    }
}

fn visit_ref(graph: &mut VisitorGraph, parent: Symbol, path: Path) {
    match parent {
        Symbol::Feature(..) => {
            graph.push_error(40, "features have to be separated by groups");
        }
        _ => {}
    }
    loop {
        if !graph.goto_next_sibling() {
            break;
        }
    }
}
fn visit_group(graph: &mut VisitorGraph, mut parent: &mut GraphNode, mode: GroupMode) {
    //let sym = Symbol::Group(graph.ast.groups.len());
    //graph.push_child(parent, sym);
    parent.group_mode = Some(mode);
    loop {
        if graph.kind() == "blk" {
            visit_children_arg(graph, &mut *parent, visit_blk_decl);
        }
        if !graph.goto_next_sibling() {
            break;
        }
    }
}
fn visit_blk_decl(graph: &mut VisitorGraph, parent: &mut GraphNode) {
    graph.goto_field("header");
    match graph.kind() {
        "name" => {
            let name = opt_name(graph).unwrap();
            visit_feature(graph, parent, name, Type::Bool);
        }
        "typed_feature" => {
            let (name, ty) = visit_children(graph, |graph| {
                graph.goto_field("type");
                let ty = match &*graph.slice_raw(graph.node().byte_range()) {
                    "Integer" | "Real" => Type::Real,
                    "String" => Type::String,
                    "Boolean" => Type::Bool,
                    _ => {
                        graph.push_error(30, "unknown type, interpreting as boolean");
                        Type::Bool
                    }
                };
                graph.goto_field("name");
                Some((opt_name(graph).unwrap(), ty))
            })
            .unwrap();
            visit_feature(graph, parent, name, ty);
        }
        /*"ref" => {
            let path = visit_children(graph, |state| {
                state.goto_field("path");
                let path = opt_path(state);
                if state.goto_field("alias") {
                    state.push_error(30, "imported features may not have an alias");
                }
                path
            })
            .unwrap();
            visit_ref(graph, parent, path);
        }*/
        "group_mode" => {
            let mode = match graph.node().child(0).unwrap().kind() {
                "mandatory" => GroupMode::Mandatory,
                "or" => GroupMode::Or,
                "optional" => GroupMode::Optional,
                "alternative" => GroupMode::Alternative,
                _ => GroupMode::Mandatory,
            };
            visit_group(graph, parent, mode);
        }
        "cardinality" => {
            let card = opt_cardinality(graph.node(), graph).unwrap_or(Cardinality::Any);
            visit_group(graph, parent, GroupMode::Cardinality(card));
        }
        _ => {
            graph.push_error(40, "expected a feature or group declaration");
        }
    }
}
fn visit_features(graph: &mut VisitorGraph) {
    let mut root: GraphNode = GraphNode::root(graph.root_name.clone());
    loop {
        if graph.kind() == "blk" {
            visit_children_arg(graph, &mut root, visit_blk_decl);
            //graph.dot.push_str(format!("{} [fillcolor=\"{}\" tooltip=\"Additional information\" shape=\"box\"]\n", root.name, FEATURE_COLOR).as_str());
            //info!("[GRAPH] add Root '{}'", root.name);
        }
        if !graph.goto_next_sibling() {
            break;
        }
    }
}
fn visit_constraint_decl(graph: &mut VisitorGraph) {
    loop {
        match graph.kind() {
            "constraint" | "ref" => visit_children_arg(graph, GraphNode::root(None), visit_constraint),
            "name" => visit_constraint(graph, GraphNode::root(None)),
            _ => {}
        }
        if graph.kind() == "ref" {
            if let Some(alias) = graph.child_by_name("alias") {
                graph.push_error_node(alias, 30, "alias not allowed here");
            }
        }
        if !graph.goto_next_sibling() {
            break;
        }
    }
}
fn visit_constraints(graph: &mut VisitorGraph) {
    loop {
        if graph.kind() == "blk" {
            let header = graph.header().unwrap();
            match header.kind() {
                "constraint" | "name" | "ref" => {
                    visit_children(graph, visit_constraint_decl);
                }
                _ => {
                    graph.push_error(40, "expected a constraint");
                }
            }
        }
        if !graph.goto_next_sibling() {
            break;
        }
    }
}
fn visit_top_lvl(graph: &mut VisitorGraph) {
    let mut top_level_order: Vec<Node> = Vec::new();
    loop {
        if graph.kind() == "blk" {
            let header = graph.header().unwrap();
            top_level_order.push(header);
            match header.kind() {
                "namespace" => visit_children(graph, visit_namespace),
                //"include" => visit_children(graph, visit_include),
                //"imports" => visit_children(graph, visit_import),
                "features" => visit_children(graph, visit_features),
                //"constraints" => visit_children(graph, visit_constraints),
                _ => {}
            }
        }
        if !graph.goto_next_sibling() {
            break;
        }
    }
}
//visits all valid children of a tree-sitter (red tree) recursively to translate them into the
//Graph
pub fn visit_root(source: Rope, tree: Tree, uri: Url) -> Graph {
    let initial = "digraph G {\nnode [style=filled fontname=\"Arial Unicode MS, Arial\"];\n\n".to_string();

    let mut graph = VisitorGraph {
        errors: Vec::new(),
        cursor: tree.walk(),
        dot: initial,
        source: &source,
        root_name: None
    };
    visit_children(&mut graph, visit_top_lvl);
    graph.dot.push_str("}");

    Graph {
        dot: graph.dot,
        uri
    }
}
