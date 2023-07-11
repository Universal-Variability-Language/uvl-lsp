use std::borrow::{Borrow, Cow};

use crate::core::*;
use ast::visitor::Visitor;
use ast::visitor::*;
use check::ErrorInfo;
use html_escape::encode_text;
use parse::*;
use ropey::Rope;
use tower_lsp::lsp_types::Url;
use tree_sitter::{Node, Tree, TreeCursor};

#[derive(Debug)]
pub struct Graph {
    pub dot: String,
    pub uri: Url,
}
impl Graph {
    pub fn new(source: Rope, tree: Tree, uri: Url) -> Self {
        visit_root(source, tree, uri)
    }
}

#[derive(Clone, Debug)]
pub enum GraphSymbol {
    Feature(String, String, Option<GroupMode>, Option<Type>), // name, description
    Group(String, String, GroupMode),                         // name, description
    Root(String),                                             // name
}

#[derive(Clone, Debug)]
pub struct GraphNode {
    pub name: String,
    pub description: Option<String>,
    pub r#type: Option<Type>,
    pub group_mode: Option<GroupMode>,
    pub cardinality: Option<Cardinality>,
    pub parent: Option<Box<GraphNode>>,
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
        GraphNode {
            name: String::default(),
            description: None,
            r#type: None,
            group_mode: None,
            cardinality: None,
            parent: None,
        }
    }
}

//Transform a tree-sitter tree into the Ast ECS via recursive decent
//While parsing we keep a mutable state to store entities and errors
#[derive(Clone)]
struct VisitorGraph<'a> {
    cursor: TreeCursor<'a>,
    dot: String,
    source: &'a Rope,
    root_name: Option<String>,
}
impl<'a> Visitor<'a> for VisitorGraph<'a> {
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

impl<'a> VisitorGraph<'a> {
    // Generate Graph Code:

    fn begin(&mut self) {
        self.dot.push_str(&"digraph FeatureModel {\nrankdir=\"TB\"\nnewrank=true\nnode [style=filled fontname=\"Arial Unicode MS, Arial\"];\n\n".to_string());
    }

    fn add_feature(&mut self, feature: GraphNode) {
        //info!("[GRAPH] add Feature '{}'", feature.name);
        let shape = Shape::by_mode(feature.group_mode.clone().unwrap_or(GroupMode::Optional));
        self.dot.push_str(
            format!(
                "{} [fillcolor=\"{}\" tooltip=\"Cardinality: {:?}\" shape=\"{}\"]\n",
                feature.name,
                FEATURE_COLOR,
                feature.cardinality,
                shape.as_str()
            )
            .as_str(),
        );
    }

    fn add_feature_link(&mut self, feature: GraphNode, parent: GraphNode) {
        if parent.group_mode.is_none() {
            return;
        }
        //info!("[GRAPH] add link Feature->Feature from '{:?}'", parent.name);
        let arrow_tail = ArrowEnd::tail(parent.group_mode.clone().unwrap());
        let arrow_head = ArrowEnd::head(parent.group_mode.clone().unwrap());

        self.dot.push_str(
            format!(
                "{} -> {} [arrowhead=\"{}\", arrowtail=\"{}\", dir=\"both\"]\n",
                parent.name,
                feature.name,
                arrow_tail.as_str(),
                arrow_head.as_str()
            )
            .as_str(),
        );
    }

    fn add_legend(&mut self) {
        self.dot.push_str(&"subgraph clusterLegend {
            label = \"Legend\"
            fontsize = 20
            node [ color=\"white\" ]
            legend [style=invis fontsize=\"0\"]
            subgraph AltOr {
              rank=none
              // or / alternative
              orNode [width=\"0.5\" height=\"0.5\" shape=\"invhouse\" color=\"black\" fontcolor=\"black\"  label=\"OR\" fillcolor=\"#ffffff\"]
              orLabel [style=invis fontsize=\"0\" height=\"0\" width=\"0\"]
              orNode -> orLabel [arrowhead=\"none\" arrowtail=\"dot\" dir=\"both\"]
              orNode -> orLabel [arrowhead=\"none\" arrowtail=\"dot\" dir=\"both\"]
      
              altNode [width=\"0.5\" height=\"0.5\" shape=\"invhouse\" color=\"black\" fontcolor=\"black\"  label=\"ALT\" fillcolor=\"#ffffff\"]
              altLabel [style=invis fontsize=\"0\" height=\"0\" width=\"0\"]
              altNode -> altLabel [arrowhead=\"none\" arrowtail=\"odot\" dir=\"both\"]
              altNode -> altLabel [arrowhead=\"none\" arrowtail=\"odot\" dir=\"both\"]
            }
            // mandatory / optional
            {rank=same; manOpt; manOpt2}
            manOpt [ color=\"white\" label=<<table border=\"0\" cellpadding=\"2\" cellspacing=\"0\" cellborder=\"0\">
              <tr><td align=\"right\" port=\"i1\">·</td></tr>
              <tr><td align=\"right\" port=\"i2\">·</td></tr>
              </table>> ]
            manOpt2 [ label=<<table border=\"0\" cellpadding=\"2\" cellspacing=\"0\" cellborder=\"0\">
              <tr><td align=\"left\" port=\"i1\" >·</td><td>mandatory</td></tr>
              <tr><td align=\"left\" port=\"i2\">·</td><td>optional</td></tr>
              </table>>]
            manOpt:i1 -> manOpt2:i1 [ arrowhead=\"dot\" ]
            manOpt:i2 -> manOpt2:i2 [ arrowhead=\"odot\"]
      
            // abstract / concrete
            abstCon [shape=\"box\" label=<<table border=\"0\" cellpadding=\"2\" cellspacing=\"0\" cellborder=\"0\">
              <tr><td align=\"right\" port=\"i1\" bgcolor=\"#ff0000\"><FONT COLOR=\"#ff0000\">░</FONT></td><td>abstract</td></tr>
              <tr><td align=\"right\" port=\"i2\" bgcolor=\"#550000\"><FONT COLOR=\"#550000\">░</FONT></td><td>concrete</td></tr>
              </table>> ]
          }
        ".to_string())
    }

    fn begin_constraints(&mut self) {
        self.dot.push_str(&"\n\nsubgraph cluster_constraints{
    label=\"Constraints\"
    constraints [shape=\"box\" color=\"white\" label=<<table border=\"0\" cellpadding=\"0\" cellspacing=\"0\" cellborder=\"0\">
    "
        .to_string());
    }

    fn add_constraint(&mut self, span: Span) {
        self.dot
            .push_str(&"    <tr><td align=\"left\">".to_string());
        self.dot
            .push_str(&encode_text(&self.source().slice_raw(span).to_string()));
        self.dot.push_str(&"</td></tr>\n".to_string());
    }

    fn end_constraints(&mut self) {
        self.dot.push_str(
            &"</table>>]
}\n"
            .to_string(),
        );
    }

    fn end(&mut self) {
        self.dot.push_str(&"}\n".to_string());
    }

    //get the current block header
    fn header(&self) -> Option<Node<'a>> {
        self.node().child_by_field_name("header")
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
                    state.root_name = opt_path(state).map(|p| p.names[0].to_string());
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
                _ => {}
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
                _ => {}
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
        None
    }
}
// returns cardinality for Node
fn opt_cardinality(node: Node, state: &mut VisitorGraph) -> Option<Cardinality> {
    let begin = node.child_by_field_name("begin");
    let end = node.child_by_field_name("end");
    match (begin, end.map(|n| n.kind())) {
        (Some(begin), Some("int")) => Some(Cardinality::Range(
            opt_int(begin, state)?,
            opt_int(end.unwrap(), state)?,
        )),
        (None, Some("int")) => Some(Cardinality::Range(0, opt_int(end.unwrap(), state)?)),
        (_, _) => Some(Cardinality::Range(0, 1)),
    }
}

fn opt_number(state: &mut VisitorGraph) -> Option<f64> {
    if let Ok(num) = state.slice(state.node()).parse() {
        Some(num)
    } else {
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
        _ => None,
    }
}
fn opt_integer_op(state: &mut VisitorGraph) -> Option<IntegerOP> {
    match state.slice(state.child_by_name("op")?).borrow() {
        "floor" => Some(IntegerOP::Floor),
        "ceil" => Some(IntegerOP::Ceil),
        _ => None,
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
    let args = opt_function_args(state)?;
    match args.len() {
        0 => None,
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
        _ => None,
    }
}
fn opt_integer(state: &mut VisitorGraph) -> Option<Expr> {
    let op = opt_integer_op(state)?;
    visit_children(state, |state| {
        if state.goto_field("arg") {
            let n: Box<ExprDecl> = opt_numeric(state)?.into();
            let out = Some(Expr::Integer { op: op.clone(), n });
            out
        } else {
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
                    None
                }
            })
        }
        "nested_expr" => visit_children(state, opt_numeric).map(|c| c.content),
        "function" => match state.slice(state.child_by_name("op")?).borrow() {
            "sum" | "avg" => opt_aggregate(state),
            "len" => visit_children(state, |state| {
                if state.goto_field("arg") {
                    Some(Expr::Len(opt_numeric(state)?.into()))
                } else {
                    None
                }
            }),
            "floor" | "ceil" => opt_integer(state),
            _ => None,
        },
        _ => None,
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
fn visit_constraint(graph: &mut VisitorGraph, _: GraphNode, _: &bool) {
    graph.add_constraint(graph.node().byte_range());
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
        visit_children(graph, |graph| {
            graph.goto_kind("string_content");
            Some(
                graph
                    .source()
                    .slice_raw(graph.node().byte_range())
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
        "path" => None,
        "binary_expr" | "nested_expr" | "aggregate" | "unary_expr" => None,
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

fn visit_attribute_value(graph: &mut VisitorGraph, _: GraphNode, _: &bool) {
    graph.goto_field("name");
    let _ = opt_name(graph).unwrap();
}
fn visit_constraint_list(graph: &mut VisitorGraph, parent: GraphNode, _: &bool) {
    loop {
        if graph.kind() == "constraint" {
            visit_children_arg(graph, parent.clone(), &false, visit_constraint);
        }
        if !graph.goto_next_sibling() {
            break;
        }
    }
}
fn visit_attributes(graph: &mut VisitorGraph, parent: &GraphNode, _: &bool) {
    loop {
        match graph.kind() {
            "attribute_constraints" => {
                visit_children_arg(graph, parent.clone(), &false, visit_constraint_list);
            }
            "attribute_constraint" => {
                visit_children(graph, |state| {
                    debug_assert!(state.goto_kind("constraint"));
                    visit_children_arg(state, parent.clone(), &false, visit_constraint);
                });
            }
            "attribute_value" => {
                visit_children_arg(graph, parent.clone(), &false, visit_attribute_value);
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
            .and_then(|n| opt_cardinality(n, graph)),
        parent: Some(Box::new(parent.clone())),
    };

    loop {
        match graph.cursor().node().kind() {
            "attributes" => {
                visit_children_arg(graph, &feature, &false, visit_attributes);
            }
            "blk" => {
                visit_children_arg(graph, &mut feature, &false, visit_blk_decl);
            }
            _ => {}
        }
        if !graph.goto_next_sibling() {
            break;
        }
    }

    graph.add_feature(feature.clone());
    graph.add_feature_link(feature, parent.clone());
}

fn visit_ref(graph: &mut VisitorGraph, _: &mut GraphNode, _: Path) {
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
            visit_children_arg(graph, &mut *parent, &false, visit_blk_decl);
        }
        if !graph.goto_next_sibling() {
            break;
        }
    }
}
fn visit_blk_decl(graph: &mut VisitorGraph, parent: &mut GraphNode, _: &bool) {
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
                    _ => Type::Bool,
                };
                graph.goto_field("name");
                Some((opt_name(graph).unwrap(), ty))
            })
            .unwrap();
            visit_feature(graph, parent, name, ty);
        }
        "ref" => {
            let path = visit_children(graph, |state| {
                state.goto_field("path");
                opt_path(state)
            })
            .unwrap();
            visit_ref(graph, parent, path);
        }
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
            let card = opt_cardinality(graph.node(), graph).unwrap_or(Cardinality::Fixed);
            visit_group(graph, parent, GroupMode::Cardinality(card));
        }
        _ => {}
    }
}
fn visit_features(graph: &mut VisitorGraph) {
    let mut root: GraphNode = GraphNode::root(graph.root_name.clone());
    loop {
        if graph.kind() == "blk" {
            visit_children_arg(graph, &mut root, &false, visit_blk_decl);
        }
        if !graph.goto_next_sibling() {
            break;
        }
    }
}
fn visit_constraint_decl(graph: &mut VisitorGraph) {
    loop {
        match graph.kind() {
            "constraint" | "ref" => {
                visit_children_arg(graph, GraphNode::root(None), &false, visit_constraint)
            }
            "name" => visit_constraint(graph, GraphNode::root(None), &false),
            _ => {}
        }
        if !graph.goto_next_sibling() {
            break;
        }
    }
}
fn visit_constraints(graph: &mut VisitorGraph) {
    let mut has_constraints = false;
    loop {
        if graph.kind() == "blk" {
            let header = graph.header().unwrap();
            match header.kind() {
                "constraint" | "name" | "ref" => {
                    if !has_constraints {
                        graph.begin_constraints();
                        has_constraints = true;
                    }

                    visit_children(graph, visit_constraint_decl);
                }
                _ => {}
            }
        }
        if !graph.goto_next_sibling() {
            break;
        }
    }
    if has_constraints {
        graph.end_constraints();
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
                // "include" => visit_children(graph, visit_include),
                // "imports" => visit_children(graph, visit_import),
                "features" => visit_children(graph, visit_features),
                "constraints" => visit_children(graph, visit_constraints),
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
    let mut graph = VisitorGraph {
        cursor: tree.walk(),
        dot: "".to_string(),
        source: &source,
        root_name: None,
    };
    graph.begin();
    visit_children(&mut graph, visit_top_lvl);
    //graph.add_legend();
    graph.end();

    Graph {
        dot: graph.dot,
        uri,
    }
}

// Constants for Graph Drawing:

const FEATURE_COLOR: &str = "#CCCCFD";
const FEATURE_ABSTRACT_COLOR: &str = "#F2F2FF";

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
    Tee,
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
            _ => Self::None,
        }
    }
    fn tail(mode: GroupMode) -> Self {
        match mode {
            GroupMode::Optional => Self::DotEmpty,
            GroupMode::Mandatory => Self::DotFilled,
            _ => Self::None,
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
    HouseInverted,
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
            _ => Self::Box,
        }
    }
}
