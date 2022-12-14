use crate::check::ErrorInfo;
use crate::parse::{parse_name, parse_path};
use crate::util::{self, node_range};
use enum_kinds;
use itertools::{Either, Itertools};
use lazy_static::lazy_static;
use log::info;
use petgraph::prelude::*;
use ropey::Rope;
use std::collections::HashMap;
use std::hash::Hash;
use std::path::Component;
use tokio::time::Instant;
use tower_lsp::lsp_types::{DiagnosticSeverity, Url};
use tree_sitter::{Node, QueryCursor, Tree};
use ustr::Ustr;

/*
 * Here we transform the loose tree-sitter syntax tree(Green tree) into a more fixed
 * according to the UVL-grammar syntax tree
 * This happens in two steps
 * 1. Extract relevant symboles like features or imports using queries
 * 2. Linke those symboles using a second set of queries
 *
 * We also parse constraints into a fixed format for easy postprocessing
 * parse errors are stored for the later check pass.
 *
 * Additionally a index for all named nodes is created to provide esay look up for paths
 * */
lazy_static! {
    pub static ref TS: util::ParseConstants = util::ParseConstants::new();
}

fn uri_to_path(uri: &Url) -> Option<Vec<Ustr>> {
    let mut p = uri.to_file_path().ok()?;
    p.set_extension("");
    p.components()
        .filter_map(|c| match c {
            Component::Normal(os) => os.to_str().map(|s| Some(s.into())),
            _ => None,
        })
        .collect()
}

fn insert_multi<K, V>(map: &mut HashMap<K, Vec<V>>, k: K, v: V)
where
    K: Hash + Eq,
{
    if let Some(old) = map.get_mut(&k) {
        old.push(v)
    } else {
        map.insert(k, vec![v]);
    }
}
fn containing_node(node: Node) -> Node {
    match node.kind() {
        "attribute_value"
        | "attribute_constraints"
        | "attribute_constraint"
        | "blk"
        | "source_file" => node,
        _ => containing_node(node.parent().unwrap()),
    }
}
pub type Span = std::ops::Range<usize>;
#[derive(Clone, Debug)]
pub struct SymbolSpan {
    pub name: Ustr,
    pub span: Span,
}
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Path {
    pub names: Vec<Ustr>,
    pub spans: Vec<Span>,
}

impl Path {
    fn append(&self, arg: &SymbolSpan) -> Path {
        let mut new = self.clone();
        new.names.push(arg.name);
        new.spans.push(arg.span.clone());
        new
    }
    pub fn range(&self) -> Span {
        if self.spans.len() > 0 {
            self.spans[0].start..self.spans.last().unwrap().end
        } else {
            0..0
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Type {
    String,
    Bool,
    Group,
    Number,
    Vector,
    Attributes,
    Namespace,
    Feature,
    Void,
}

#[derive(Clone, Debug)]
pub enum GroupMode {
    Or,
    Alternative,
    Optional,
    Mandatory,
    Cardinality(Cardinality),
}
#[derive(Clone, Debug)]
pub enum Cardinality {
    From(usize),
    Range(usize, usize),
    Max(usize),
    Any,
}
#[derive(Clone, Debug)]
pub enum LanguageLevelMajor {
    SAT,
    SMT,
}
#[derive(Clone, Debug)]
pub enum LanguageLevelSMT {
    Any,
    FeatureCardinality,
    Aggregate,
}
#[derive(Clone, Debug)]
pub enum LanguageLevelSAT {
    Any,
    GroupCardinality,
}
#[derive(Clone, Debug)]
pub enum LanguageLevel {
    SAT(Vec<LanguageLevelSAT>),
    SMT(Vec<LanguageLevelSMT>),
}
#[derive(Clone, Debug)]
pub struct Feature {
    pub name: SymbolSpan,
    pub cardinality: Option<Cardinality>,
}
#[derive(Clone, Debug)]
pub struct Import {
    pub path: Path,
    pub alias: Option<SymbolSpan>,
}
#[derive(Clone, Debug)]
pub struct Dir {
    name: Ustr,
}
#[derive(Clone, Debug)]
pub struct Namespace {
    pub prefix: Path,
}
#[derive(Clone, Debug)]
pub struct Group {
    pub mode: GroupMode,
}
#[derive(Clone, Debug)]
pub struct Reference {
    pub path: Path,
    pub ty: Type,
}
#[derive(Clone, Debug)]
pub struct Attribute {
    pub name: SymbolSpan,
    pub value: Value,
    pub prefix: Vec<Ustr>,
}
impl Attribute {
    fn symbol(&self, offset: usize) -> Symbol {
        match self.value {
            Value::Void => Symbol::Void(offset as u32),
            Value::Vector => Symbol::Vector(offset as u32),
            Value::Bool(..) => Symbol::Bool(offset as u32),
            Value::Attributes => Symbol::Attributes(offset as u32),
            Value::Number(..) => Symbol::Number(offset as u32),
            Value::String(..) => Symbol::String(offset as u32),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, enum_kinds::EnumKind)]
#[enum_kind(SymbolKind)]
pub enum Symbol {
    Feature(u32),
    Number(u32),
    Bool(u32),
    String(u32),
    Vector(u32),
    Void(u32),
    Constraint(u32),
    Attributes(u32),
    Reference(u32),
    Group(u32),
    Import(u32),
    Dir(u32),
    LangLvl(u32),
    Root,
}
impl Symbol {
    fn offset(&self) -> u32 {
        match self {
            Self::Dir(id)
            | Self::Feature(id)
            | Self::Bool(id)
            | Self::Number(id)
            | Self::String(id)
            | Self::Vector(id)
            | Self::Constraint(id)
            | Self::Attributes(id)
            | Self::Reference(id)
            | Self::Group(id)
            | Self::Void(id)
            | Self::LangLvl(id)
            | Self::Import(id) => *id,
            _ => panic!(),
        }
    }
    pub fn is_value(&self) -> bool {
        match self {
            Self::Void(..)
            | Self::Bool(..)
            | Self::Number(..)
            | Self::String(..)
            | Self::Vector(..)
            | Self::Attributes(..) => true,
            _ => false,
        }
    }
    pub fn ty(&self) -> Type {
        match self {
            Symbol::String(..) => Type::String,
            Symbol::Bool(..) => Type::Bool,
            Symbol::Vector(..) => Type::Vector,
            Symbol::Number(..) => Type::Number,
            Symbol::Attributes(..) => Type::Attributes,
            Symbol::Feature(..) => Type::Feature,
            _ => Type::Void,
        }
    }
}
#[derive(Clone, Debug)]
pub enum Value {
    Void,
    Number(f64),
    String(String),
    Vector,
    Bool(bool),
    Attributes,
}

#[derive(Clone, Debug)]
pub enum NumericOP {
    Add,
    Sub,
    Div,
    Mul,
}

impl NumericOP {
    fn parse(op: &str) -> Option<Self> {
        match op {
            "+" => Some(NumericOP::Add),
            "-" => Some(NumericOP::Sub),
            "*" => Some(NumericOP::Mul),
            "/" => Some(NumericOP::Div),
            _ => None,
        }
    }
}
#[derive(Clone, Debug)]
pub enum LogicOP {
    And,
    Or,
    Implies,
    Equiv,
}

impl LogicOP {
    fn parse(op: &str) -> Option<Self> {
        match op {
            "&" => Some(LogicOP::And),
            "|" => Some(LogicOP::Or),
            "=>" => Some(LogicOP::Implies),
            "<=>" => Some(LogicOP::Equiv),
            _ => None,
        }
    }
}
#[derive(Clone, Debug)]
pub enum AggregateOP {
    Avg,
    Sum,
}

impl AggregateOP {
    fn parse(source: &String, op: Node) -> Option<Self> {
        match &source[op.byte_range()] {
            "avg" => Some(AggregateOP::Avg),
            "sum" => Some(AggregateOP::Sum),
            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
pub enum EquationOP {
    Greater,
    Smaller,
    Equal,
}

impl EquationOP {
    fn parse(op: &str) -> Option<Self> {
        match op {
            ">" => Some(Self::Greater),
            "<" => Some(Self::Smaller),
            "==" => Some(Self::Equal),
            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
pub enum Constraint {
    Constant(bool),
    Equation {
        op: EquationOP,
        lhs: Box<Numeric>,
        rhs: Box<Numeric>,
    },
    Logic {
        op: LogicOP,
        lhs: Box<Constraint>,
        rhs: Box<Constraint>,
    },
    Ref(Symbol),
    Not(Box<Constraint>),
}

#[derive(Clone, Debug)]
pub enum Numeric {
    Number(f64),
    Ref(Symbol),
    Binary {
        op: NumericOP,
        rhs: Box<Numeric>,
        lhs: Box<Numeric>,
    },
    Aggregate {
        op: AggregateOP,
        context: Option<Symbol>,
        query: Path,
    },
}
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum LocalEdge {
    Containes,
}

#[derive(Clone, Debug)]
pub struct FileGraph {
    namespace: Option<Path>,
    features: Vec<Feature>,
    attributes: Vec<Attribute>,
    references: Vec<Reference>,
    directories: Vec<Vec<Ustr>>,
    imports: Vec<Import>,
    groups: Vec<Group>,
    constraints: Vec<Constraint>,
    root_attributes: Vec<u32>,
    graph: DiGraphMap<Symbol, LocalEdge>,
    index: HashMap<Vec<Ustr>, Vec<Symbol>>,
    lang_lvls: Vec<LanguageLevel>,
    //For the most part we ignore syntax errors while building the file graph
    //But while parseing constraints and values we can cheaply check for correctness
    pub parse_errors: Vec<ErrorInfo>,
    pub tree: Tree,
    pub name: Ustr,
    pub path: Vec<Ustr>,
    pub source: String,
    pub rope: Rope,
    pub uri: Url,
    pub ts2sym: HashMap<usize, Symbol>,
    pub timestamp: Instant,
}
impl FileGraph {
    fn parse_lang_lvl(&mut self, node: Node) -> Option<LanguageLevel> {
        if node.kind() != "lang_lvl" {
            return None;
        }
        let mut cursor = node.walk();
        cursor.goto_first_child();
        let mut out = None;
        loop {
            if cursor.node().kind() == "major_lvl" {
                if out.is_some() {
                    self.parse_errors.push(ErrorInfo {
                        location: node_range(cursor.node(), &self.rope),
                        severity: DiagnosticSeverity::ERROR,
                        weight: 30,
                        msg: "duplicate major level, please pick a minor level".into(),
                    });
                    return None;
                } else {
                    cursor.goto_first_child();
                    match cursor.node().kind() {
                        "SMT-level" => out = Some(LanguageLevel::SMT(vec![])),
                        "SAT-level" => out = Some(LanguageLevel::SAT(vec![])),
                        _ => {
                            self.parse_errors.push(ErrorInfo {
                                location: node_range(cursor.node(), &self.rope),
                                severity: DiagnosticSeverity::ERROR,
                                weight: 30,
                                msg: "unknown major language level".into(),
                            });
                            return None;
                        }
                    }
                    cursor.goto_parent();
                }
            }
            if cursor.node().kind() == "minor_lvl" {
                if let Some(major) = out.as_mut() {
                    cursor.goto_first_child();
                    match major {
                        LanguageLevel::SMT(v) => match cursor.node().kind() {
                            "*" => v.push(LanguageLevelSMT::Any),
                            "feature-cardinality" => v.push(LanguageLevelSMT::FeatureCardinality),
                            "aggregate-function" => v.push(LanguageLevelSMT::Aggregate),
                            "group-cardinality" => {
                                self.parse_errors.push(ErrorInfo {
                                    location: node_range(cursor.node(), &self.rope),
                                    severity: DiagnosticSeverity::ERROR,
                                    weight: 30,
                                    msg: "not allowed under SMT".into(),
                                });
                                return None;
                            }
                            _ => {
                                self.parse_errors.push(ErrorInfo {
                                    location: node_range(cursor.node(), &self.rope),
                                    severity: DiagnosticSeverity::ERROR,
                                    weight: 30,
                                    msg: "unknown SMT level".into(),
                                });
                                return None;
                            }
                        },
                        LanguageLevel::SAT(v) => match cursor.node().kind() {
                            "*" => v.push(LanguageLevelSAT::Any),
                            "group-cardinality" => v.push(LanguageLevelSAT::GroupCardinality),
                            "feature-cardinality" | "aggregate-function" => {
                                self.parse_errors.push(ErrorInfo {
                                    location: node_range(cursor.node(), &self.rope),
                                    severity: DiagnosticSeverity::ERROR,
                                    weight: 30,
                                    msg: "not allowed under SAT".into(),
                                });
                                return None;
                            }
                            _ => {
                                self.parse_errors.push(ErrorInfo {
                                    location: node_range(cursor.node(), &self.rope),
                                    severity: DiagnosticSeverity::ERROR,
                                    weight: 30,
                                    msg: "unknown SAT level".into(),
                                });
                                return None;
                            }
                        },
                    }
                    cursor.goto_parent();
                } else {
                    self.parse_errors.push(ErrorInfo {
                        location: node_range(cursor.node(), &self.rope),
                        severity: DiagnosticSeverity::ERROR,
                        weight: 30,
                        msg: "missing major level, please specify SMT or SAT level".into(),
                    });
                    return None;
                }
            }
            if cursor.node().kind() == "name" {
                self.parse_errors.push(ErrorInfo {
                    location: node_range(cursor.node(), &self.rope),
                    severity: DiagnosticSeverity::ERROR,
                    weight: 30,
                    msg: "unknown language level".into(),
                });
            }

            if !cursor.goto_next_sibling() {
                break;
            }
        }
        out
    }

    fn parse_cardinality(&mut self, node: Node, source: &String) -> Cardinality {
        let begin = node.child_by_field_name("begin");
        let end = node.child_by_field_name("end");
        match (begin, end.map(|n| n.kind())) {
            (Some(begin), Some("int")) => Cardinality::Range(
                source[begin.byte_range()].parse().unwrap(),
                source[end.unwrap().byte_range()].parse().unwrap(),
            ),
            (Some(begin), Some("*")) => {
                Cardinality::From(source[begin.byte_range()].parse().unwrap())
            }
            (None, Some("int")) => {
                Cardinality::Max(source[end.unwrap().byte_range()].parse().unwrap())
            }
            (_, _) => Cardinality::Any,
        }
    }
    fn parse_feature(&mut self, node: Node, source: &String) -> Feature {
        let name = parse_name(node.child_by_field_name("header").unwrap(), source).unwrap();
        let cardinality = node
            .child_by_field_name("cardinality")
            .map(|c| self.parse_cardinality(c, source));
        Feature { name, cardinality }
    }
    pub fn duplicate_symboles<'a>(&'a self) -> impl Iterator<Item = (Symbol, Symbol)> + 'a {
        self.index.values().flat_map(|i| {
            i.iter().tuple_windows().filter_map(|(a, b)| {
                if SymbolKind::from(a) == SymbolKind::from(b) {
                    Some((*a, *b))
                } else {
                    None
                }
            })
        })
    }
    pub fn imports(&self) -> impl Iterator<Item = Symbol> {
        (0..self.imports.len())
            .into_iter()
            .map(|i| Symbol::Import(i as u32))
    }
    pub fn import_path(&self, sym: Symbol) -> &[Ustr] {
        self.imports[sym.offset() as usize].path.names.as_slice()
    }
    pub fn references(&self) -> impl Iterator<Item = &Reference> {
        self.references.iter()
    }
    pub fn lookup<'a>(&'a self, path: &[Ustr]) -> impl Iterator<Item = Symbol> + 'a {
        self.index
            .get(path)
            .into_iter()
            .flat_map(|i| i.iter().cloned())
    }
    pub fn imports_under<'a>(&'a self, sym: Symbol) -> impl Iterator<Item = Symbol> + 'a {
        if sym == Symbol::Root {
            Either::Left(self.imports())
        } else {
            Either::Right(self.children(sym).filter_map(|(_, sym)| match sym {
                Symbol::Import(..) => Some(sym),
                _ => None,
            }))
        }
    }
    fn parse_path(&mut self, source: &String, node: Node) -> Option<Path> {
        if let Some(path) = parse_path(node, source) {
            Some(path)
        } else {
            self.parse_errors.push(ErrorInfo {
                location: node_range(node, &self.rope),
                severity: DiagnosticSeverity::ERROR,
                weight: 30,
                msg: "expected a path".into(),
            });
            None
        }
    }
    fn add_reference(&mut self, source: &String, node: Node, required_type: Type) -> Symbol {
        self.references.push(Reference {
            path: parse_path(node, source).unwrap(),
            ty: required_type,
        });
        Symbol::Reference(self.references.len() as u32 - 1)
    }
    fn parse_numeric(&mut self, source: &String, node: Node) -> Option<Numeric> {
        match node.kind() {
            "path" | "name" => Some(Numeric::Ref(self.add_reference(source, node, Type::Number))),
            "number" => Some(Numeric::Number(source[node.byte_range()].parse().unwrap())),
            "binary_expr" => {
                if let Some(op) = NumericOP::parse(node.child_by_field_name("op").unwrap().kind()) {
                    let lhs = self.parse_numeric(source, node.child_by_field_name("rhs")?)?;
                    let rhs = self.parse_numeric(source, node.child_by_field_name("lhs")?)?;
                    Some(Numeric::Binary {
                        op,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    })
                } else {
                    self.parse_errors.push(ErrorInfo {
                        location: node_range(node, &self.rope),
                        severity: DiagnosticSeverity::ERROR,
                        weight: 30,
                        msg: "expected a number found a constraint".into(),
                    });
                    None
                }
            }

            "aggregate" => {
                if let Some(op) =
                    AggregateOP::parse(source, node.child_by_field_name("op").unwrap())
                {
                    if let Some(ctx) = node.child_by_field_name("context") {
                        let path = self.parse_path(source, ctx)?;
                        self.references.push(Reference {
                            path,
                            ty: Type::Feature,
                        });
                        let id = Symbol::Reference(self.references.len() as u32 - 1);

                        Some(Numeric::Aggregate {
                            op,
                            context: Some(id),
                            query: self
                                .parse_path(source, node.child_by_field_name("query").unwrap())?,
                        })
                    } else {
                        Some(Numeric::Aggregate {
                            op,
                            context: None,
                            query: self
                                .parse_path(source, node.child_by_field_name("query").unwrap())?,
                        })
                    }
                } else {
                    self.parse_errors.push(ErrorInfo {
                        location: node_range(node, &self.rope),
                        severity: DiagnosticSeverity::ERROR,
                        weight: 30,
                        msg: "unknown aggregate function".into(),
                    });
                    None
                }
            }

            "nested_expr" => self.parse_numeric(source, node.named_child(0)?),
            "bool" | "unary_expr" => {
                self.parse_errors.push(ErrorInfo {
                    location: node_range(node, &self.rope),
                    severity: DiagnosticSeverity::ERROR,
                    weight: 30,
                    msg: "expected a number found a constraint".into(),
                });
                None
            }

            _ => None,
        }
    }
    fn parse_constraint(&mut self, source: &String, node: Node) -> Option<Constraint> {
        match node.kind() {
            "constraint" => self.parse_constraint(source, node.named_child(0)?),
            "path" | "name" => Some(Constraint::Ref(self.add_reference(
                source,
                node,
                Type::Feature,
            ))),
            "bool" => Some(Constraint::Constant(match &source[node.byte_range()] {
                "true" => true,
                "false" => false,
                _ => panic!(),
            })),
            "nested_expr" => self.parse_constraint(source, node.named_child(0)?),
            "unary_expr" => match node.child_by_field_name("op").unwrap().kind() {
                "!" => {
                    let out = Some(Constraint::Not(Box::new(
                        self.parse_constraint(source, node.child_by_field_name("lhs").unwrap())?,
                    )));
                    out
                }
                s => {
                    self.parse_errors.push(ErrorInfo {
                        location: node_range(node, &self.rope),
                        severity: DiagnosticSeverity::ERROR,
                        weight: 50,
                        msg: format!("unknown unary operator {}", s),
                    });
                    None
                }
            },
            "binary_expr" => {
                if let Some(op) = LogicOP::parse(node.child_by_field_name("op").unwrap().kind()) {
                    let lhs = self.parse_constraint(source, node.child_by_field_name("rhs")?)?;
                    let rhs = self.parse_constraint(source, node.child_by_field_name("lhs")?)?;
                    Some(Constraint::Logic {
                        op,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    })
                } else if let Some(op) =
                    EquationOP::parse(node.child_by_field_name("op").unwrap().kind())
                {
                    let lhs = self.parse_numeric(source, node.child_by_field_name("rhs")?)?;
                    let rhs = self.parse_numeric(source, node.child_by_field_name("lhs")?)?;
                    Some(Constraint::Equation {
                        op,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    })
                } else {
                    self.parse_errors.push(ErrorInfo {
                        location: node_range(node, &self.rope),
                        severity: DiagnosticSeverity::ERROR,
                        weight: 30,
                        msg: "expected a constraint found a number".into(),
                    });
                    None
                }
            }
            "aggregate" | "number" => {
                self.parse_errors.push(ErrorInfo {
                    location: node_range(node, &self.rope),
                    severity: DiagnosticSeverity::ERROR,
                    weight: 30,
                    msg: "expected a constraint found a numeric expression".into(),
                });
                None
            }
            _ => {
                panic!("unknown constraint kind  {}", node.kind());
            }
        }
    }
    pub fn prefix(&self, sym: Symbol) -> &[Ustr] {
        match sym {
            Symbol::Feature(i) => std::slice::from_ref(&self.features[i as usize].name.name),
            Symbol::Number(i)
            | Symbol::String(i)
            | Symbol::Attributes(i)
            | Symbol::Bool(i)
            | Symbol::Void(i)
            | Symbol::Vector(i) => self.attributes[i as usize].prefix.as_slice(),
            Symbol::Dir(i) => self.directories[i as usize].as_slice(),
            Symbol::Import(i) => {
                if let Some(alias) = self.imports[i as usize].alias.as_ref() {
                    std::slice::from_ref(&alias.name)
                } else {
                    self.imports[i as usize].path.names.as_slice()
                }
            }

            _ => &[],
        }
    }
    pub fn range(&self, sym: Symbol) -> Span {
        match sym {
            Symbol::Reference(id) => self.references[id as usize].path.range(),
            Symbol::Number(id)
            | Symbol::Attributes(id)
            | Symbol::String(id)
            | Symbol::Void(id)
            | Symbol::Vector(id)
            | Symbol::Bool(id) => self.attributes[id as usize].name.span.clone(),
            Symbol::Feature(id) => self.features[id as usize].name.span.clone(),
            Symbol::Import(id) => self.imports[id as usize].path.range(),
            _ => unimplemented!(),
        }
    }
    //All attributes under root
    pub fn children_attributes<'a>(
        &'a self,
        root: Symbol,
    ) -> impl Iterator<Item = (&'a [Ustr], Symbol)> + 'a {
        if matches!(root, Symbol::Root) {
            Either::Left(
                (0..self.attributes.len())
                    .into_iter()
                    .map(move |i| self.attributes[i].symbol(i))
                    .filter_map(move |i| {
                        let prefix = &self.prefix(i);
                        if prefix.len() <= 1 {
                            None
                        } else {
                            Some((&prefix[1..], i))
                        }
                    }),
            )
        } else {
            let mut stack = vec![];
            let base_len = 1;
            for (_, b, _) in self.graph.edges(root) {
                stack.push(b);
            }
            Either::Right(std::iter::from_fn(move || loop {
                if let Some(sym) = stack.pop().map(|sym| {
                    for (_, b, _) in self.graph.edges(sym) {
                        stack.push(b);
                    }
                    sym
                }) {
                    if sym.is_value() {
                        return Some((&self.prefix(sym)[base_len..], sym));
                    }
                } else {
                    return None;
                }
            }))
        }
    }
    pub fn children<'a>(&'a self, root: Symbol) -> impl Iterator<Item = (&'a [Ustr], Symbol)> + 'a {
        if matches!(root, Symbol::Root) {
            Either::Left(self.all_named_symboles().map(|sym| (self.prefix(sym), sym)))
        } else {
            let mut stack = vec![];
            let base_len = self.prefix(root).len();
            for (_, b, _) in self
                .graph
                .edges(root)
                .filter(|(_, b, _)| self.prefix(*b).len() > base_len)
            {
                stack.push(b);
            }
            Either::Right(std::iter::from_fn(move || {
                stack.pop().map(|sym| {
                    for (_, b, _) in self
                        .graph
                        .edges(sym)
                        .filter(|(_, b, _)| self.prefix(*b).len() > self.prefix(sym).len())
                    {
                        stack.push(b);
                    }
                    (&self.prefix(sym)[base_len..], sym)
                })
            }))
        }
    }
    pub fn owner(&self, sym: Symbol) -> Symbol {
        self.graph
            .edges_directed(sym, Incoming)
            .find_map(|e| {
                if matches!(e.weight(), LocalEdge::Containes) {
                    Some(e.source())
                } else {
                    None
                }
            })
            .unwrap()
    }

    pub fn all_named_symboles<'a>(&'a self) -> impl Iterator<Item = Symbol> + 'a {
        (0..self.imports.len())
            .into_iter()
            .map(|i| Symbol::Import(i as u32))
            .chain(
                (0..self.directories.len())
                    .into_iter()
                    .map(|i| Symbol::Dir(i as u32)),
            )
            .chain(
                (0..self.features.len())
                    .into_iter()
                    .map(|i| Symbol::Feature(i as u32)),
            )
            .chain(
                (0..self.attributes.len())
                    .into_iter()
                    .map(move |i| self.attributes[i].symbol(i)),
            )
    }

    fn build(&mut self, source: &String) {
        let mut cursor = QueryCursor::new();
        let cap_names = &TS.queries.extract_symboles.capture_names();
        for i in cursor.matches(
            &TS.queries.extract_symboles,
            self.tree.clone().root_node(),
            source.as_bytes(),
        ) {
            let m = &i.captures[0];
            let n = m.node;
            match cap_names[m.index as usize].as_str() {
                "feature" => {
                    let feature = self.parse_feature(n, source);
                    self.features.push(feature);
                    let sym = Symbol::Feature(self.features.len() as u32 - 1);
                    self.ts2sym.insert(containing_node(n).id(), sym);
                }
                "feature_ref" => {
                    let id = self.add_reference(source, n, Type::Feature);
                    self.ts2sym.insert(containing_node(n).id(), id);
                }
                "import_name" => {
                    let path = parse_path(n, source).unwrap();
                    self.imports.push(Import { path, alias: None });
                    self.ts2sym.insert(
                        containing_node(n).id(),
                        Symbol::Import(self.imports.len() as u32 - 1),
                    );
                }
                "import_ref" => {
                    let path = parse_path(n.child_by_field_name("path").unwrap(), source).unwrap();
                    let alias = n
                        .child_by_field_name("alias")
                        .map(|alias| parse_name(alias, source))
                        .flatten();
                    self.imports.push(Import { path, alias });
                    self.ts2sym.insert(
                        containing_node(n).id(),
                        Symbol::Import(self.imports.len() as u32 - 1),
                    );
                }
                "namespace" => {
                    let name = parse_path(n, source).unwrap();
                    if self.namespace.is_none() {
                        self.namespace = Some(name);
                    }
                }
                "group" => {
                    let mode = match n.child(0).unwrap().kind() {
                        "mandatory" => GroupMode::Mandatory,
                        "or" => GroupMode::Or,
                        "optional" => GroupMode::Optional,
                        "alternative" => GroupMode::Alternative,
                        _ => panic!("Unknown group mode"),
                    };
                    self.groups.push(Group { mode });
                    self.ts2sym.insert(
                        containing_node(n).id(),
                        Symbol::Group(self.groups.len() as u32 - 1),
                    );
                }
                "cardinality" => {
                    let card = self.parse_cardinality(n, source);
                    self.groups.push(Group {
                        mode: GroupMode::Cardinality(card),
                    });
                    self.ts2sym.insert(
                        containing_node(n).id(),
                        Symbol::Group(self.groups.len() as u32 - 1),
                    );
                }
                "attrib" => {
                    let name = parse_name(n.child_by_field_name("name").unwrap(), source).unwrap();
                    let value = n
                        .child_by_field_name("value")
                        .map(|node| {
                            match node.kind() {
                                "string" => Value::String(source[node.byte_range()].to_string()),
                                "vector" => Value::Vector, //TODO
                                "attributes" => Value::Attributes,
                                "attrib_expr" => match node.named_child(0).unwrap().kind() {
                                    "bool" => Value::Bool(match &source[node.byte_range()] {
                                        "true" => true,
                                        "false" => false,
                                        _ => panic!(),
                                    }),
                                    "number" => {
                                        Value::Number(source[node.byte_range()].parse().unwrap())
                                    }
                                    _ => {
                                        self.parse_errors.push(ErrorInfo {
                                            severity: DiagnosticSeverity::ERROR,
                                            weight: 10,
                                            msg: "composit attributes are not supported yet"
                                                .to_string(),
                                            location: node_range(node, &self.rope),
                                        });
                                        Value::Void
                                    }
                                },
                                _ => panic!(),
                            }
                        })
                        .unwrap_or(Value::Void);
                    let attrib = Attribute {
                        prefix: vec![],
                        name,
                        value,
                    };
                    let sym = attrib.symbol(self.attributes.len());
                    self.attributes.push(attrib);
                    self.ts2sym.insert(containing_node(n).id(), sym);
                }
                "constraint" => {
                    if let Some(constraint) = self.parse_constraint(source, n) {
                        self.constraints.push(constraint);

                        //info!("{:?} err {:?}", n, self.parse_errors);
                        self.ts2sym.insert(
                            containing_node(n).id(),
                            Symbol::Constraint(self.constraints.len() as u32 - 1),
                        );
                    }
                }
                "lang_lvl" => {
                    if let Some(l) = self.parse_lang_lvl(n) {
                        self.lang_lvls.push(l); //TODO: parse
                        self.ts2sym.insert(
                            containing_node(n).id(),
                            Symbol::LangLvl(self.lang_lvls.len() as u32 - 1),
                        );
                    }
                }
                _ => {}
            }
        }

        for i in cursor.matches(
            &TS.queries.extract_dependencies,
            self.tree.clone().root_node(),
            source.as_bytes(),
        ) {
            match i.pattern_index {
                0 => {
                    if let Some(&inner) = self.ts2sym.get(&i.captures[1].node.id()) {
                        if let Some(&outer) = self.ts2sym.get(&i.captures[0].node.id()) {
                            self.graph.add_edge(outer, inner, LocalEdge::Containes);
                        } else {
                            self.graph
                                .add_edge(Symbol::Root, inner, LocalEdge::Containes);
                        }
                    }
                }
                1 => {
                    if let Some(&inner) = self.ts2sym.get(&i.captures[1].node.id()) {
                        if let Some(&outer) = self.ts2sym.get(&i.captures[0].node.id()) {
                            self.graph.add_edge(outer, inner, LocalEdge::Containes);
                            self.root_attributes.push(inner.offset())
                        }
                    } else {
                    }
                }
                2 => {
                    if let Some(&inner) = self.ts2sym.get(&i.captures[1].node.id()) {
                        if let Some(&outer) = self.ts2sym.get(&i.captures[0].node.id()) {
                            self.graph.add_edge(outer, inner, LocalEdge::Containes);
                        }
                    }
                }
                _ => {}
            }
        }
        for (id, f) in self
            .features
            .iter()
            .enumerate()
            .map(|(i, f)| (Symbol::Feature(i as u32), f))
        {
            insert_multi(&mut self.index, vec![f.name.name], id)
        }
        let mut all_features = (0..self.features.len())
            .into_iter()
            .map(|i| Symbol::Feature(i as u32));
        let mut stack = Vec::new();
        while let Some(sym) = all_features.next().or_else(|| stack.pop()) {
            for (_, b, _) in self.graph.edges(sym).filter(|(_, b, _)| b.is_value()) {
                let prefix = [
                    self.prefix(sym),
                    &[self.attributes[b.offset() as usize].name.name],
                ]
                .concat();
                self.attributes[b.offset() as usize].prefix = prefix.clone();
                insert_multi(&mut self.index, prefix, b);
                stack.push(b);
            }
        }
        let mut unique_dir = HashMap::new();
        unique_dir.insert(Vec::new(), Symbol::Root);
        for i in self.imports() {
            let prefix_len = self.prefix(i).len();
            for k in 1..prefix_len {
                let sym = if let Some(sym) = unique_dir.get(&self.prefix(i)[0..k]) {
                    *sym
                } else {
                    let prefix = self.prefix(i)[0..k].to_vec();
                    self.directories.push(prefix.clone());
                    let sym = Symbol::Dir(self.directories.len() as u32 - 1);
                    unique_dir.insert(prefix, sym);
                    sym
                };
                self.graph.add_edge(
                    unique_dir[&self.prefix(sym)[0..k - 1]],
                    sym,
                    LocalEdge::Containes,
                );
            }
            self.graph.add_edge(
                unique_dir[&self.prefix(i)[0..prefix_len - 1]],
                i,
                LocalEdge::Containes,
            );
        }
        for (prefix, sym) in unique_dir {
            insert_multi(&mut self.index, prefix, sym);
        }
        for i in self.index.values_mut() {
            i.sort_unstable();
        }
        //info!("{:#?}",self);
        self.path = uri_to_path(&self.uri).unwrap();
        if let Some(ns) = self.namespace.as_ref() {
            let len = self.path.len().saturating_sub(ns.names.len());
            self.path.truncate(len);
            self.path.extend_from_slice(&ns.names);
        }
    }
    pub fn new(timestamp: Instant, tree: Tree, rope: Rope, uri: Url) -> FileGraph {
        let mut graph = DiGraphMap::new();
        graph.add_node(Symbol::Root);

        let source = rope.to_string();
        let mut out = FileGraph {
            graph,
            index: HashMap::new(),
            root_attributes: Vec::new(),
            features: Vec::new(),
            attributes: Vec::new(),
            references: Vec::new(),
            constraints: Vec::new(),
            groups: Vec::new(),
            directories: Vec::new(),
            imports: Vec::new(),
            timestamp,
            namespace: None,
            path: Vec::new(),
            ts2sym: HashMap::new(),
            lang_lvls: Vec::new(),
            tree,
            source: "".into(),
            rope,
            name: uri.as_str().into(),
            uri,
            parse_errors: Vec::new(),
        };
        out.build(&source);
        out.source = source;
        out
    }
}
