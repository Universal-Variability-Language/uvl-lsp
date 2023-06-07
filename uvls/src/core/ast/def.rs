//Basic Ast components
use ustr::Ustr;
use itertools::Itertools;
use enumflags2::bitflags;
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
    pub fn append(&self, arg: &SymbolSpan) -> Path {
        let mut new = self.clone();
        new.names.push(arg.name);
        new.spans.push(arg.span.clone());
        new
    }
    pub fn len(&self) -> usize {
        self.names.len()
    }
    pub fn range(&self) -> Span {
        if !self.spans.is_empty() {
            self.spans[0].start..self.spans.last().unwrap().end
        } else {
            0..0
        }
    }
    pub fn segment(&self, offset: usize) -> usize {
        self.spans
            .iter()
            .take_while(|i| i.start < offset)
            .count()
            .saturating_sub(1)
    }
    pub fn to_string(&self) -> String {
        self.names.iter().map(|i| i.as_str()).join(".")
    }
}

//Type definitions for symbols
#[bitflags]
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Type {
    String,
    Real,
    Vector,
    Attributes,
    Bool,
    Void,
    Namespace,
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
    TYPE,
}
#[derive(Clone, Debug, PartialEq)]
pub enum LanguageLevelSMT {
    Any,
    FeatureCardinality,
    Aggregate,
}
#[derive(Clone, Debug, PartialEq)]
pub enum LanguageLevelSAT {
    Any,
    GroupCardinality,
}
#[derive(Clone, Debug, PartialEq)]
pub enum LanguageLevelTYPE {
    Any,
    NumericConstraints,
    StringConstraints,
}
#[derive(Clone, Debug)]
pub enum LanguageLevel {
    SAT(Vec<LanguageLevelSAT>),
    SMT(Vec<LanguageLevelSMT>),
    TYPE(Vec<LanguageLevelTYPE>),
}

#[derive(Clone, Debug)]
pub struct LanguageLevelDecl {
    pub lang_lvl: LanguageLevel,
    pub span: Span,
}
#[derive(Clone, Debug)]
pub struct Feature {
    pub name: SymbolSpan,
    pub cardinality: Option<Cardinality>,
    pub ty: Type,
}
#[derive(Clone, Debug)]
pub struct Import {
    pub path: Path,
    pub alias: Option<SymbolSpan>,
}
#[derive(Clone, Debug)]
pub struct Namespace {
    pub prefix: Path,
}
#[derive(Clone, Debug)]
pub struct Group {
    pub mode: GroupMode,
    pub span: Span,
}
#[derive(Clone, Debug)]
pub struct Reference {
    pub path: Path,
}
#[derive(Clone, Debug)]
pub struct Attribute {
    pub name: SymbolSpan,
    pub value: ValueDecl,
    pub depth: u32,
}
#[derive(Clone, Debug)]
pub struct Keyword {
    pub name: Ustr,
    pub span: Span,
}
#[derive(Clone, Debug)]
pub struct Dir {
    pub name: Ustr,
    pub depth: u32,
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
pub struct ValueDecl {
    pub value: Value,
    pub span: Span,
}

impl Default for Value {
    fn default() -> Self {
        Value::Void
    }
}

#[derive(Clone, Debug,PartialEq,Eq)]
pub enum NumericOP {
    Add,
    Sub,
    Div,
    Mul,
}

impl NumericOP {
    pub fn parse(op: &str) -> Option<Self> {
        match op {
            "+" => Some(NumericOP::Add),
            "-" => Some(NumericOP::Sub),
            "*" => Some(NumericOP::Mul),
            "/" => Some(NumericOP::Div),
            _ => None,
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LogicOP {
    And,
    Or,
    Implies,
    Equiv,
}

#[derive(Clone, Debug)]
pub enum AggregateOP {
    Avg,
    Sum,
}

#[derive(Clone, Debug)]
pub enum IntegerOP {
    Floor,
    Ceil,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EquationOP {
    Greater,
    Smaller,
    Equal,
}


#[derive(Clone, Debug)]
pub enum Constraint {
    Constant(bool),
    Equation {
        op: EquationOP,
        lhs: Box<ExprDecl>,
        rhs: Box<ExprDecl>,
    },
    Logic {
        op: LogicOP,
        lhs: Box<ConstraintDecl>,
        rhs: Box<ConstraintDecl>,
    },
    Ref(Symbol),
    Not(Box<ConstraintDecl>),
}

#[derive(Clone, Debug)]
pub struct ConstraintDecl {
    pub content: Constraint,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum Expr {
    Number(f64),
    String(String),
    Ref(Symbol),
    Binary {
        op: NumericOP,
        rhs: Box<ExprDecl>,
        lhs: Box<ExprDecl>,
    },
    Aggregate {
        op: AggregateOP,
        context: Option<Symbol>,
        query: Path,
    },
    Integer {
        op: IntegerOP,
        n: Box<ExprDecl>,
    },
    Len(Box<ExprDecl>),
}
#[derive(Clone, Debug)]
pub struct ExprDecl {
    pub content: Expr,
    pub span: Span,
}
//A symbol represents an entity in some uvl document
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, enum_kinds::EnumKind)]
#[enum_kind(SymbolKind, derive(Hash))]
pub enum Symbol {
    Keyword(usize),
    Feature(usize),
    Constraint(usize),
    Attribute(usize),
    Reference(usize),
    Group(usize),
    Import(usize),
    LangLvl(usize),
    Dir(usize),
    Root,
}
impl Symbol {
    pub fn offset(&self) -> usize {
        match self {
            Self::Feature(id)
            | Self::Constraint(id)
            | Self::Attribute(id)
            | Self::Reference(id)
            | Self::Group(id)
            | Self::LangLvl(id)
            | Self::Dir(id)
            | Self::Import(id) => *id,
            _ => panic!(),
        }
    }
}