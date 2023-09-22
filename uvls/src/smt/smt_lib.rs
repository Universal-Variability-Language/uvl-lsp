use crate::core::*;
use hashbrown::HashMap;
use indexmap::IndexSet;
use lazy_static::lazy_static;
use log::info;
use regex::Regex;
use std::fmt::Display;
use std::fmt::Write;
use tokio::time::Instant;
use ustr::Ustr;
#[derive(Clone, Debug)]
pub enum AssertName {
    Config,
    Constraint,
    Attribute,
    Group,
    GroupMember,
    GroupMin,
    GroupMax,
    RootFeature,
}
impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}
impl Display for AssertName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Attribute => write!(f, "attribute value"),
            Self::Constraint => write!(f, "constraint"),
            Self::Config => write!(f, "configuration value"),
            Self::Group => write!(f, "group"),
            Self::GroupMin => write!(f, "lower bound"),
            Self::GroupMax => write!(f, "upper bound"),
            Self::GroupMember => write!(f, "group member"),
            Self::RootFeature => write!(f, "root feature are always required"),
        }
    }
}
#[derive(Clone, Debug)]
pub struct AssertInfo(pub ModuleSymbol, pub AssertName);
#[derive(Clone, Debug)]
pub struct Assert(pub Option<AssertInfo>, pub Expr);
#[derive(Clone, Debug)]
pub enum Expr {
    Bool(bool),
    Real(f64),
    String(String),
    Var(usize),
    //Logic
    And(Vec<Expr>),
    Or(Vec<Expr>),
    Not(Box<Expr>),
    Implies(Vec<Expr>),
    Greater(Vec<Expr>),
    Less(Vec<Expr>),
    Equal(Vec<Expr>),
    AtLeast(usize, Vec<Expr>),
    AtMost(usize, Vec<Expr>),
    //Arithmetic
    Add(Vec<Expr>),
    Sub(Vec<Expr>),
    Mul(Vec<Expr>),
    Div(Vec<Expr>),
    //Integer Arithmetic
    Ceil(Box<Expr>),
    Floor(Box<Expr>),
    //String ops
    Strlen(Box<Expr>),
    StrLess(Vec<Expr>),
    StrLessEq(Vec<Expr>),
    StrConcat(Box<Expr>, Box<Expr>),
    //IfThenElse
    Ite(Box<Expr>, Box<Expr>, Box<Expr>),
}
pub struct SMTModule {
    pub variables: IndexSet<ModuleSymbol>,
    pub asserts: Vec<Assert>,
}
impl SMTModule {
    #[allow(dead_code)]
    pub fn parse_model<'a>(
        &'a self,
        model: &'a str,
    ) -> impl Iterator<Item = (ModuleSymbol, ConfigValue)> + 'a {
        lazy_static! {
            static ref RE: Regex =
                Regex::new(r#"\(\s*define-fun\s+v(\d+)\s+\(\)\s+(Bool|String|Real)\s+(true|false|"[^"]*"|-?[0-9]*\.[0-9]*)\s*\)"#)
                    .unwrap();
        };

        RE.captures_iter(model).map(|i| {
            let idx: usize = i[1].parse().unwrap();
            let var = *self.variables.get_index(idx).unwrap();
            (
                var,
                match &i[2] {
                    "Bool" => ConfigValue::Bool(match &i[3] {
                        "true" => true,
                        _ => false,
                    }),
                    "Real" => ConfigValue::Number(i[3].parse().unwrap()),
                    _ => {
                        let s = &i[3];
                        ConfigValue::String(s[1..s.len() - 1].into())
                    }
                },
            )
        })
    }
    //extract values from a response string
    pub fn parse_values<'a>(
        &'a self,
        values: &'a str,
        module: &'a Module,
    ) -> impl Iterator<Item = (ModuleSymbol, ConfigValue)> + 'a {
        super::parse::iter_values(self, module, values)
        /*
        //This abomination parses a identifier with a bool, negative number, positive number or a string
        //The problem is that z3 encodes numbers using nested expressions instead of simple floating point
        //values. Hopefully all cases are covered here...
        //TODO replace this with a true eval parser(best use NOM)

        lazy_static! {
            static ref RE: Regex = Regex::new(
                r#"\(\s*v(\d+)\s+(?:(true|false)|\(- ((?:[0-9]*\.)?[0-9]+)\??|((?:[0-9]*\.)?[0-9]+)\??|"([^"]*)")\s*\)"#
            )
            .unwrap();
        };
        //info!("{values}");
        RE.captures_iter(values).map(|i| {
            let idx: usize = i[1].parse().unwrap();
            let var = *self.variables.get_index(idx).unwrap();
            (
                var,
                match (i.get(2), i.get(3), i.get(4), i.get(5)) {
                    (Some(b), _, _, _) => ConfigValue::Bool(match b.as_str() {
                        "true" => true,
                        _ => false,
                    }),
                    (_, Some(num), _, _) => {
                        ConfigValue::Number(-(num.as_str().parse::<f64>().unwrap()))
                    }
                    (_, _, Some(num), _) => ConfigValue::Number(num.as_str().parse().unwrap()),
                    (_, _, _, Some(s)) => ConfigValue::String(s.as_str().into()),
                    _ => unreachable!(),
                },
            )
        })
        */
    }
    pub fn parse_unsat_core<'a>(&'a self, core: &'a str) -> impl Iterator<Item = AssertInfo> + 'a {
        lazy_static! {
            static ref RE: Regex = Regex::new(r"a(\d+)").unwrap();
        };
        RE.captures_iter(core).filter_map(|i| {
            let idx: usize = i[1].parse().unwrap();
            self.asserts[idx].0.clone()
        })
    }
    // create source to config z3 Solver
    pub fn config_to_source(&self) -> String {
        let out = "(set-option :produce-unsat-cores true)
        (define-fun smooth_div ((x Real) (y Real)) Real(if (not (= y 0.0))(/ x y)0.0))
        (define-fun floor ((x Real)) Int (to_int x))
        (define-fun ceil ((x Real)) Int (ite (= (to_int x) x) (to_int x) (to_int (+ x 1)) ))
        (set-option :smt.core.minimize true)\n"
            .to_string();
        out
    }
    // create with all Variable the source for the SMTSolver
    pub fn variable_to_source(&self, module: &Module) -> String {
        let mut out = "".to_string();
        for (i, v) in self.variables.iter().enumerate() {
            let ty = module.type_of(*v);
            let _ = writeln!(out, "(declare-const v{i} {ty})");
        }
        out
    }

    // create the source for an assert, if the assert should be negated the variable neg must be true
    pub fn assert_to_source(
        &self,
        i: usize,
        info: &Option<AssertInfo>,
        expr: &Expr,
        not: bool,
    ) -> String {
        let mut out = "".to_string();
        let _ = write!(out, "(assert");

        if info.is_some() {
            let _ = write!(out, "(! ");
        }
        if not {
            let _ = write!(out, "( not ");
        }
        #[derive(Debug)]
        enum CExpr<'a> {
            Expr(&'a Expr),
            End,
        }
        let mut stack = vec![CExpr::Expr(expr)];
        while let Some(e) = stack.pop() {
            match e {
                CExpr::End => {
                    let _ = write!(out, ")");
                }
                //Head
                CExpr::Expr(e) => {
                    match e {
                        Expr::Bool(b) => {
                            let _ = write!(out, " {b}");
                        }
                        Expr::Real(r) => {
                            let _ = write!(out, " {r:?}");
                        }
                        Expr::String(val) => {
                            let _ = write!(out, " \"{val}\"");
                        }
                        Expr::Var(off) => {
                            let _ = write!(out, " v{off}");
                        }
                        Expr::Add(..) => {
                            let _ = write!(out, "(+");
                        }
                        Expr::Sub(..) => {
                            let _ = write!(out, "(-");
                        }
                        Expr::Mul(..) => {
                            let _ = write!(out, "(*");
                        }
                        Expr::Div(..) => {
                            let _ = write!(out, "(smooth_div");
                        }
                        Expr::Ceil(..) => {
                            let _ = write!(out, "(ceil");
                        }
                        Expr::Floor(..) => {
                            let _ = write!(out, "(floor");
                        }
                        Expr::And(..) => {
                            let _ = write!(out, "(and");
                        }
                        Expr::Or(..) => {
                            let _ = write!(out, "(or");
                        }
                        Expr::Implies(..) => {
                            let _ = write!(out, "(=>");
                        }
                        Expr::Not(..) => {
                            let _ = write!(out, "(not");
                        }
                        Expr::Ite(..) => {
                            let _ = write!(out, "(ite");
                        }
                        Expr::Equal(..) => {
                            let _ = write!(out, "(=");
                        }
                        Expr::Greater(..) => {
                            let _ = write!(out, "(>");
                        }
                        Expr::Less(..) => {
                            let _ = write!(out, "(<");
                        }
                        Expr::Strlen(..) => {
                            let _ = write!(out, "(str.len");
                        }
                        Expr::AtLeast(min, ..) => {
                            let _ = write!(out, "((_ at-least {min})");
                        }
                        Expr::AtMost(max, ..) => {
                            let _ = write!(out, "((_ at-most {max})");
                        }
                        Expr::StrConcat(..) => {
                            let _ = write!(out, "(str.++");
                        }
                        Expr::StrLess(..) => {
                            let _ = write!(out, "(str.<");
                        }
                        Expr::StrLessEq(..) => {
                            let _ = write!(out, "(str.<=");
                        }
                    }
                    //Args
                    match e {
                        Expr::Add(v)
                        | Expr::Sub(v)
                        | Expr::Mul(v)
                        | Expr::Div(v)
                        | Expr::Or(v)
                        | Expr::And(v)
                        | Expr::Implies(v)
                        | Expr::AtLeast(_, v)
                        | Expr::AtMost(_, v)
                        | Expr::Greater(v)
                        | Expr::Less(v)
                        | Expr::StrLess(v)
                        | Expr::StrLessEq(v)
                        | Expr::Equal(v) => {
                            stack.push(CExpr::End);
                            for i in v.iter().rev() {
                                stack.push(CExpr::Expr(i));
                            }
                        }
                        Expr::Strlen(e) | Expr::Ceil(e) | Expr::Floor(e) | Expr::Not(e) => {
                            stack.push(CExpr::End);
                            stack.push(CExpr::Expr(e));
                        }
                        Expr::StrConcat(rhs, lhs) => {
                            stack.push(CExpr::End);
                            stack.push(CExpr::Expr(rhs));
                            stack.push(CExpr::Expr(lhs));
                        }
                        Expr::Ite(cond, lhs, rhs) => {
                            stack.push(CExpr::End);
                            stack.push(CExpr::Expr(rhs));
                            stack.push(CExpr::Expr(lhs));
                            stack.push(CExpr::Expr(cond));
                        }
                        Expr::Bool(..) | Expr::String(..) | Expr::Real(..) | Expr::Var(..) => {}
                    }
                }
            }
        }
        if not {
            let _ = write!(out, " )");
        }
        //name tag
        if info.is_some() {
            let _ = write!(out, " :named a{i})");
        }

        let _ = write!(out, ")\n");
        out
    }

    //tree to source
    pub fn to_source(&self, module: &Module) -> String {
        let time = Instant::now();
        //
        let mut out = self.config_to_source();
        let _ = writeln!(out, "{}", self.variable_to_source(module));
        for (i, Assert(info, expr)) in self.asserts.iter().enumerate() {
            let _ = writeln!(out, "{}", self.assert_to_source(i, info, expr, false));
        }
        info!("model to string  in {:?}", time.elapsed());
        out
    }
    pub fn var(&self, ms: ModuleSymbol) -> usize {
        self.variables.get_index_of(&ms).unwrap()
    }
    pub fn pseudo_bool(&self, ms: ModuleSymbol, module: &Module) -> String {
        let ms = module.resolve_value(ms);
        match module.type_of(ms) {
            Type::Bool => format!("v{}", self.var(ms)),
            Type::Real => format!("(not(= v{} 0.0))", self.var(ms)),
            Type::String => format!(r#"(not(= v{} ""))"#, self.var(ms)),
            _ => unimplemented!(),
        }
    }
}
struct SMTBuilder<'a> {
    //Each variable is encoded as v{n} where n is an index into sym2var using an IndexSet
    //enables us to lookup a variable both by index and ModuleSymbol
    sym2var: IndexSet<ModuleSymbol>,
    assert: Vec<Assert>,
    module: &'a Module,
}
impl<'a> SMTBuilder<'a> {
    //Variable to index
    fn var(&self, ms: ModuleSymbol) -> Expr {
        Expr::Var(
            self.sym2var
                .get_index_of(&self.module.resolve_value(ms))
                .unwrap_or(0),
        )
    }
    //The language allows non boolean variables as attribute and feature parents
    //So we treat them as boolean expressions in those contexts
    fn pseudo_bool(&self, ms: ModuleSymbol) -> Expr {
        let ms = self.module.resolve_value(ms);
        match self.module.type_of(ms) {
            Type::Bool => self.var(ms),
            Type::Real => Expr::Not(Expr::Equal(vec![self.var(ms), Expr::Real(0.0)]).into()),
            Type::String => {
                Expr::Not(Expr::Equal(vec![self.var(ms), Expr::String("".into())]).into())
            }
            _ => unimplemented!(),
        }
    }
    fn clause(&self, g: ModuleSymbol) -> Vec<Expr> {
        let file = self
            .module
            .instances()
            .filter(|(id, _)| id == &g.instance)
            .map(|(_, f)| f)
            .collect::<Vec<&AstDocument>>()[0];

        let mut cardinalitys: HashMap<Ustr, (Cardinality, Vec<Symbol>)> = HashMap::from([]);
        // Cardinality
        let card_expressions = self
            .module
            .file(g.instance)
            .direct_children(g.sym)
            .filter(|i| {
                if let Symbol::Feature(index) = i {
                    let feature = file.get_feature(index.clone()).unwrap();
                    match feature.cardinality {
                        Some(Cardinality::Range(_, _)) => {
                            if !cardinalitys.contains_key(&feature.name.name) {
                                cardinalitys.insert(
                                    feature.name.name,
                                    (
                                        feature.clone().cardinality.unwrap(),
                                        vec![Symbol::Feature(index.clone())],
                                    ),
                                );
                            } else {
                                cardinalitys
                                    .get_mut(&feature.name.name)
                                    .unwrap()
                                    .1
                                    .push(Symbol::Feature(index.clone()));
                            }
                            return true;
                        }
                        _ => return false,
                    }
                }
                return false;
            })
            .collect::<Vec<Symbol>>();

        let mut result = self
            .module
            .file(g.instance)
            .direct_children(g.sym)
            .filter(|s| !card_expressions.contains(s))
            .map(|i| self.pseudo_bool(g.instance.sym(i)))
            .collect::<Vec<Expr>>();

        result.append(
            cardinalitys
                .values()
                .into_iter()
                .map(|(card, syms)| {
                    let list = syms
                        .into_iter()
                        .map(|i| self.pseudo_bool(g.instance.sym(i.clone())))
                        .collect::<Vec<Expr>>();
                    match card {
                        Cardinality::Range(min, max) => Expr::And(vec![
                            Expr::AtLeast(min.clone(), list.clone()),
                            Expr::AtMost(max.clone(), list),
                        ]),
                        _ => panic!(),
                    }
                })
                .collect::<Vec<Expr>>()
                .as_mut(),
        );

        return result;
    }
    fn min_assert(&mut self, min: usize, p_bind: &Expr, g: ModuleSymbol) {
        let clause = self.clause(g);
        self.assert.push(Assert(
            Some(AssertInfo(g, AssertName::GroupMin)),
            Expr::Implies(vec![p_bind.clone(), Expr::AtLeast(min, clause)]),
        ));
    }
    fn max_assert(&mut self, max: usize, p_bind: &Expr, g: ModuleSymbol) {
        let clause = self.clause(g);
        self.assert.push(Assert(
            Some(AssertInfo(g, AssertName::GroupMax)),
            Expr::Implies(vec![p_bind.clone(), Expr::AtMost(max, clause)]),
        ));
    }
    fn push_var(&mut self, ms: ModuleSymbol) -> Expr {
        self.sym2var.insert(ms);
        Expr::Var(self.sym2var.len() - 1)
    }
}
impl Into<Expr> for ConfigValue {
    fn into(self) -> Expr {
        match self {
            Self::Bool(b) => Expr::Bool(b),
            Self::Number(n) => Expr::Real(n),
            Self::String(s) => Expr::String(s),
            Self::Cardinality(_) => Expr::Bool(true),
        }
    }
}

pub fn uvl2smt(module: &Module, config: &HashMap<ModuleSymbol, ConfigValue>) -> SMTModule {
    assert!(module.ok);
    let mut builder = SMTBuilder {
        module,
        sym2var: IndexSet::new(),
        assert: Vec::new(),
    };
    //encode features
    for (m, file) in module.instances() {
        for f in file.all_features() {
            builder.push_var(m.sym(f));
        }

        for sym_feature in file.all_features() {
            if let Symbol::Feature(id) = sym_feature {
                let feature = file.get_feature(id).unwrap().clone();
                if let Cardinality::Range(min, _) =
                    feature.cardinality.unwrap_or_else(|| Cardinality::Fixed)
                {
                    // Make AtLeast assertion for cardinality feature
                    if feature.first_cardinality_child {
                        let mut list = vec![];
                        let parent = file.parent(sym_feature, false).unwrap();

                        for child in file.direct_children(parent) {
                            if let Symbol::Feature(sibling_id) = child {
                                let sibling = file.get_feature(sibling_id);
                                if sibling.unwrap().name.name.as_str() == feature.name.name.as_str()
                                {
                                    list.push(builder.var(m.sym(Symbol::Feature(sibling_id))));
                                }
                            }
                        }

                        match file.parent(Symbol::Feature(id), false) {
                            Some(Symbol::Group(_)) => {
                                // if parent is group, a cardinality can be atleast 0 or min, since it can not be selected at all.
                                builder.assert.push(Assert(
                                    Some(AssertInfo(m.sym(sym_feature), AssertName::GroupMin)),
                                    Expr::Or(vec![
                                        Expr::AtLeast(min, list.clone()),
                                        Expr::AtMost(0, list),
                                    ]),
                                ));
                            }
                            _ => {
                                builder.assert.push(Assert(
                                    Some(AssertInfo(m.sym(sym_feature), AssertName::GroupMin)),
                                    Expr::AtLeast(min, list),
                                ));
                            }
                        }
                    }
                }
            }
        }
    }
    //set config features
    for (&ms, val) in config
        .iter()
        .filter(|i| matches!(i.0.sym, Symbol::Feature(..)))
    {
        let var = builder.var(ms);
        builder.assert.push(Assert(
            Some(AssertInfo(ms, AssertName::Config)),
            Expr::Equal(vec![var, val.clone().into()]),
        ));
    }
    //encode attributes
    for (m, file) in module.instances() {
        for f in file.all_features() {
            file.visit_named_children(f, true, |a, _| {
                if !matches!(a, Symbol::Attribute(..)) {
                    return true;
                }
                let ms = m.sym(a);
                let Some((val, n)) = config.get(&ms).map(|v|( v.clone().into()  ,AssertName::Config )).or_else(|| {
                    file.value(a)
                        .and_then(|v| match v {
                            ast::Value::Bool(x) => Some(Expr::Bool(*x)),
                            ast::Value::Number(x) => Some(Expr::Real(*x)),
                            ast::Value::String(x) => Some(Expr::String(x.clone())),
                            _ => None,
                        })
                        .map(|v| (v, AssertName::Attribute))
                }) else {return true} ;
                let zero = match val {
                    Expr::Bool(..) => Expr::Bool(false),
                    Expr::Real(..) => Expr::Real(0.0),
                    Expr::String(..) => Expr::String("".into()),
                    _=>unreachable!()
                };
                let attrib_var = builder.push_var(ms);
                let feat_var = builder.pseudo_bool(m.sym(f));
                builder.assert.push(Assert(Some(AssertInfo(ms, n)),Expr::Equal(vec![
                                                                               Expr::Ite(feat_var.into(),
                                                                               val.into(),
                                                                               zero.into()),
                                                                               attrib_var] ) ));
                true
            });
        }
    }
    //encode groups
    for (m, file) in module.instances() {
        for p in file.all_features() {
            for g in file
                .direct_children(p)
                .filter(|sym| matches!(sym, Symbol::Group(..)))
            {
                if file.direct_children(g).next().is_none() {
                    continue;
                }
                let p_bind = builder.pseudo_bool(m.sym(p));
                for c in file.direct_children(g) {
                    let c_bind = builder.pseudo_bool(m.sym(c));
                    builder.assert.push(Assert(
                        None,
                        Expr::Implies(vec![c_bind.into(), p_bind.clone().into()]),
                    ));
                }
                match file.group_mode(g).unwrap() {
                    GroupMode::Or => {
                        let clause = builder.clause(m.sym(g));
                        builder.assert.push(Assert(
                            Some(AssertInfo(m.sym(g), AssertName::Group)),
                            Expr::Implies(vec![p_bind.into(), Expr::Or(clause).into()]),
                        ));
                    }
                    GroupMode::Alternative => {
                        builder.min_assert(1, &p_bind, m.sym(g));
                        builder.max_assert(1, &p_bind, m.sym(g));
                    }
                    GroupMode::Mandatory => {
                        builder.clause(m.sym(g)).into_iter().for_each(|expr| {
                            info!("expr {:?}", expr);
                            builder.assert.push(Assert(
                                Some(AssertInfo(m.sym(p), AssertName::GroupMember)),
                                Expr::Equal(vec![expr.into(), p_bind.clone().into()]),
                            ))
                        });
                    }
                    GroupMode::Optional | GroupMode::Cardinality(Cardinality::Fixed) => {}
                    GroupMode::Cardinality(Cardinality::Range(min, max)) => {
                        builder.min_assert(min, &p_bind, m.sym(g));
                        builder.max_assert(max, &p_bind, m.sym(g));
                    }
                }
            }
        }
    }
    //assert root features are always on
    for f in module
        .file(InstanceID(0))
        .direct_children(Symbol::Root)
        .filter(|f| matches!(f, Symbol::Feature(..)))
    {
        builder.assert.push(Assert(
            Some(AssertInfo(InstanceID(0).sym(f), AssertName::RootFeature)),
            builder.pseudo_bool(InstanceID(0).sym(f)),
        ));
    }
    //encode constraints
    for (m, file) in module.instances() {
        for c in file.all_constraints() {
            let expr = translate_constraint(file.constraint(c).unwrap(), m, &mut builder, file);
            builder.assert.push(Assert(
                Some(AssertInfo(m.sym(c), AssertName::Constraint)),
                expr,
            ));
        }
    }

    SMTModule {
        variables: builder.sym2var,
        asserts: builder.assert,
    }
}

//create an SMTModule, but the asserts are only constraints
pub fn uvl2smt_constraints(module: &Module) -> SMTModule {
    assert!(module.ok);
    let mut builder = SMTBuilder {
        module,
        sym2var: IndexSet::new(),
        assert: Vec::new(),
    };
    //encode features
    for (m, file) in module.instances() {
        for f in file.all_features() {
            builder.push_var(m.sym(f));
        }
    }
    //encode attributes
    for (m, file) in module.instances() {
        for f in file.all_features() {
            file.visit_named_children(f, true, |a, _| {
                if !matches!(a, Symbol::Attribute(..)) {
                    return true;
                }
                let ms = m.sym(a);
                builder.push_var(ms);
                true
            });
        }
    }
    //encode constraints
    for (m, file) in module.instances() {
        for c in file.all_constraints() {
            let expr = translate_constraint(file.constraint(c).unwrap(), m, &mut builder, file);
            builder.assert.push(Assert(
                Some(AssertInfo(m.sym(c), AssertName::Constraint)),
                expr,
            ));
        }
    }
    SMTModule {
        variables: builder.sym2var,
        asserts: builder.assert,
    }
}

fn translate_constraint(
    decl: &ast::ConstraintDecl,
    m: InstanceID,
    builder: &mut SMTBuilder,
    ast: &AstDocument,
) -> Expr {
    match &decl.content {
        ast::Constraint::Ref(sym) => {
            let module_symbol: ModuleSymbol = builder.module.resolve_value(m.sym(*sym));
            match module_symbol.sym {
                Symbol::Feature(x) => {
                    let all_of = ast
                        .find_all_of(ast.name(Symbol::Feature(x)).unwrap())
                        .into_iter()
                        .map(|feature| builder.var(m.sym(feature)))
                        .collect::<Vec<Expr>>();
                    return Expr::Or(all_of);
                }
                _ => (),
            }
            builder.var(m.sym(*sym))
        }
        ast::Constraint::Not(lhs) => stacker::maybe_grow(32 * 1024, 1024 * 1024, || {
            Expr::Not(translate_constraint(lhs, m, builder, ast).into())
        }),
        ast::Constraint::Constant(b) => Expr::Bool(*b),
        ast::Constraint::Logic { op, lhs, rhs } => {
            let lhs = stacker::maybe_grow(32 * 1024, 1024 * 1024, || {
                translate_constraint(lhs, m, builder, ast)
            });
            let rhs = translate_constraint(rhs, m, builder, ast);
            match op {
                ast::LogicOP::Or => Expr::Or(vec![lhs, rhs]),
                ast::LogicOP::And => Expr::And(vec![lhs, rhs]),
                ast::LogicOP::Equiv => Expr::Equal(vec![lhs, rhs]),
                ast::LogicOP::Implies => Expr::Implies(vec![lhs, rhs]),
            }
        }
        ast::Constraint::Equation { op, lhs, rhs } => {
            let (lhs, lty) =
                stacker::maybe_grow(32 * 1024, 1024 * 1024, || translate_expr(lhs, m, builder));
            let (rhs, rty) = translate_expr(rhs, m, builder);
            debug_assert!(rty == lty);
            if lty == Type::String {
                match op {
                    ast::EquationOP::Equal => Expr::Equal(vec![lhs, rhs]),
                    ast::EquationOP::Greater => Expr::StrLess(vec![lhs, rhs]),
                    ast::EquationOP::Smaller => Expr::Not(Expr::StrLessEq(vec![lhs, rhs]).into()),
                }
            } else {
                match op {
                    ast::EquationOP::Equal => Expr::Equal(vec![lhs, rhs]),
                    ast::EquationOP::Greater => Expr::Greater(vec![lhs, rhs]),
                    ast::EquationOP::Smaller => Expr::Less(vec![lhs, rhs]),
                }
            }
        }
    }
}

fn translate_expr(decl: &ast::ExprDecl, m: InstanceID, builder: &mut SMTBuilder) -> (Expr, Type) {
    match &decl.content {
        ast::Expr::Number(n) => (Expr::Real(*n), Type::Real),
        ast::Expr::String(s) => (Expr::String(s.clone()), Type::String),
        ast::Expr::Ref(sym) => (
            builder.var(m.sym(*sym)),
            builder.module.type_of(m.sym(*sym)),
        ),
        ast::Expr::Len(lhs) => (
            Expr::Strlen(translate_expr(lhs, m, builder).0.into()),
            Type::Real,
        ),
        ast::Expr::Binary { lhs, rhs, op } => {
            let (lhs, lty) =
                stacker::maybe_grow(32 * 1024, 1024 * 1024, || translate_expr(lhs, m, builder));
            let (rhs, rty) = translate_expr(rhs, m, builder);
            debug_assert!(rty == lty);
            if rty == Type::String {
                debug_assert!(*op == NumericOP::Add);
                (Expr::StrConcat(rhs.into(), lhs.into()), Type::String)
            } else {
                let expr = match op {
                    ast::NumericOP::Add => Expr::Add(vec![lhs, rhs]),
                    ast::NumericOP::Sub => Expr::Sub(vec![lhs, rhs]),
                    ast::NumericOP::Mul => Expr::Mul(vec![lhs, rhs]),
                    ast::NumericOP::Div => Expr::Div(vec![lhs, rhs]),
                };
                (expr, Type::Real)
            }
        }
        ast::Expr::Aggregate { op, context, query } => {
            let mut all_attributes = Vec::new();
            let mut count_features = Vec::new();
            let tgt = context
                .map(|sym| builder.module.resolve_value(m.sym(sym)))
                .unwrap_or(m.sym(Symbol::Root));
            let tgt_file = builder.module.file(tgt.instance);
            tgt_file.visit_attributes(tgt.sym, |feature, attrib, prefix| {
                if prefix == query.names.as_slice()
                    && tgt_file.type_of(attrib).unwrap() == Type::Real
                {
                    count_features.push(Expr::Ite(
                        builder.pseudo_bool(tgt.instance.sym(feature)).into(),
                        Expr::Real(1.0).into(),
                        Expr::Real(0.0).into(),
                    ));
                    all_attributes.push(builder.var(tgt.instance.sym(attrib)));
                }
            });
            if all_attributes.is_empty() {
                (Expr::Real(0.0), Type::Real)
            } else {
                (
                    match op {
                        ast::AggregateOP::Sum => Expr::Add(all_attributes),
                        ast::AggregateOP::Avg => {
                            Expr::Div(vec![Expr::Add(all_attributes), Expr::Add(count_features)])
                        }
                    },
                    Type::Real,
                )
            }
        }
        ast::Expr::Integer { op, n } => (
            match op {
                ast::IntegerOP::Ceil => Expr::Ceil(translate_expr(n, m, builder).0.into()),
                ast::IntegerOP::Floor => Expr::Floor(translate_expr(n, m, builder).0.into()),
            },
            Type::Real,
        ),
    }
}
