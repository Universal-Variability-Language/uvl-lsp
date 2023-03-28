use crate::{
    ast::*,
    check::{DiagnosticUpdate, ErrorsAcc},
    config::*,
    inlays::{InlayHandler, InlaySource},
    module::*,
    semantic::*,
    util::{maybe_cancel, Result},
    webview,
};
use futures::future::join_all;
use hashbrown::{HashMap, HashSet};
use indexmap::{IndexMap, IndexSet};
use itertools::Itertools;
use lazy_static::lazy_static;
use log::info;
use regex::Regex;
use std::fmt::{Display, Write};
use std::sync::Arc;
use tokio::{
    io::Lines,
    join,
    process::{ChildStdin, ChildStdout, Command},
    sync::{mpsc, watch},
    time::Instant,
};
use tokio::{
    io::{AsyncBufReadExt, AsyncWriteExt, BufReader, BufWriter},
    process::Child,
    spawn,
};
use tokio_util::sync::CancellationToken;
use tower_lsp::lsp_types::*;
pub struct SmtSolver {
    proc: Child,
    stdin: BufWriter<ChildStdin>,
    stdout: Lines<BufReader<ChildStdout>>,
    cancel: CancellationToken,
}
impl SmtSolver {
    pub async fn new(model: String, cancel: &CancellationToken) -> Result<Self> {
        let mut proc = Command::new("z3")
            .arg("-in")
            .arg("-smt2")
            .stdin(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .kill_on_drop(true)
            .spawn()?;

        let mut stdin = BufWriter::new(proc.stdin.take().unwrap());
        let stdout = BufReader::new(proc.stdout.take().unwrap()).lines();
        let mut stderr = BufReader::new(proc.stderr.take().unwrap()).lines();
        spawn(async move {
            while let Some(err) = stderr.next_line().await? {
                info!("smt error {:?}", err);
            }
            return tokio::io::Result::Ok(());
        });
        maybe_cancel(&cancel, stdin.write_all(model.as_bytes())).await??;
        stdin.flush().await?;
        Ok(SmtSolver {
            cancel: cancel.clone(),
            proc,
            stdin,
            stdout,
        })
    }

    pub async fn read_block(&mut self) -> Result<String> {
        let mut out = String::new();
        let mut nesting = 0;
        while let Some(line) = maybe_cancel(&self.cancel, self.stdout.next_line()).await?? {
            let _ = write!(out, " {}", line);
            for i in line.chars() {
                match i {
                    '(' => nesting += 1,
                    ')' => nesting -= 1,
                    _ => {}
                }
            }
            if nesting == 0 {
                break;
            }
        }
        Ok(out)
    }
    pub async fn check_sat(&mut self) -> Result<bool> {
        self.stdin.write_all("(check-sat)\n".as_bytes()).await?;
        self.stdin.flush().await?;
        let ret = maybe_cancel(&self.cancel, self.stdout.next_line())
            .await??
            .ok_or("failed to get line")?;
        match ret.as_str() {
            "sat" => Ok(true),
            "unsat" => Ok(false),
            s => Err(format!("Bad response {s}"))?,
        }
    }
    pub async fn unsat_core(&mut self) -> Result<String> {
        self.stdin
            .write_all("(get-unsat-core)\n".as_bytes())
            .await?;
        self.stdin.flush().await?;
        self.read_block().await
    }
    pub async fn push(&mut self, cmd: String) -> Result<()> {
        self.stdin.write_all(cmd.as_bytes()).await?;
        self.stdin.flush().await?;
        Ok(())
    }
    pub async fn model(&mut self) -> Result<String> {
        self.stdin.write_all(b"(get-model)\n").await?;
        self.stdin.flush().await?;
        self.read_block().await
    }
    pub async fn values(&mut self, active: String) -> Result<String> {
        if active.is_empty() {
            return Ok(String::new());
        }
        let query = format!("(get-value ({active}))\n");
        self.stdin.write_all(query.as_bytes()).await?;
        self.stdin.flush().await?;
        self.read_block().await
    }
}
pub fn can_run_z3() -> bool {
    Command::new("z3")
        .stdin(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .spawn()
        .is_ok()
}

lazy_static! {
    static ref HAS_Z3: bool = can_run_z3();
}
#[derive(Clone, Debug)]
pub enum AssertName {
    Config,
    Constraint,
    Attribute,
    Group,
    GroupMember,
    GroupMin,
    GroupMax,
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
        }
    }
}
#[derive(Debug, Clone)]
pub struct AssertInfo(pub ModuleSymbol, pub AssertName);
struct SMTModule {
    asserts: Vec<AssertInfo>,
    sym2var: IndexSet<ModuleSymbol>,
}
impl SMTModule {
    fn var(&self, ms: ModuleSymbol) -> usize {
        self.sym2var.get_index_of(&ms).unwrap()
    }
    fn pseudo_bool(&self, ms: ModuleSymbol, module: &Module) -> String {
        let ms = module.resolve_value(ms);
        match module.type_of(ms) {
            Type::Bool => format!("v{}", self.var(ms)),
            Type::Real => format!("(not(= v{} 0.0))", self.var(ms)),
            Type::String => format!(r#"(not(= v{} ""))"#, self.var(ms)),
            _ => unimplemented!(),
        }
    }
}

impl SMTModule {
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
            let var = *self.sym2var.get_index(idx).unwrap();
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
    pub fn parse_values<'a>(
        &'a self,
        values: &'a str,
    ) -> impl Iterator<Item = (ModuleSymbol, ConfigValue)> + 'a {
        lazy_static! {
            static ref RE: Regex = Regex::new(
                r#"\(\s*v(\d+)\s+(?:(true|false)|([+-]?(?:[0-9]*\.)?[0-9]+)|"([^"]*)")\s*\)"#
            )
            .unwrap();
        };
        //info!("{values}");
        RE.captures_iter(values).map(|i| {
            let idx: usize = i[1].parse().unwrap();
            let var = *self.sym2var.get_index(idx).unwrap();
            (
                var,
                match (i.get(2), i.get(3), &i.get(4)) {
                    (Some(b), _, _) => ConfigValue::Bool(match b.as_str() {
                        "true" => true,
                        _ => false,
                    }),
                    (_, Some(num), _) => ConfigValue::Number(num.as_str().parse().unwrap()),
                    (_, _, Some(s)) => ConfigValue::String(s.as_str().into()),
                    _ => unreachable!(),
                },
            )
        })
    }
    pub fn parse_unsat_core<'a>(&'a self, core: &'a str) -> impl Iterator<Item = AssertInfo> + 'a {
        lazy_static! {
            static ref RE: Regex = Regex::new(r"a(\d+)").unwrap();
        };
        RE.captures_iter(core).map(|i| {
            let idx: usize = i[1].parse().unwrap();
            self.asserts[idx].clone()
        })
    }
}
struct SMTBuilder<'a> {
    sym2var: IndexSet<ModuleSymbol>,
    assert: Vec<AssertInfo>,
    module: &'a Module,
}
impl<'a> SMTBuilder<'a> {
    fn var(&self, ms: ModuleSymbol) -> usize {
        self.sym2var
            .get_index_of(&self.module.resolve_value(ms))
            .unwrap()
    }
    fn pseudo_bool(&self, ms: ModuleSymbol) -> String {
        let ms = self.module.resolve_value(ms);
        match self.module.type_of(ms) {
            Type::Bool => format!("v{}", self.var(ms)),
            Type::Real => format!("(not(= v{} 0.0))", self.var(ms)),
            Type::String => format!(r#"(not(= v{} ""))"#, self.var(ms)),
            _ => unimplemented!(),
        }
    }
    fn clause(&self, g: ModuleSymbol) -> String {
        self.module
            .file(g.instance)
            .direct_children(g.sym)
            .map(|i| self.pseudo_bool(g.instance.sym(i)))
            .join(" ")
    }
    fn min_assert(&mut self, min: usize, p_bind: &str, g: ModuleSymbol) -> String {
        let name = self.push_assert(AssertInfo(g, AssertName::GroupMin));
        let clause = self.clause(g);
        format!("(assert(!(=> {p_bind} ( (_ at-least {min}) {clause}) ):named a{name}))")
    }
    fn max_assert(&mut self, max: usize, p_bind: &str, g: ModuleSymbol) -> String {
        let name = self.push_assert(AssertInfo(g, AssertName::GroupMax));
        let clause = self.clause(g);
        format!("(assert(!(=> {p_bind} ( (_ at-most {max}) {clause}) ):named a{name}))")
    }
    fn push_var(&mut self, ms: ModuleSymbol) -> usize {
        self.sym2var.insert(ms);
        self.sym2var.len() - 1
    }
    fn push_assert(&mut self, name: AssertInfo) -> usize {
        self.assert.push(name);
        self.assert.len() - 1
    }
}

//We need special formating for SMT, so we reimplement display
struct SmtConfigValue<'a>(&'a ConfigValue);
impl<'a> Display for SmtConfigValue<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            ConfigValue::Bool(x) => {
                write!(f, "{x}")
            }
            ConfigValue::Number(x) => {
                write!(f, "{:?}", x)
            }
            ConfigValue::String(x) => {
                write!(f, "\"{x}\"")
            }
        }
    }
}
impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

//Encodes a UVL module into an SMT-LIB module
fn create_module<'a>(
    module: &Module,
    config: &HashMap<ModuleSymbol, ConfigValue>,
) -> (String, SMTModule) {
    let mut out = "(set-option :pp.decimal true)(set-option :produce-unsat-cores true)(define-fun smooth_div ((x Real) (y Real)) Real(if (not (= y 0.0))(/ x y)0.0))\n".to_string();
    //info!("{module:#?}");
    let mut builder = SMTBuilder {
        module,
        sym2var: IndexSet::new(),
        assert: Vec::new(),
    };
    //Encode features
    for (m, file) in module.instances() {
        for f in file.all_features() {
            let ms = m.sym(f);
            let ty = file.type_of(f).unwrap();
            let var = builder.push_var(ms);
            let _ = writeln!(out, "(declare-const v{var} {ty})");
        }
    }
    for (&ms, val) in config
        .iter()
        .filter(|i| matches!(i.0.sym, Symbol::Feature(..)))
    {
        let val = SmtConfigValue(val);
        let var = builder.var(ms);
        let name = builder.push_assert(AssertInfo(ms, AssertName::Config));
        let _ = writeln!(out, "(assert(!(= v{var} {val}):named a{name}))");
    }
    //Encode attributes
    for (m, file) in module.instances() {
        for f in file.all_features() {
            file.visit_named_children(f, true, |a, _| {
                if !matches!(a, Symbol::Attribute(..)) {
                    return true;
                }
                let ms = m.sym(a);
                let Some((val, n)) = config.get(&ms).map(|v|(v.clone(),AssertInfo(ms,AssertName::Config) )).or_else(|| {
                    file.value(a)
                        .and_then(|v| match v {
                            Value::Bool(x) => Some(ConfigValue::Bool(*x)),
                            Value::Number(x) => Some(ConfigValue::Number(*x)),
                            Value::String(x) => Some(ConfigValue::String(x.clone())),
                            _ => None,
                        })
                        .map(|v| (v, AssertInfo(ms,AssertName::Attribute)))
                }) else {return true} ;
                let zero = match val {
                    ConfigValue::Bool(..) => ConfigValue::Bool(false),
                    ConfigValue::Number(..) => ConfigValue::Number(0.0),
                    ConfigValue::String(..) => ConfigValue::String("".into()),
                };
                let zero = SmtConfigValue(&zero);
                let val = SmtConfigValue(&val);
                let attrib_var = builder.push_var(ms);
                let ty = file.type_of(a).unwrap();
                let _ = writeln!(out, "(declare-const v{attrib_var} {ty})");
                let feat_var = builder.pseudo_bool(m.sym(f));
                let name = builder.push_assert(n);
                let _ = writeln!(
                    out,
                    "(assert(!(= (ite {feat_var} {val} {zero}) v{attrib_var}):named a{name}))"
                );
                true
            });
        }
    }
    //Encode groups
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
                    let _ = writeln!(out, "(assert(=> {c_bind} {p_bind}))");
                }
                match file.group_mode(g).unwrap() {
                    GroupMode::Or => {
                        let clause = builder.clause(m.sym(g));
                        let name = builder.push_assert(AssertInfo(m.sym(g), AssertName::Group));
                        let _ =
                            writeln!(out, "(assert(!(=> {p_bind} (or {clause}) ):named a{name}))");
                    }
                    GroupMode::Alternative => {
                        let _ = writeln!(out, "{}", builder.min_assert(1, &p_bind, m.sym(g)));
                        let _ = writeln!(out, "{}", builder.max_assert(1, &p_bind, m.sym(g)));
                    }
                    GroupMode::Mandatory => {
                        for c in file.direct_children(g) {
                            let c_bind = builder.pseudo_bool(m.sym(c));
                            let name =
                                builder.push_assert(AssertInfo(m.sym(c), AssertName::GroupMember));
                            let _ = writeln!(out, "(assert(!(= {c_bind} {p_bind}):named a{name}))");
                        }
                    }
                    GroupMode::Optional | GroupMode::Cardinality(Cardinality::Any) => {}
                    GroupMode::Cardinality(Cardinality::Max(max)) => {
                        let _ = writeln!(out, "{}", builder.max_assert(max, &p_bind, m.sym(g)));
                    }

                    GroupMode::Cardinality(Cardinality::From(min)) => {
                        let _ = writeln!(out, "{}", builder.min_assert(min, &p_bind, m.sym(g)));
                    }
                    GroupMode::Cardinality(Cardinality::Range(min, max)) => {
                        let _ = writeln!(out, "{}", builder.min_assert(min, &p_bind, m.sym(g)));
                        let _ = writeln!(out, "{}", builder.max_assert(max, &p_bind, m.sym(g)));
                    }
                }
            }
        }
    }
    //make root features mandatory
    for (m, file) in module.instances() {
        for f in file
            .direct_children(Symbol::Root)
            .filter(|f| matches!(f, Symbol::Feature(..)))
        {
            let _ = writeln!(out, "(assert {})", builder.pseudo_bool(m.sym(f)));
        }
    }
    //encode constraints
    #[derive(Debug)]
    enum CExpr<'a> {
        Constraint(&'a ConstraintDecl),
        Expr(&'a ExprDecl),
        End,
    }
    for (m, file) in module.instances() {
        for c in file.all_constraints() {
            let mut stack = vec![CExpr::Constraint(&file.constraint(c).unwrap())];
            //info!("{stack:?}");
            let _ = write!(out, "(assert (! ");
            while let Some(expr) = stack.pop() {
                match expr {
                    CExpr::Constraint(expr) => match &expr.content {
                        Constraint::Constant(val) => {
                            let _ = write!(out, " {val}");
                        }
                        Constraint::Ref(sym) => {
                            let name = builder.var(m.sym(*sym));
                            let _ = write!(out, " v{name}");
                        }
                        Constraint::Not(lhs) => {
                            let _ = write!(out, "(not ");
                            stack.push(CExpr::End);
                            stack.push(CExpr::Constraint(lhs));
                        }
                        Constraint::Logic { op, lhs, rhs } => {
                            match op {
                                LogicOP::And => {
                                    let _ = write!(out, "(and ");
                                }
                                LogicOP::Or => {
                                    let _ = write!(out, "(or ");
                                }
                                LogicOP::Implies => {
                                    let _ = write!(out, "(=> ");
                                }
                                LogicOP::Equiv => {
                                    let _ = write!(out, "(= ");
                                }
                            }
                            stack.push(CExpr::End);
                            stack.push(CExpr::Constraint(rhs));
                            stack.push(CExpr::Constraint(lhs));
                        }
                        Constraint::Equation { op, lhs, rhs } => {
                            match op {
                                EquationOP::Greater => {
                                    let _ = write!(out, "(> ");
                                }
                                EquationOP::Equal => {
                                    let _ = write!(out, "(= ");
                                }
                                EquationOP::Smaller => {
                                    let _ = write!(out, "(< ");
                                }
                            }
                            stack.push(CExpr::End);
                            stack.push(CExpr::Expr(rhs));
                            stack.push(CExpr::Expr(lhs));
                        }
                    },
                    CExpr::Expr(expr) => match &expr.content {
                        Expr::Number(val) => {
                            let _ = write!(out, " {:?}", val);
                        }
                        Expr::String(val) => {
                            let _ = write!(out, "\"{val}\"");
                        }
                        Expr::Ref(sym) => {
                            let name = builder.var(m.sym(*sym));
                            let _ = write!(out, " v{name}");
                        }
                        Expr::Len(lhs) => {
                            let _ = write!(out, "(str.len ");
                            stack.push(CExpr::End);
                            stack.push(CExpr::Expr(lhs));
                        }
                        Expr::Binary { op, rhs, lhs } => {
                            match op {
                                NumericOP::Add => {
                                    let _ = write!(out, "(+ ");
                                }
                                NumericOP::Sub => {
                                    let _ = write!(out, "(- ");
                                }
                                NumericOP::Mul => {
                                    let _ = write!(out, "(* ");
                                }
                                NumericOP::Div => {
                                    let _ = write!(out, "(/ ");
                                }
                            }
                            stack.push(CExpr::End);
                            stack.push(CExpr::Expr(rhs));
                            stack.push(CExpr::Expr(lhs));
                        }
                        Expr::Aggregate { op, context, query } => {
                            let mut all_attributes = String::new();
                            let mut count_features = String::new();
                            let tgt = context
                                .map(|sym| module.resolve_value(m.sym(sym)))
                                .unwrap_or(m.sym(Symbol::Root));
                            let tgt_file = module.file(tgt.instance);
                            tgt_file.visit_attributes(tgt.sym, |feature, attrib, prefix| {
                                if prefix == query.names.as_slice()
                                    && tgt_file.type_of(attrib).unwrap() == Type::Real
                                {
                                    let _ = write!(
                                        count_features,
                                        "(ite {}  1.0 0.0)",
                                        builder.pseudo_bool(tgt.instance.sym(feature))
                                    );
                                    let name = builder.var(tgt.instance.sym(attrib));
                                    let _ = write!(all_attributes, " v{name}");
                                }
                            });
                            if all_attributes.is_empty() {
                                let _ = write!(out, " 0.0");
                            }
                            match op {
                                AggregateOP::Sum => {
                                    let _ = write!(out, "(+ {all_attributes})");
                                }
                                AggregateOP::Avg => {
                                    let _ = write!(
                                        out,
                                        "(smooth_div(+ {all_attributes}) (+ {count_features}))",
                                    );
                                }
                            };
                        }
                    },
                    CExpr::End => {
                        let _ = write!(out, ")");
                    }
                }
            }
            let name = builder.push_assert(AssertInfo(m.sym(c), AssertName::Constraint));
            let _ = write!(out, " :named a{name}))\n");
        }
    }
    //info!("{out}");
    (
        out,
        SMTModule {
            sym2var: builder.sym2var,
            asserts: builder.assert,
        },
    )
}

#[derive(Debug, Clone)]
pub enum SMTValueState {
    Any,
    On,
    Off,
}
#[derive(Debug, Clone)]
pub enum SMTModel {
    SAT {
        values: HashMap<ModuleSymbol, ConfigValue>,
        fixed: HashMap<ModuleSymbol, SMTValueState>,
    },
    UNSAT {
        reasons: Vec<AssertInfo>,
    },
}
pub struct OwnedSMTModel {
    pub model: SMTModel,
    pub modul: Arc<Module>,
}
impl Default for SMTModel {
    fn default() -> Self {
        Self::SAT {
            values: HashMap::new(),
            fixed: HashMap::new(),
        }
    }
}
//find constant boolean values for dead features and other cool analysis
//this is quite naive and should be improved with a better solver
async fn find_fixed(
    solve: &mut SmtSolver,
    base_module: &Module,
    module: &SMTModule,
    initial_model: impl Iterator<Item = (ModuleSymbol, ConfigValue)>,
) -> Result<HashMap<ModuleSymbol, SMTValueState>> {
    let mut state = HashMap::new();
    for (s, v) in initial_model {
        match v {
            ConfigValue::Bool(true) => {
                state.insert(s, SMTValueState::On);
            }
            ConfigValue::Bool(false) => {
                state.insert(s, SMTValueState::Off);
            }
            _ => {}
        }
    }
    let keys: Vec<ModuleSymbol> = state.keys().cloned().collect();
    for k in keys {
        match &state[&k] {
            SMTValueState::Any => {
                continue;
            }
            SMTValueState::On => {
                solve
                    .push(format!(
                        "(push 1)(assert (not {}))",
                        module.pseudo_bool(k, base_module)
                    ))
                    .await?;
            }
            SMTValueState::Off => {
                solve
                    .push(format!(
                        "(push 1)(assert {})",
                        module.pseudo_bool(k, base_module)
                    ))
                    .await?;
            }
        }
        //let time = Instant::now();
        if solve.check_sat().await? {
            //info!("check sat {:?}", time.elapsed());
            let unknown = state
                .iter()
                .filter(|(_, v)| !matches!(*v, SMTValueState::Any))
                .fold(String::new(), |acc, (k, _)| {
                    format!("{acc} v{}", module.var(*k))
                });
            let values = solve.values(unknown).await?;
            //info!("model {:?}", time.elapsed());
            for (s, v) in module.parse_values(&values) {
                if let Some(old) = state.get(&s) {
                    match (v, old) {
                        (ConfigValue::Bool(true), SMTValueState::Off) => {
                            state.insert(s, SMTValueState::Any);
                        }
                        (ConfigValue::Bool(false), SMTValueState::On) => {
                            state.insert(s, SMTValueState::Any);
                        }
                        _ => {}
                    }
                }
            }

            //info!("parse {:?}", time.elapsed());
        }
        solve.push("(pop 1)".into()).await?;
    }
    Ok(state)
}
async fn create_model(
    base_module: &Module,
    cancel: CancellationToken,
    module: SMTModule,
    source: String,
    fixed: bool,
    value: bool,
) -> Result<SMTModel> {
    let mut solver = SmtSolver::new(source, &cancel).await?;
    if solver.check_sat().await? {
        let values = if value | fixed {
            let query = module
                .sym2var
                .iter()
                .enumerate()
                .fold(String::new(), |acc, (i, _)| format!("{acc} v{i}"));
            module.parse_values(&solver.values(query).await?).collect()
        } else {
            HashMap::new()
        };
        Ok(SMTModel::SAT {
            fixed: if fixed {
                find_fixed(
                    &mut solver,
                    base_module,
                    &module,
                    values.iter().map(|(k, v)| (*k, v.clone())),
                )
                .await?
            } else {
                HashMap::new()
            },
            values,
        })
    } else {
        let core = solver.unsat_core().await?;
        Ok(SMTModel::UNSAT {
            reasons: module.parse_unsat_core(&core).collect(),
        })
    }
}

async fn check_base_sat(
    root: &RootGraph,
    tx_err: &mpsc::Sender<DiagnosticUpdate>,
    latest_revisions: HashMap<FileID, Instant>,
) -> HashMap<FileID, Instant> {
    let active = root.cache().modules.iter().filter(|(k, v)| {
        latest_revisions
            .get(*k)
            .map(|old| old != &v.timestamp)
            .unwrap_or(true)
            && v.ok
    });
    let models = join_all(active.map(|(k, v)| {
        let k = k.clone();
        let module = v.clone();
        async move {
            let (smt_module, source) = create_module(&module, &HashMap::new());
            let model = create_model(
                &module,
                root.cancellation_token(),
                source,
                smt_module,
                true,
                false,
            )
            .await;
            model.map(|m| (m, k, module))
        }
    }))
    .await;

    let mut e = ErrorsAcc::new(root);
    for k in models.into_iter() {
        match k {
            Ok((SMTModel::SAT { fixed, .. }, root_file, module)) => {
                let mut visited = HashSet::new();
                for (m, file) in module.instances() {
                    file.visit_children(Symbol::Root, true, |sym| match sym {
                        Symbol::Feature(..) => {
                            if let Some(val) = fixed.get(&m.sym(sym)) {
                                match val {
                                    SMTValueState::Off => {
                                        if visited.insert((sym, file.id)) {
                                            e.sym_info(sym, file.id, 10, "dead feature");
                                        }
                                        false
                                    }
                                    SMTValueState::On => {
                                        //Is this even a good idea?
                                        true
                                    }
                                    _ => true,
                                }
                            } else {
                                true
                            }
                        }
                        Symbol::Group(..) => true,
                        _ => false,
                    })
                }
            }
            Ok((SMTModel::UNSAT { reasons }, _, module)) => {
                let mut visited = HashSet::new();
                for r in reasons {
                    let file = module.file(r.0.instance).id;

                    if visited.insert((r.0.sym, file)) {
                        e.sym(r.0.sym, file, 12, format!("UNSAT: {}", r.1))
                    }
                }
            }
            Err(e) => {
                info!("SMT check failed: {e}");
            }
        }
    }
    let _ = tx_err
        .send(DiagnosticUpdate {
            timestamp: root.revision(),
            error_state: e.errors,
        })
        .await;
    root.cache()
        .modules
        .iter()
        .map(|(k, v)| (*k, v.timestamp))
        .collect()
}

async fn check_config(
    root: &RootGraph,
    tx_err: &mpsc::Sender<DiagnosticUpdate>,
    inlay_state: &InlayHandler,
    latest_revisions: HashMap<FileID, Instant>,
) -> HashMap<FileID, Instant> {
    let active = root.cache().config_modules.iter().filter(|(k, v)| {
        latest_revisions
            .get(*k)
            .map(|old| old != &v.module.timestamp)
            .unwrap_or(true)
            && v.module.ok
    });
    let models = join_all(active.map(|(k, v)| {
        let k = k.clone();
        let module = v.clone();
        async move {
            let (source, smt_module) = create_module(&module.module, &module.values);
            let is_active = inlay_state.is_active(InlaySource::File(k));
            let model = create_model(
                &module.module,
                root.cancellation_token(),
                smt_module,
                source,
                !k.is_config(),
                is_active,
            )
            .await;

            if k.is_config() {
                if let Ok(model) = model.as_ref() {
                    inlay_state
                        .maybe_publish(InlaySource::File(k), Instant::now(), || {
                            Arc::new(OwnedSMTModel {
                                model: model.clone(),
                                modul: module.module.clone(),
                            })
                        })
                        .await;
                } else {
                    inlay_state.maybe_reset(InlaySource::File(k)).await;
                }
            }
            model.map(|m| (m, k, module))
        }
    }))
    .await;

    let mut e = ErrorsAcc::new(root);
    for k in models.into_iter() {
        match k {
            Ok((SMTModel::SAT { .. }, ..)) => {
                //Do something?
            }
            Ok((SMTModel::UNSAT { reasons }, root_file, module)) => {
                for r in reasons {
                    if matches!(r.1, AssertName::Config) {
                        e.span(
                            module.source_map[&r.0].clone(),
                            module.module.file(r.0.instance).id,
                            12,
                            format!("UNSAT!"),
                        );
                    }
                }
            }
            Err(e) => {
                info!("SMT check failed: {e}");
            }
        }
    }
    let _ = tx_err
        .send(DiagnosticUpdate {
            timestamp: root.revision(),
            error_state: e.errors,
        })
        .await;
    root.cache()
        .modules
        .iter()
        .map(|(k, v)| (*k, v.timestamp))
        .collect()
}

//SMT-checks modules when the RootGraph changed
pub async fn check_handler(
    mut rx_root: watch::Receiver<Arc<RootGraph>>,
    tx_err: mpsc::Sender<DiagnosticUpdate>,
    client: tower_lsp::Client,
    inlay_state: InlayHandler,
) {
    if !can_run_z3() {
        client
            .send_notification::<tower_lsp::lsp_types::notification::ShowMessage>(
                ShowMessageParams {
                    typ: MessageType::INFO,
                    message: "UVLS: Z3 was not found on youre system. It is required for semantic analysis".into(),
                },
            )
            .await;
    }
    let mut latest_versions: HashMap<FileID, Instant> = HashMap::new();
    let mut latest_versions_config: HashMap<FileID, Instant> = HashMap::new();
    loop {
        info!("Check SMT");
        let root = rx_root.borrow_and_update().clone();
        latest_versions = check_base_sat(&root, &tx_err, latest_versions).await;
        latest_versions_config =
            check_config(&root, &tx_err, &inlay_state, latest_versions_config).await;
        if rx_root.changed().await.is_err() {
            break;
        }
    }
}
pub async fn web_view_handler(
    mut state: watch::Receiver<webview::ConfigSource>,
    tx_ui: mpsc::Sender<webview::UIAction>,
    inlay_state: InlayHandler,
    inlay_source: InlaySource,
) -> Result<()> {
    loop {
        let (module, cancel, tag) = {
            let lock = state.borrow_and_update();
            (lock.module.clone(), lock.cancel.clone(), lock.tag)
        };
        info!("cancled {}", cancel.is_cancelled());

        if module.ok {
            let (source, smt_module) = create_module(&module, &module.values);
            let res = create_model(&module, cancel, smt_module, source, false, true).await;
            match res {
                Ok(model) => {
                    inlay_state
                        .maybe_publish(inlay_source, Instant::now(), || {
                            Arc::new(OwnedSMTModel {
                                model: model.clone(),
                                modul: module.module.clone(),
                            })
                        })
                        .await;
                    //info!("model: {model:?}");
                    tx_ui
                        .send(webview::UIAction::UpdateSMTModel(model, tag))
                        .await?;
                }
                Err(e) => {
                    //info!("err {e}");
                    inlay_state.maybe_reset(inlay_source).await;
                    tx_ui
                        .send(webview::UIAction::UpdateSMTInvalid(format!("{e}"), tag))
                        .await?;
                }
            }
        } else {
            inlay_state.maybe_reset(inlay_source).await;
            tx_ui
                .send(webview::UIAction::UpdateSMTInvalid(
                    format!("sources invalid"),
                    tag,
                ))
                .await?;
        }

        state.changed().await?;
    }
}
