use crate::{
    ast::*,
    check::{DiagnosticUpdate, ErrorsAcc},
    config::*,
    inlays::{InlayHandler, InlaySource},
    semantic::*,
    util::{maybe_cancel, Result},
};
use futures::future::join_all;
use hashbrown::HashMap;
use indexmap::IndexMap;
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
pub enum SmtName {
    Config(RootSymbol),
    Attribute(RootSymbol),
    Constraint(RootSymbol),
    GroupMember(RootSymbol),
    Group(RootSymbol),
    GroupMin(RootSymbol),
    GroupMax(RootSymbol),
}
impl SmtName {
    pub fn symbol(&self) -> RootSymbol {
        match self {
            SmtName::Config(s)
            | SmtName::Attribute(s)
            | SmtName::Constraint(s)
            | SmtName::GroupMember(s)
            | SmtName::Group(s)
            | SmtName::GroupMin(s)
            | SmtName::GroupMax(s) => *s,
        }
    }
}
struct SMTModule {
    asserts: Vec<SmtName>,
    sym2var: IndexMap<RootSymbol, usize>,
}
impl SMTModule {
    pub fn parse_model<'a>(
        &'a self,
        model: &'a str,
    ) -> impl Iterator<Item = (RootSymbol, ConfigValue)> + 'a {
        lazy_static! {
            static ref RE: Regex =
                Regex::new(r#"\(\s*define-fun\s+v(\d+)\s+\(\)\s+(Bool|String|Real)\s+(true|false|"[^"]*"|-?[0-9]*\.[0-9]*)\s*\)"#)
                    .unwrap();
        };

        RE.captures_iter(model).map(|i| {
            let idx: usize = i[1].parse().unwrap();
            let var = *self.sym2var.get_index(idx).unwrap().0;
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
    ) -> impl Iterator<Item = (RootSymbol, ConfigValue)> + 'a {
        lazy_static! {
            static ref RE: Regex = Regex::new(
                r#"\(\s*v(\d+)\s+(?:(true|false)|([+-]?(?:[0-9]*\.)?[0-9]+)|"([^"]*)")\s*\)"#
            )
            .unwrap();
        };
        RE.captures_iter(values).map(|i| {
            let idx: usize = i[1].parse().unwrap();
            let var = *self.sym2var.get_index(idx).unwrap().0;

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
    pub fn parse_unsat_core<'a>(&'a self, core: &'a str) -> impl Iterator<Item = SmtName> + 'a {
        lazy_static! {
            static ref RE: Regex = Regex::new(r"a(\d+)").unwrap();
        };
        RE.captures_iter(core).map(|i| {
            let idx: usize = i[1].parse().unwrap();
            self.asserts[idx].clone()
        })
    }
}

fn pseudo_bool(
    root: &RootGraph,
    rs: RootSymbol,
    sym2var: &IndexMap<RootSymbol, usize>,
) -> Option<String> {
    let rs = root.resolve_sym(rs)?;
    let file = root.file(rs.file);
    match file.type_of(rs.sym)? {
        Type::Bool => Some(format!("v{}", sym2var[&rs])),
        Type::Real => Some(format!("(not(= v{} 0.0))", sym2var[&rs])),
        Type::String => Some(format!(r#"(not(= v{} ""))"#, sym2var[&rs])),
        _ => None,
    }
}
fn clause(
    root: &RootGraph,
    g: RootSymbol,
    sym2var: &IndexMap<RootSymbol, usize>,
) -> Option<String> {
    let mut out = String::new();
    for i in root.file(g.file).direct_children(g.sym) {
        let _ = write!(
            out,
            " {}",
            pseudo_bool(
                root,
                RootSymbol {
                    file: g.file,
                    sym: i
                },
                sym2var
            )?
        );
    }
    Some(out)
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

fn create_modul(
    root: &RootGraph,
    members: &[FileID],
    features: &HashMap<RootSymbol, ConfigValue>,
    attribs: &HashMap<RootSymbol, ConfigValue>,
) -> Option<(String, SMTModule)> {
    let mut asserts = Vec::new();
    let mut sym2var = IndexMap::new();
    let mut out = "(set-option :produce-unsat-cores true)(define-fun smooth_div ((x Real) (y Real)) Real(if (not (= y 0.0))(/ x y)0.0))\n".to_string();
    for &m in members {
        let file = root.file(m);
        for f in file.all_features() {
            let rs = RootSymbol { sym: f, file: m };
            let ty = file.type_of(f).unwrap();
            let var = sym2var.len();
            let _ = writeln!(out, "(declare-const v{var} {ty})");
            sym2var.insert(rs, sym2var.len());
        }
    }
    for (&rs, val) in features {
        let val = SmtConfigValue(val);
        let var = sym2var[&rs];
        let name = asserts.len();
        let _ = writeln!(out, "(assert(!(= v{var} {val}):named a{name}))");
        asserts.push(SmtName::Config(rs));
    }
    for &m in members {
        let file = root.file(m);
        for f in file.all_features() {
            file.visit_named_children(f, true, |a, _| {
                if !matches!(a, Symbol::Attribute(..)) {
                    return true;
                }
                let rs = RootSymbol { sym: a, file: m };
                let (val, n) = if let Some(val) = attribs.get(&rs) {
                    (val.clone(), SmtName::Config(rs))
                } else {
                    (
                        match file.value(a) {
                            Some(Value::Bool(x)) => ConfigValue::Bool(*x),
                            Some(Value::Number(x)) => ConfigValue::Number(*x),
                            Some(Value::String(x)) => ConfigValue::String(x.clone()),
                            _ => return true,
                        },
                        SmtName::Attribute(rs),
                    )
                };
                let zero = match val {
                    ConfigValue::Bool(..) => ConfigValue::Bool(false),
                    ConfigValue::Number(..) => ConfigValue::Number(0.0),
                    ConfigValue::String(..) => ConfigValue::String("".into()),
                };
                let zero = SmtConfigValue(&zero);
                let val = SmtConfigValue(&val);

                let attrib_var = sym2var.len();
                let ty = file.type_of(a).unwrap();
                let _ = writeln!(out, "(declare-const v{attrib_var} {ty})");
                let name = asserts.len();
                let feat_var = pseudo_bool(root, RootSymbol { sym: f, file: m }, &sym2var).unwrap();
                let _ = writeln!(
                    out,
                    "(assert(!(= (ite {feat_var} {val} {zero}) v{attrib_var}):named a{name}))"
                );
                asserts.push(n);
                sym2var.insert(rs, sym2var.len());
                true
            });
        }
    }

    for &m in members {
        let file = root.file(m);
        for p in file.all_features() {
            for g in file
                .direct_children(p)
                .filter(|sym| matches!(sym, Symbol::Group(..)))
            {
                if file.direct_children(g).next().is_none() {
                    continue;
                }
                let p_rs = RootSymbol { sym: p, file: m };
                let g_rs = RootSymbol { sym: g, file: m };
                let p_bind = pseudo_bool(root, p_rs, &sym2var)?;
                for c in file.direct_children(g) {
                    let name = asserts.len();
                    let c_bind = pseudo_bool(root, RootSymbol { sym: c, file: m }, &sym2var)?;
                    let _ = writeln!(out, "(assert(!(=> {c_bind} {p_bind}):named a{name} ))");
                    asserts.push(SmtName::GroupMember(RootSymbol { sym: c, file: m }));
                }
                match file.group_mode(g)? {
                    GroupMode::Or => {
                        let clause = clause(root, g_rs, &sym2var)?;
                        let name = asserts.len();
                        let _ =
                            writeln!(out, "(assert(!(=> {p_bind} (or {clause}) ):named a{name}))");
                        asserts.push(SmtName::Group(g_rs));
                    }
                    GroupMode::Alternative => {
                        let clause = clause(root, g_rs, &sym2var)?;
                        let name = asserts.len();
                        let _ = writeln!(
                            out,
                            "(assert(!(=> {p_bind} ( (_ at-least 1) {clause}) ):named a{name}))"
                        );
                        asserts.push(SmtName::GroupMin(g_rs));
                        let name = asserts.len();
                        let _ = writeln!(
                            out,
                            "(assert(!(=> {p_bind} ( (_ at-most 1) {clause}) ):named a{name}))"
                        );
                        asserts.push(SmtName::GroupMax(g_rs));
                    }
                    GroupMode::Mandatory => {
                        for c in file.direct_children(g) {
                            let c_bind =
                                pseudo_bool(root, RootSymbol { sym: c, file: m }, &sym2var)?;
                            let name = asserts.len();
                            let _ = writeln!(out, "(assert(!(= {c_bind} {p_bind}):named a{name}))");
                            asserts.push(SmtName::GroupMember(RootSymbol { sym: c, file: m }));
                        }
                    }
                    GroupMode::Optional | GroupMode::Cardinality(Cardinality::Any) => {}
                    GroupMode::Cardinality(Cardinality::Max(max)) => {
                        let clause = clause(root, g_rs, &sym2var)?;
                        let name = asserts.len();
                        let _ = writeln!(
                            out,
                            "(assert(!(=> {p_bind} ( (_ at-most {max}) {clause}) ):named a{name}))"
                        );
                        asserts.push(SmtName::GroupMax(g_rs));
                    }

                    GroupMode::Cardinality(Cardinality::From(min)) => {
                        let clause = clause(root, g_rs, &sym2var)?;
                        let name = asserts.len();
                        let _ = writeln!(
                            out,
                            "(assert(!(=> {p_bind} ( (_ at-least {min}) {clause}) ):named a{name}))"
                        );
                        asserts.push(SmtName::GroupMin(g_rs));
                    }
                    GroupMode::Cardinality(Cardinality::Range(min, max)) => {
                        let clause = clause(root, g_rs, &sym2var)?;
                        let name = asserts.len();
                        let _ = writeln!(
                            out,
                            "(assert(!(=> {p_bind} ( (_ at-least {min}) {clause}) ):named a{name}))"
                        );
                        asserts.push(SmtName::GroupMin(g_rs));
                        let name = asserts.len();
                        let _ = writeln!(
                            out,
                            "(assert(!(=> {p_bind} ( (_ at-most {max}) {clause}) ):named a{name}))"
                        );
                        asserts.push(SmtName::GroupMax(g_rs));
                    }
                }
            }
        }
    }
    #[derive(Debug)]
    enum CExpr<'a> {
        Constraint(&'a ConstraintDecl),
        Expr(&'a ExprDecl),
        End,
    }
    for &m in members {
        let file = root.file(m);
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
                            let name = sym2var
                                .get(&root.resolve_sym(RootSymbol { sym: *sym, file: m })?)?;
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
                            let name = sym2var
                                .get(&root.resolve_sym(RootSymbol { sym: *sym, file: m })?)?;
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
                            root.resolve_attributes_with_feature(
                                m,
                                context
                                    .map(|context| root.file(m).path(context))
                                    .unwrap_or(&[]),
                                |feature, attrib, prefix, tgt_file| {
                                    if prefix == query.names.as_slice()
                                        && tgt_file.type_of(attrib.sym).unwrap() == Type::Real
                                    {
                                        let _ = write!(
                                            count_features,
                                            "(ite {}  1.0 0.0)",
                                            pseudo_bool(root, feature, &sym2var).unwrap()
                                        );

                                        let name = sym2var[&root.resolve_sym(attrib).unwrap()];
                                        let _ = write!(all_attributes, " v{name}");
                                    }
                                },
                            );
                            if all_attributes.is_empty() {
                                let _ = write!(out, " 0.0");
                            }
                            match op {
                                AggregateOP::Sum => {
                                    let _ = write!(out, "(+ {all_attributes})");
                                }
                                AggregateOP::Avg => {
                                    let _ =
                                        write!(out,
                                        "(smooth_divuvl.  (+ {all_attributes}) (+ {count_features}))",
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
            let name = asserts.len();
            let _ = write!(out, " :named a{name}))\n");
            asserts.push(SmtName::Constraint(RootSymbol { sym: c, file: m }));
        }
    }
    //info!("{out}");
    Some((out, SMTModule { sym2var, asserts }))
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
        values: HashMap<RootSymbol, ConfigValue>,
        fixed: HashMap<RootSymbol, SMTValueState>,
    },
    UNSAT {
        reasons: Vec<SmtName>,
    },
}
impl Default for SMTModel {
    fn default() -> Self {
        Self::SAT {
            values: HashMap::new(),
            fixed: HashMap::new(),
        }
    }
}

async fn find_fixed(
    root: &RootGraph,
    solve: &mut SmtSolver,
    module: &SMTModule,
    initial_model: impl Iterator<Item = (RootSymbol, ConfigValue)>,
) -> Result<HashMap<RootSymbol, SMTValueState>> {
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
    let keys: Vec<RootSymbol> = state.keys().cloned().collect();
    for k in keys {
        match &state[&k] {
            SMTValueState::Any => {
                continue;
            }
            SMTValueState::On => {
                solve
                    .push(format!(
                        "(push 1)(assert (not {}))",
                        pseudo_bool(root, k, &module.sym2var).unwrap()
                    ))
                    .await?;
            }
            SMTValueState::Off => {
                solve
                    .push(format!(
                        "(push 1)(assert {})",
                        pseudo_bool(root, k, &module.sym2var).unwrap()
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
                    format!("{acc} v{}", module.sym2var[k])
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
    root: &RootGraph,
    module: SMTModule,
    source: String,
    fixed: bool,
) -> Result<SMTModel> {
    let mut solver = SmtSolver::new(source, &root.cancellation_token()).await?;
    if solver.check_sat().await? {
        let query = module
            .sym2var
            .iter()
            .fold(String::new(), |acc, (_, i)| format!("{acc} v{i}"));
        let values: HashMap<RootSymbol, ConfigValue> =
            module.parse_values(&solver.values(query).await?).collect();
        Ok(SMTModel::SAT {
            fixed: if fixed {
                find_fixed(
                    root,
                    &mut solver,
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

async fn check_modules(
    root: Arc<RootGraph>,
    tx_err: mpsc::Sender<DiagnosticUpdate>,
    latest_revisions: HashMap<Vec<FileID>, u64>,
) -> HashMap<Vec<FileID>, u64> {
    let models = join_all(
        root.cache()
            .modules
            .iter()
            .filter(|(k, v)| {
                latest_revisions
                    .get(*k)
                    .map(|&r| r != v.revision)
                    .unwrap_or(true)
                    && v.ok
            })
            .map(|(members, _)| {
                let root = root.clone();
                let members = members.clone();
                async move {
                    let (source, module) =
                        create_modul(&root, &members, &HashMap::new(), &HashMap::new())
                            .ok_or("model generation failed")?;
                    //info!("HIR: {:#?}", hir);
                    let model = create_model(&root, module, source, true).await;
                    model.map(|i| (i, members))
                }
            }),
    )
    .await;
    let mut e = ErrorsAcc::new(&root);
    //info!("{:#?}", models);
    for i in models.into_iter() {
        match i {
            Ok(model) => match model {
                (SMTModel::SAT { fixed, .. }, members) => {
                    for m in members {
                        root.file(m)
                            .visit_children(Symbol::Root, true, |sym| match sym {
                                Symbol::Feature(..) => {
                                    if let Some(val) = fixed.get(&RootSymbol { sym, file: m }) {
                                        match val {
                                            SMTValueState::Off => {
                                                e.sym(sym, m, 10, "dead feature");
                                                false
                                            }

                                            SMTValueState::On => {
                                                e.sym_info(sym, m, 10, "required feature");
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
                (SMTModel::UNSAT { reasons }, ..) => {
                    for i in reasons {
                        match i {
                            SmtName::Attribute(sym) => {
                                e.sym(sym.sym, sym.file, 12, "UNSAT attribute value");
                            }
                            SmtName::Constraint(sym) => {
                                e.sym(sym.sym, sym.file, 12, "UNSAT constraint");
                            }

                            SmtName::Group(sym) => {
                                e.sym(sym.sym, sym.file, 12, "UNSAT group");
                            }

                            SmtName::GroupMin(sym) => {
                                e.sym(sym.sym, sym.file, 12, "UNSAT group minimum");
                            }

                            SmtName::GroupMax(sym) => {
                                e.sym(sym.sym, sym.file, 12, "UNSAT group maximum");
                            }

                            SmtName::GroupMember(sym) => {
                                e.sym(sym.sym, sym.file, 12, "UNSAT group member");
                            }
                            _ => {}
                        }
                    }
                }
            },
            Err(e) => {
                info!("SMT check failed {e}")
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
        .map(|(k, v)| (k.clone(), v.revision))
        .collect()
}
async fn check_config(
    root: Arc<RootGraph>,
    tx_err: mpsc::Sender<DiagnosticUpdate>,
    latest_revisions: HashMap<FileID, u64>,
    inlay_handler: &InlayHandler,
) -> HashMap<FileID, u64> {
    let timestamp = Instant::now();
    for (k, v) in root.cache().config_modules.iter() {
        if inlay_handler.is_active(InlaySource::File(*k))
            && !v.ok
            && latest_revisions
                .get(k)
                .map(|l| l != &v.revision)
                .unwrap_or(true)
        {
            inlay_handler
                .maybe_publish(
                    InlaySource::File(*k),
                    &root,
                    &SMTModel::default(),
                    timestamp,
                )
                .await; //Reset inlay
        }
    }
    let models = join_all(
        root.cache()
            .config_modules
            .iter()
            .filter(|(k, v)| {
                !k.is_virtual()
                    && v.ok
                    && latest_revisions
                        .get(*k)
                        .map(|&l| l != v.revision)
                        .unwrap_or(true)
            })
            .map(|(&k, v)| {
                let root = root.clone();
                let config = v.clone();
                async move {
                    let (source, module) = create_modul(
                        &root,
                        v.members.iter().cloned().collect::<Vec<_>>().as_slice(),
                        &config.features,
                        &config.attributes,
                    )
                    .ok_or("model generation failed")?;
                    let model = create_model(&root, module, source, true).await;
                    if let Ok(model) = model.as_ref() {
                        inlay_handler
                            .maybe_publish(
                                InlaySource::File(config.doc.id),
                                &root,
                                &model,
                                timestamp,
                            )
                            .await;
                    } else {
                        inlay_handler
                            .maybe_publish(
                                InlaySource::File(config.doc.id),
                                &root,
                                &SMTModel::default(),
                                timestamp,
                            )
                            .await;
                    }
                    model.map(|m| (k, m))
                }
            }),
    )
    .await;

    let mut e = ErrorsAcc::new(&root);
    for i in models.into_iter() {
        match i {
            Ok((config, model)) => match model {
                SMTModel::SAT { fixed, .. } => {
                    for (sym, v) in fixed {
                        match v {
                            SMTValueState::On | SMTValueState::Off => {
                                if let Some(tgt) =
                                    root.cache().config_modules[&config].source_map.get(&sym)
                                {
                                    e.span_info(tgt.clone(), config, 12, "Required!");
                                }
                            }
                            _ => {}
                        }
                    }
                }
                SMTModel::UNSAT { reasons } => {
                    for r in reasons {
                        match r {
                            SmtName::Config(sym) => {
                                e.span(
                                    root.cache().config_modules[&config].source_map[&sym].clone(),
                                    config,
                                    12,
                                    "UNSAT",
                                );
                            }
                            _ => {}
                        }
                    }
                }
            },
            Err(e) => {
                info!("SMT check failed {e}")
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
        .config_modules
        .iter()
        .map(|(k, v)| (*k, v.revision))
        .collect()
}

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
    let mut latest_versions: HashMap<Vec<FileID>, u64> = HashMap::new();
    let mut latest_versions_config: HashMap<FileID, u64> = HashMap::new();
    loop {
        info!("Check SMT");
        let root = rx_root.borrow_and_update().clone();
        let (a, b) = join!(
            check_modules(root.clone(), tx_err.clone(), latest_versions.clone(),),
            check_config(
                root.clone(),
                tx_err.clone(),
                latest_versions_config.clone(),
                &inlay_state
            )
        );

        latest_versions = a;
        latest_versions_config = b;
        if rx_root.changed().await.is_err() {
            break;
        }
    }
}

//Turn paths into features and attributes
fn create_config(
    root: &RootGraph,
    files: &DirectConfig,
) -> (
    HashMap<RootSymbol, ConfigValue>,
    HashMap<RootSymbol, ConfigValue>,
    Vec<FileID>,
) {
    let mut features = HashMap::new();
    let mut attributes = HashMap::new();
    let mut members = Vec::new();
    for (fi, f) in files.iter() {
        if !root.containes_id(*fi) {
            continue;
        }
        members.push(*fi);
        for (p, v) in f.iter() {
            if let Some(rs) = root.resolve(*fi, &p).find(|rs| {
                matches!(
                    root.type_of(*rs),
                    Some(Type::String | Type::Bool | Type::Real)
                )
            }) {
                if matches!(rs.sym, Symbol::Feature(..)) {
                    features.insert(rs, v.clone());
                } else {
                    attributes.insert(rs, v.clone());
                }
            }
        }
    }
    (features, attributes, members)
}
async fn config_create_model2(
    root: &RootGraph,
    members: &[FileID],
    features: &HashMap<RootSymbol, ConfigValue>,
    attribs: &HashMap<RootSymbol, ConfigValue>,
) -> Result<SMTModel> {
    let (source, modul) =
        create_modul(root, members, &features, &attribs).ok_or("Model Generation Failure")?;
    create_model(root, modul, source, false).await
}
use crate::webview::UIAction;
pub async fn create_config_model(
    timestamp: Instant,
    root: Arc<RootGraph>,
    cancel: CancellationToken,
    config: DirectConfig,
    tx: mpsc::Sender<UIAction>,
    inlay_state: InlayHandler,
    id: u64,
) -> Result<()> {
    let (features, attributes, mut members) = create_config(&root, &config);
    members.retain(|f| root.containes_id(*f));
    let mut ok = true;
    for &m in members.iter() {
        ok &= root.cache().modules[root.cache().file2module[&m]].ok;
    }
    info!("Update SMT in handler");
    if ok {
        match maybe_cancel(
            &cancel,
            config_create_model2(&root, &members, &features, &attributes),
        )
        .await
        {
            Ok(Ok(m)) => {
                inlay_state
                    .maybe_publish(InlaySource::Web(id), &root, &m, timestamp)
                    .await;
                tx.send(UIAction::UpdateSMTModel(m, timestamp)).await?;
            }
            Err(e) | Ok(Err(e)) => {
                inlay_state
                    .maybe_publish(InlaySource::Web(id), &root, &SMTModel::default(), timestamp)
                    .await;
                tx.send(UIAction::UpdateSMTInvalid(format!("{e}"), timestamp))
                    .await?;
            }
        }
    } else {
        inlay_state
            .maybe_publish(InlaySource::Web(id), &root, &SMTModel::default(), timestamp)
            .await;
        tx.send(UIAction::UpdateSMTInvalid(
            "source files contain errors".into(),
            timestamp,
        ))
        .await?;
    }
    Ok(())
}
