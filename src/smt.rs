use crate::{
    ast::*,
    check::ErrorInfo,
    semantic::{Component, ComponentErrorState, Context, FileID, RootGraph, RootSymbol},
    util::maybe_cancel,
};
use futures::future::join_all;
use hashbrown::HashMap;
use lazy_static::lazy_static;
use log::info;
use std::error;
use std::fmt::{Display, Write};
use std::sync::Arc;
use tokio::{
    io::Lines,
    process::{ChildStdin, ChildStdout, Command},
};
use tokio::{
    io::{AsyncBufReadExt, AsyncWriteExt, BufReader, BufWriter},
    process::Child,
};
use tokio_util::sync::CancellationToken;
use tower_lsp::lsp_types::DiagnosticSeverity;
use write as write_smt;

#[derive(Debug)]
struct Bind {
    file: u16,
    sym: Symbol,
}

impl Display for Bind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.sym {
            Symbol::Feature(..) => write!(f, "f{}_{}", self.sym.offset(), self.file),
            Symbol::Group(..) => write!(f, "g{}_{}", self.sym.offset(), self.file),
            Symbol::Attribute(..) => write!(f, "a{}_{}", self.sym.offset(), self.file),
            Symbol::Constraint(..) => write!(f, "c{}_{}", self.sym.offset(), self.file),
            _ => unimplemented!(),
        }
    }
}
impl Bind {
    fn parse(src: &str) -> Option<Bind> {
        let mut numbers = src[1..].split("_").map(|i| i.parse::<usize>());
        let sym = numbers.next().unwrap().unwrap();
        let file = numbers.next().unwrap().unwrap();

        match &src[0..1] {
            "g" => Some(Bind {
                file: file as u16,
                sym: Symbol::Group(sym as u32),
            }),

            "a" => Some(Bind {
                file: file as u16,
                sym: Symbol::Attribute(sym as u32),
            }),
            "f" => Some(Bind {
                file: file as u16,
                sym: Symbol::Feature(sym as u32),
            }),

            "c" => Some(Bind {
                file: file as u16,
                sym: Symbol::Constraint(sym as u32),
            }),

            _ => None,
        }
    }
}
struct Binding<'a> {
    root: &'a RootGraph,
    index: HashMap<FileID, u16>,
    members: &'a [FileID],
}
impl<'a> Binding<'a> {
    fn bind(&self, sym: Symbol, file_id: FileID) -> Option<Bind> {
        let tgt = self.root.resolve_sym(RootSymbol { file: file_id, sym })?;
        Some(Bind {
            file: self.index[&tgt.file],
            sym: tgt.sym,
        })
    }
}

fn declare_features(ctx: &Binding, file_id: FileID) -> String {
    let mut out = String::new();
    for i in ctx.root.file(file_id).all_features() {
        let _ = write_smt!(
            out,
            "(declare-const {} Bool)",
            ctx.bind(i, file_id).unwrap()
        );
    }
    out
}
fn declare_attributes(ctx: &Binding, file_id: FileID) -> String {
    let mut out = String::new();
    let file = ctx.root.file(file_id);
    for i in file.all_features() {
        file.visit_children(i, true, |sym| match file.value(sym) {
            Some(Value::Number(num)) => {
                let _ = write_smt!(
                    out,
                    "(define-fun {} () Real (ite {}  {:?} 0.0) )",
                    ctx.bind(sym, file_id).unwrap(),
                    ctx.bind(i, file_id).unwrap(),
                    num
                );
                true
            }
            Some(..) => true,
            _ => false,
        });
    }
    out
}
fn gather_clause(ctx: &Binding, file: &Document, file_id: FileID, g: Symbol) -> Option<String> {
    let mut clause = String::new();
    for c in file.direct_children(g) {
        let _ = write!(clause, " {}", ctx.bind(c, file_id)?);
    }
    Some(clause)
}
fn declare_groups(ctx: &Binding, file_id: FileID) -> Option<String> {
    let mut out = String::new();
    let file = &ctx.root.file(file_id);
    if !file.errors.is_empty() {
        return None;
    }
    for p in file.all_features() {
        for g in file
            .direct_children(p)
            .filter(|sym| matches!(sym, Symbol::Group(..)))
        {
            if file.direct_children(g).next().is_none() {
                continue;
            }
            let p_bind = ctx.bind(p, file_id)?;
            let g_bind = ctx.bind(g, file_id)?;
            match file.group_mode(g)? {
                GroupMode::Or => {
                    let clause = gather_clause(ctx, file, file_id, g);
                    let _ = write_smt!(
                        out,
                        "(assert(!(= {} (or {})):named {})) ",
                        p_bind,
                        clause?,
                        g_bind
                    );
                }
                GroupMode::Alternative => {
                    let clause = gather_clause(ctx, file, file_id, g);
                    let _ = write_smt!(
                        out,
                        "(assert(!(=> {} ((_ at-most 1) {})):named {}))",
                        p_bind,
                        clause?,
                        g_bind
                    );
                }
                GroupMode::Mandatory => {
                    for c in file.direct_children(g) {
                        let _ = write_smt!(
                            out,
                            "(assert(! (= {} {}):named {}.{}))",
                            p_bind,
                            ctx.bind(c, file_id)?,
                            g_bind,
                            ctx.bind(c, file_id)?
                        );
                    }
                }
                GroupMode::Optional | GroupMode::Cardinality(Cardinality::Any) => {
                    for c in file.direct_children(g) {
                        let _ = write_smt!(
                            out,
                            "(assert(!(=> {} {}):named {}.{}))",
                            p_bind,
                            ctx.bind(c, file_id)?,
                            g_bind,
                            ctx.bind(c, file_id)?
                        );
                    }
                }
                GroupMode::Cardinality(Cardinality::Max(max)) => {
                    let clause = gather_clause(ctx, file, file_id, g);
                    let _ = write_smt!(
                        out,
                        "(assert(!(=> {}((_ at-most {}) {})):named {}))",
                        p_bind,
                        max,
                        clause?,
                        g_bind
                    );
                }

                GroupMode::Cardinality(Cardinality::From(min)) => {
                    let clause = gather_clause(ctx, file, file_id, g);
                    let _ = write_smt!(
                        out,
                        "(assert(!(=> {} ((_ at-atleast {}) {})):named {}))",
                        p_bind,
                        min,
                        clause?,
                        g_bind,
                    );
                }
                GroupMode::Cardinality(Cardinality::Range(min, max)) => {
                    let clause = gather_clause(ctx, file, file_id, g)?;
                    let _ = write_smt!(
                        out,
                        "(assert(!(=> {} ((_ at-most {}) {})):named {}.max))",
                        p_bind,
                        max,
                        clause,
                        g_bind
                    );
                    let _ = write_smt!(
                        out,
                        "(assert(!(=> {} ((_ at-least {}) {})):named {}.min))",
                        p_bind,
                        min,
                        clause,
                        g_bind
                    );
                }
            }
        }
    }
    Some(out)
}
fn encode_numeric(ctx: &Binding, file_id: FileID, expr: &Numeric) -> Option<String> {
    match expr {
        Numeric::Number(num) => Some(format!("{:?}", num)),
        Numeric::Ref(id) => Some(format!("{}", ctx.bind(*id, file_id)?)),
        Numeric::Binary { op, rhs, lhs } => {
            let op_str = match op {
                NumericOP::Add => "+",
                NumericOP::Sub => "-",
                NumericOP::Mul => "*",
                NumericOP::Div => "smooth_div",
            };
            Some(format!(
                "({} {} {})",
                op_str,
                stacker::maybe_grow(32 * 1024, 1024 * 1024, || encode_numeric(ctx, file_id, lhs))?,
                stacker::maybe_grow(32 * 1024, 1024 * 1024, || encode_numeric(ctx, file_id, rhs))?
            ))
        }
        Numeric::Aggregate { op, context, query } => {
            let mut all_attributes = String::new();
            let mut count_features = String::new();
            ctx.root.resolve_attributes_with_feature(
                file_id,
                context
                    .map(|context| ctx.root.file(file_id).path(context))
                    .unwrap_or(&[]),
                |feature, attrib, prefix, tgt_file| {
                    if prefix == query.names.as_slice()
                        && tgt_file.type_of(attrib.sym).unwrap() == Type::Number
                    {
                        let _ = write!(
                            count_features,
                            " (ite {}  1.0 0.0)",
                            ctx.bind(feature.sym, feature.file).unwrap()
                        );
                        let _ = write!(
                            all_attributes,
                            " {}",
                            ctx.bind(attrib.sym, attrib.file).unwrap()
                        );
                    }
                },
            );
            if all_attributes.is_empty() {
                return Some("0.0".into());
            }
            match op {
                AggregateOP::Sum => Some(format!("(+ {})", all_attributes)),
                AggregateOP::Avg => Some(format!(
                    "(smooth_div  (+ {}) (+ {}))",
                    all_attributes, count_features
                )),
            }
        }
    }
}

fn encode_constraint(ctx: &Binding, file_id: FileID, constraint: &Constraint) -> Option<String> {
    match constraint {
        Constraint::Constant(val) => Some(format!("{}", val)),
        Constraint::Ref(id) => Some(format!("{}", ctx.bind(*id, file_id)?)),
        Constraint::Not(lhs) => Some(format!(
            "(not {})",
            stacker::maybe_grow(32 * 1024, 1024 * 1024, || encode_constraint(
                ctx, file_id, lhs
            ))?,
        )),
        Constraint::Logic { op, lhs, rhs } => {
            let op_str = match op {
                LogicOP::Or => "or",
                LogicOP::And => "and",
                LogicOP::Equiv => "=",
                LogicOP::Implies => "=>",
            };
            Some(format!(
                "({} {} {})",
                op_str,
                stacker::maybe_grow(32 * 1024, 1024 * 1024, || encode_constraint(
                    ctx, file_id, lhs
                ))?,
                stacker::maybe_grow(32 * 1024, 1024 * 1024, || encode_constraint(
                    ctx, file_id, rhs
                ))?,
            ))
        }
        Constraint::Equation { op, lhs, rhs } => {
            let op_str = match op {
                EquationOP::Equal => "=",
                EquationOP::Greater => ">",
                EquationOP::Smaller => "<",
            };
            Some(format!(
                "({} {} {})",
                op_str,
                stacker::maybe_grow(32 * 1024, 1024 * 1024, || encode_numeric(ctx, file_id, lhs))?,
                stacker::maybe_grow(32 * 1024, 1024 * 1024, || encode_numeric(ctx, file_id, rhs))?
            ))
        }
    }
}

fn encode_constraints(ctx: &Binding, file_id: FileID) -> Option<String> {
    let mut out = String::new();
    let file = ctx.root.file(file_id);
    for c in file.all_constraints() {
        let scope = file.scope(c);
        match scope {
            Symbol::Feature(..) => {
                let _ = write_smt!(
                    out,
                    "(assert (! (=> {}  {}) :named {}))",
                    ctx.bind(scope, file_id)?,
                    encode_constraint(ctx, file_id, file.constraint(c).unwrap())?,
                    ctx.bind(c, file_id)?,
                );
            }
            Symbol::Root => {
                let _ = write_smt!(
                    out,
                    "(assert (! {} :named {}))",
                    encode_constraint(ctx, file_id, file.constraint(c).unwrap())?,
                    ctx.bind(c, file_id)?,
                );
            }
            _ => {}
        }
    }
    Some(out)
}

async fn smtlib_model<'a>(ctx: &'a Binding<'a>) -> Option<String> {
    if ctx
        .members
        .iter()
        .any(|f| ctx.root.file(*f).errors.len() > 0)
    {
        return None;
    }
    let mut out = "(set-option :produce-unsat-cores true)(define-fun smooth_div ((x Real) (y Real)) Real(if (not (= y 0.0))(/ x y)0.0))".to_string();
    let _ = write_smt!(
        out,
        "{}",
        ctx.members
            .iter()
            .map(|f| declare_features(ctx, *f))
            .collect::<String>()
    );
    let _ = write_smt!(
        out,
        "{}",
        ctx.members
            .iter()
            .map(|f| declare_attributes(ctx, *f))
            .collect::<String>()
    );
    for file in ctx.members.iter() {
        let _ = write_smt!(out, "{}", declare_groups(ctx, *file)?);
    }
    for file in ctx.members.iter() {
        let _ = write_smt!(out, "{}", encode_constraints(ctx, *file)?);
    }
    let _ = write_smt!(out, "{}", "\n");
    Some(out)
}
#[derive(Debug)]
enum Reason {
    Single(Bind),
    GroubMember(Bind, Bind),
    GroupMin(Bind),
    GroupMax(Bind),
}
impl Reason {
    fn parse(src: &str) -> Option<Reason> {
        let mut segs = src.split(".");
        let head = Bind::parse(segs.next().unwrap())?;
        if let Some(sub) = segs.next() {
            match sub {
                "min" => Some(Reason::GroupMin(head)),
                "max" => Some(Reason::GroupMin(head)),
                _ => Some(Self::GroubMember(head, Bind::parse(sub)?)),
            }
        } else {
            Some(Reason::Single(head))
        }
    }
}

fn parse_core(ctx: &Binding, core: String) -> HashMap<FileID, Vec<ErrorInfo>> {
    let mut out = HashMap::new();
    for r in core[1..core.len() - 1].split(" ").map(Reason::parse) {
        //info!("Reason: {:?}",r );
        match r {
            Some(Reason::Single(Bind { file, sym })) => {
                let file = ctx.members[file as usize];
                match sym {
                    Symbol::Group(..) => {
                        insert_multi(
                            &mut out,
                            file,
                            ErrorInfo {
                                location: ctx.root.file(file).lsp_range(sym).unwrap(),
                                severity: DiagnosticSeverity::WARNING,
                                msg: "unsatisfiable group".into(),
                                weight: 20,
                            },
                        );
                    }
                    Symbol::Constraint(..) => {
                        insert_multi(
                            &mut out,
                            file,
                            ErrorInfo {
                                location: ctx.root.file(file).lsp_range(sym).unwrap(),
                                severity: DiagnosticSeverity::WARNING,
                                msg: "unsatisfiable constraint".into(),
                                weight: 20,
                            },
                        );
                    }
                    _ => {}
                }
            }
            Some(Reason::GroupMin(Bind { file, sym })) => {
                let file = ctx.members[file as usize];
                insert_multi(
                    &mut out,
                    file,
                    ErrorInfo {
                        location: ctx.root.file(file).lsp_range(sym).unwrap(),
                        severity: DiagnosticSeverity::WARNING,
                        msg: "unsatisfiable group minimum".into(),
                        weight: 20,
                    },
                );
            }
            Some(Reason::GroupMax(Bind { file, sym })) => {
                let file = ctx.members[file as usize];
                insert_multi(
                    &mut out,
                    file,
                    ErrorInfo {
                        location: ctx.root.file(file).lsp_range(sym).unwrap(),
                        severity: DiagnosticSeverity::WARNING,
                        msg: "unsatisfiable group maximum".into(),
                        weight: 20,
                    },
                );
            }
            Some(Reason::GroubMember(Bind { .. }, Bind { file, sym })) => {
                let file = ctx.members[file as usize];
                insert_multi(
                    &mut out,
                    file,
                    ErrorInfo {
                        location: ctx.root.file(file).lsp_range(sym).unwrap(),
                        severity: DiagnosticSeverity::WARNING,
                        msg: "unsatisfiable group member".into(),
                        weight: 20,
                    },
                );
            }
            _ => {}
        }
    }
    out
}
type Result<T> = std::result::Result<T, Box<dyn error::Error>>;

struct SmtModel {
    proc: Child,
    stdin: BufWriter<ChildStdin>,
    stdout: Lines<BufReader<ChildStdout>>,
}
impl SmtModel {
    async fn new(model: String, cancel: &CancellationToken) -> Result<Self> {
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
        maybe_cancel(&cancel, stdin.write(model.as_bytes())).await??;
        stdin.flush().await?;
        Ok(SmtModel {
            proc,
            stdin,
            stdout,
        })
    }
    async fn check_sat(&mut self, cancel: &CancellationToken) -> Result<bool> {
        maybe_cancel(&cancel, self.stdin.write("(check-sat)\n".as_bytes())).await??;
        self.stdin.flush().await?;
        Ok(maybe_cancel(cancel, self.stdout.next_line())
            .await??
            .unwrap()
            == "sat")
    }
    async fn get_unsat_core(&mut self, cancel: &CancellationToken) -> Result<String> {
        maybe_cancel(&cancel, self.stdin.write("(get-unsat-core)\n".as_bytes())).await??;
        self.stdin.flush().await?;
        Ok(maybe_cancel(cancel, self.stdout.next_line())
            .await??
            .unwrap())
    }
    async fn push(&mut self, cmd: String) -> Result<()> {
        self.stdin.write(cmd.as_bytes()).await?;
        self.stdin.flush().await?;
        Ok(())
    }
}

pub async fn run_z3(
    root: &RootGraph,
    comp: &Component,
    sema: Arc<Context>,
    cancel: CancellationToken,
) -> Result<()> {
    if !comp.dirty || comp.error != ComponentErrorState::Valid {
        Err("dirty or syntax errors")?
    }
    //info!("SMT check {:#?}", comp);
    let ctx = Binding {
        members: &comp.members,
        root,
        index: comp
            .members
            .iter()
            .enumerate()
            .map(|(i, f)| (*f, i as u16))
            .collect(),
    };
    let source = maybe_cancel(&cancel, smtlib_model(&ctx))
        .await?
        .ok_or("model generation failure")?;
    info!("{}",source);
    let mut model = SmtModel::new(source, &cancel).await?;
    if !model.check_sat(&cancel).await? {
        let core = model.get_unsat_core(&cancel).await?;
        sema.publish_err(parse_core(&ctx, core), root).await;
    } else {
        let mut err = HashMap::new();
        for m in ctx.members.iter() {
            let file = root.file(*m);
            for f in file.all_features() {
                model
                    .push(format!("(push 1)(assert {})\n", ctx.bind(f, *m).unwrap()))
                    .await?;
                if !model.check_sat(&cancel).await? {
                    insert_multi(
                        &mut err,
                        *m,
                        ErrorInfo {
                            location: file.lsp_range(f).unwrap(),
                            severity: DiagnosticSeverity::WARNING,
                            weight: 20,
                            msg: "dead feature".into(),
                        },
                    );
                }
                else{
                    info!("sat {:?}",f);
                }
                model.push(format!("(pop 1)\n")).await?;
            }
        }
        sema.publish_err(err, root).await;
    }
    Ok(())
}

pub fn can_run_z3() -> bool {
    Command::new("z3").spawn().is_ok()
}
lazy_static! {
    static ref HAS_Z3: bool = can_run_z3();
}
pub async fn check_smt(ctx: Arc<Context>, cancel: CancellationToken) {
    if *HAS_Z3 {
        info!("start smt");
        let root = ctx.root.read().await;
        let _results =
            maybe_cancel(
                &cancel,
                join_all(root.components().iter().map(|c| async {
                    if let Err(e) = run_z3(&root, c, ctx.clone(), cancel.clone()).await {
                        info!("failed to run z3 {}",e);

                    }
                })),
            )
            .await;
    }
}
