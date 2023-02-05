use crate::{
    ast::*,
    check::ErrorInfo,
    semantic::{FileID, RootSymbol, Snapshot},
};
use futures::future::join_all;
use hashbrown::HashMap;
use log::info;
use std::fmt::{Display, Write};
use tokio::io::{AsyncReadExt, AsyncWriteExt, BufReader};
use tokio::process::Command;
use writeln as write_smt;
struct Bind {
    file: u16,
    sym: Symbol,
}

impl Display for Bind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.sym {
            Symbol::Feature(..) => write!(f, "f{}_{}", self.file, self.sym.offset()),
            Symbol::Group(..) => write!(f, "g{}_{}", self.file, self.sym.offset()),
            Symbol::Attribute(..) => write!(f, "a{}_{}", self.file, self.sym.offset()),
            Symbol::Constraint(..) => write!(f, "c{}_{}", self.file, self.sym.offset()),
            _ => unimplemented!(),
        }
    }
}
struct Component<'a> {
    root: &'a Snapshot,
    index: HashMap<FileID, u16>,
    members: &'a [FileID],
}
impl<'a> Component<'a> {
    fn bind(&self, sym: Symbol, file_id: FileID) -> Option<Bind> {
        let tgt = self.root.resolve_sym(RootSymbol { file: file_id, sym })?;
        Some(Bind {
            file: self.index[&tgt.file],
            sym: tgt.sym,
        })
    }
}

fn declare_features(ctx: &Component, file_id: FileID) -> String {
    let mut out = String::new();
    for i in ctx.root.file(file_id).all_features() {
        info!("{:?}", i);
        let _ = write_smt!(
            out,
            "(declare-const {} Bool)",
            ctx.bind(i, file_id).unwrap()
        );
    }
    out
}
fn declare_attributes(ctx: &Component, file_id: FileID) -> String {
    let mut out = String::new();
    let file = ctx.root.file(file_id);
    for i in file.all_features() {
        file.visit_children(i, true, |sym| match file.value(i) {
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
fn gather_clause(ctx: &Component, file: &Document, file_id: FileID, g: Symbol) -> Option<String> {
    let mut clause = String::new();
    for c in file.direct_children(g) {
        let _ = write!(clause, " {}", ctx.bind(c, file_id)?);
    }
    Some(clause)
}
fn declare_groups(ctx: &Component, file_id: FileID) -> Option<String> {
    let mut out = String::new();
    let file = &ctx.root.file(file_id);
    if file.errors.len() > 0 {
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
            match file.group_mode(g)? {
                GroupMode::Or => {
                    let clause = gather_clause(ctx, file, file_id, g);
                    let _ = write_smt!(out, "(assert (= {} (or {})))", p_bind, clause?);
                }
                GroupMode::Alternative => {
                    let clause = gather_clause(ctx, file, file_id, g);
                    let _ = write_smt!(out, "(assert (=> {} ((_ at-most 1) {})))", p_bind, clause?);
                }
                GroupMode::Mandatory => {
                    for c in file.direct_children(g) {
                        let _ =
                            write_smt!(out, "(assert (= {} {}))", p_bind, ctx.bind(c, file_id)?);
                    }
                }
                GroupMode::Optional | GroupMode::Cardinality(Cardinality::Any) => {
                    for c in file.direct_children(g) {
                        let _ =
                            write_smt!(out, "(assert (=> {} {}))", p_bind, ctx.bind(c, file_id)?);
                    }
                }
                GroupMode::Cardinality(Cardinality::Max(max)) => {
                    let clause = gather_clause(ctx, file, file_id, g);
                    let _ = write_smt!(
                        out,
                        "(assert (=> {} ((_ at-most {}) {})))",
                        p_bind,
                        max,
                        clause?
                    );
                }

                GroupMode::Cardinality(Cardinality::From(min)) => {
                    let clause = gather_clause(ctx, file, file_id, g);
                    let _ = write_smt!(
                        out,
                        "(assert (=> {} ((_ at-atleast {}) {})))",
                        p_bind,
                        min,
                        clause?
                    );
                }
                GroupMode::Cardinality(Cardinality::Range(min, max)) => {
                    let clause = gather_clause(ctx, file, file_id, g)?;
                    let _ = write_smt!(
                        out,
                        "(assert (=> {} ((_ at-most {}) {})))",
                        p_bind,
                        max,
                        clause
                    );
                    let _ = write_smt!(
                        out,
                        "(assert (=> {} ((_ at-least {}) {})))",
                        p_bind,
                        min,
                        clause
                    );
                }
            }
        }
    }
    Some(out)
}
fn encode_numeric(ctx: &Component, file_id: FileID, expr: &Numeric) -> Option<String> {
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
                encode_numeric(ctx, file_id, lhs)?,
                encode_numeric(ctx, file_id, rhs)?
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
fn encode_constraint(ctx: &Component, file_id: FileID, constraint: &Constraint) -> Option<String> {
    match constraint {
        Constraint::Constant(val) => Some(format!("{}", val)),
        Constraint::Ref(id) => Some(format!("{}", ctx.bind(*id, file_id)?)),
        Constraint::Not(lhs) => Some(format!("(not {})", encode_constraint(ctx, file_id, &lhs)?)),
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
                encode_constraint(ctx, file_id, lhs)?,
                encode_constraint(ctx, file_id, rhs)?
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
                encode_numeric(ctx, file_id, lhs)?,
                encode_numeric(ctx, file_id, rhs)?
            ))
        }
    }
}
fn encode_constraints(ctx: &Component, file_id: FileID) -> Option<String> {
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

fn smtlib_model(ctx: &Component) -> Option<String> {
    let mut out = "(set-option :produce-unsat-cores true)(define-fun smooth_div ((x Real) (y Real)) Real(if (not (= y 0.0))(/ x y)0.0))\n".to_string();
    let _ = write_smt!(
        out,
        "{}",
        ctx.members
            .iter()
            .map(|f| declare_features(&ctx, *f))
            .collect::<String>()
    );
    let _ = write_smt!(
        out,
        "{}",
        ctx.members
            .iter()
            .map(|f| declare_attributes(&ctx, *f))
            .collect::<String>()
    );
    for file in ctx.members.iter() {
        let _ = write_smt!(out, "{}", declare_groups(&ctx, *file)?);
    }
    for file in ctx.members.iter() {
        let _ = write_smt!(out, "{}", encode_constraints(&ctx, *file)?);
    }
    let _ = write_smt!(out, "{}", "(check_sat)");
    Some(out)
}
pub async fn run_z3(root: Snapshot, members: Vec<FileID>) -> Option<Vec<ErrorInfo>> {
    let ctx = Component {
        members: &members,
        root: &root,
        index: members
            .iter()
            .enumerate()
            .map(|(i, f)| (*f, i as u16))
            .collect(),
    };
    let model = smtlib_model(&ctx)?;
    let mut cmd = Command::new("z3")
        .arg("-in")
        .arg("-smt2")
        .stdin(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .kill_on_drop(true)
        .spawn()
        .ok()?;
    let mut stdin = cmd.stdin.take()?;
    let mut stdout = BufReader::new(cmd.stdout.take()?);
    let mut stderr = BufReader::new(cmd.stderr.take()?);
    let _ =stdin.write(model.as_bytes()).await.ok()?;
    let mut result = String::new();
    stdout.read_to_string(&mut result).await.ok()?;
    if result == "unsat" {
        let _ = stdin.write("(get-unsat-core)".as_bytes()).await.ok()?;
        result.clear();
        stdout.read_to_string(&mut result).await.ok()?;
        info!("unsat core {}", result);
    }
    None
}

pub async fn check_smt(root: Snapshot) {
    let mut components = root.connected_components();
    let results = join_all(components.drain(..).map(|c| run_z3(root.clone(), c))).await;
}
