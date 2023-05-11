use crate::{
    core::*,
    ide::inlays::{InlayHandler, InlaySource},
    webview,
};
use futures::future::join_all;
use hashbrown::{HashMap, HashSet};

use lazy_static::lazy_static;
use log::info;

use std::fmt::Write;
use std::sync::Arc;
use tokio::{
    io::Lines,
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
mod parse;
pub mod smt_lib;
pub use smt_lib::*;

//SMT semantic analysis with Z3, communication with the solver happens over stdio and SMT-LIB2.
//While the performance is worse than linking with Z3, we are solver independent and don't have to interact
//with any C-Bindings. UVL is translated directly into SMT-LIB, both attributes and features are treated as
//free variables. The rest is encoded in named asserts, this allows to get a accurate unsat core.
//Eg. each attribute is restricted with an assert that allows it to either be its defined value or 0 depending
//on the parent feature value.
//Using functions might be more efficient, but this way we can reconfigure and detect if
//an attribute value contributes to the unsat core.
//Variables are named as v{n} where n is an index into a lookup table of UVL ModuleSymbols
//Asserts are encoded similarly as a{n} where n is and index into a list of naming information
//that links uvl expression to asserts.
pub struct SmtSolver {
    _proc: Child,
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
            _proc: proc,
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

    #[allow(dead_code)]
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
    pub module: Arc<Module>,
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
    cancel: CancellationToken,
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
            for (s, v) in module.parse_values(&values, base_module) {
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
        }
        solve.push("(pop 1)".into()).await?;
    }
    //check if a constraint is a tautologie

    // load in the module all variable and all constraints as Asserts
    let smt_module_constraint = uvl2smt_constraints(&base_module);
    // create source for smtsolver, but only with the variable
    let mut source_variable = smt_module_constraint.config_to_source();
    let _ = writeln!(
        source_variable,
        "{}",
        smt_module_constraint.variable_to_source(&base_module)
    );
    //create SMTSolver for the constraints
    let mut solver_constraint = SmtSolver::new(source_variable, &cancel).await?;
    for (i, Assert(info, expr)) in smt_module_constraint.asserts.iter().enumerate() {
        //get the negated constraint source
        let constraint_assert = smt_module_constraint.assert_to_source(i, info, expr, true);
        //push negated constraint
        solver_constraint
            .push(format!("(push 1) {}", constraint_assert))
            .await?;
        //check if negated constraint is unsat
        let sat = solver_constraint.check_sat().await?;
        if !sat {
            let module_symbol = info.clone().unwrap().0;
            state.insert(module_symbol, SMTValueState::On);
        }
        //pop negated constraint
        solver_constraint.push("(pop 1)".into()).await?;
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
    let time = Instant::now();
    let mut solver = SmtSolver::new(source, &cancel).await?;
    info!("create model: {:?}", time.elapsed());
    if solver.check_sat().await? {
        let values = if value | fixed {
            let query = module
                .variables
                .iter()
                .enumerate()
                .fold(String::new(), |acc, (i, _)| format!("{acc} v{i}"));

            let values = solver.values(query).await?;

            let time = Instant::now();
            let values = module.parse_values(&values, base_module).collect();
            info!("parse values: {:?}", time.elapsed());
            values
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
                    cancel,
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
    let models = join_all(active.map(|(_, v)| {
        let module = v.clone();
        async move {
            let smt_module = uvl2smt(&module, &HashMap::new());
            let source = smt_module.to_source(&module);
            let model = create_model(
                &module,
                root.cancellation_token(),
                smt_module,
                source,
                true,
                false,
            )
            .await;
            model.map(|m| (m, module))
        }
    }))
    .await;

    let mut e = ErrorsAcc::new(root);
    for k in models.into_iter() {
        match k {
            Ok((SMTModel::SAT { fixed, .. }, module)) => {
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
                        Symbol::Constraint(..) => {
                            if let Some(val) = fixed.get(&m.sym(sym)) {
                                match val {
                                    SMTValueState::On => {
                                        if visited.insert((sym, file.id)) {
                                            e.sym_info(sym, file.id, 10, "TAUT: constraint");
                                        }
                                        false
                                    }
                                    _ => true,
                                }
                            } else {
                                true
                            }
                        }
                        _ => false,
                    })
                }
            }
            Ok((SMTModel::UNSAT { reasons }, module)) => {
                let mut visited = HashSet::new();
                let mut void_is_marked = false;
                for r in reasons {
                    let file = module.file(r.0.instance).id;
                    if !void_is_marked {
                        // works only if keyword feature is the only keyword stored in the Keyword vector in the AST, but since I see no reason 
                        // why another keyword is needed in the green tree, so the features keyword would always have id 0.
                        e.sym(Symbol::Keyword(0), file, 12, "void feature model");
                        void_is_marked = true;
                    }
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
    //Reset inlays
    for (k, v) in latest_revisions.iter() {
        if root
            .cache()
            .config_modules
            .get(k)
            .map(|old| old.module.timestamp != *v)
            .unwrap_or(true)
        {
            info!("Reset {k:?}");
            inlay_state.maybe_reset(InlaySource::File(*k)).await;
        }
    }
    let active = root.cache().config_modules.iter().filter(|(k, v)| {
        latest_revisions
            .get(*k)
            .map(|old| old != &v.module.timestamp)
            .unwrap_or(true)
            && v.module.ok
            && k.is_config()
    });
    let models = join_all(active.map(|(k, v)| {
        let k = k.clone();
        let module = v.clone();
        async move {
            info!("checking {k:?}");
            let smt_module = uvl2smt(&module, &module.values);
            let source = smt_module.to_source(&module);
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
            if let Ok(model) = model.as_ref() {
                inlay_state
                    .maybe_publish(InlaySource::File(k), Instant::now(), || {
                        Arc::new(OwnedSMTModel {
                            model: model.clone(),
                            module: module.module.clone(),
                        })
                    })
                    .await;
            } else {
                inlay_state.maybe_reset(InlaySource::File(k)).await;
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
                            root_file,
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
        .config_modules
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
                    message: "UVLS: Z3 was not found on you're system. It is required for semantic analysis".into(),
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
        let (module, cancel, tag, config_ok) = {
            let lock = state.borrow_and_update();
            (lock.module.clone(), lock.cancel.clone(), lock.tag, lock.ok)
        };
        tx_ui.send(webview::UIAction::SolverActive).await?;

        if module.ok && config_ok {
            let smt_module = uvl2smt(&module, &module.values);
            let source = smt_module.to_source(&module);
            let res = create_model(&module, cancel, smt_module, source, false, true).await;
            match res {
                Ok(model) => {
                    inlay_state
                        .maybe_publish(inlay_source, Instant::now(), || {
                            Arc::new(OwnedSMTModel {
                                model: model.clone(),
                                module: module.module.clone(),
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
