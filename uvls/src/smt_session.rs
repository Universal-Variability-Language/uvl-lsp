use crate::ast::*;
use crate::cache::ModelState;
use crate::semantic::*;
use crate::smt::*;
use crate::util::{retry, Result};
use hashbrown::{HashMap, HashSet};
use serde::{Deserialize, Serialize};
use std::collections::VecDeque;
use std::error;
use std::sync::Arc;
use tokio::{
    select, spawn,
    sync::{mpsc, oneshot},
};
use tower_lsp::lsp_types::*;
use ustr::Ustr;
#[derive(Serialize, Debug)]
#[serde(untagged)]
pub enum ItemKind {
    Attribute,
    FeatureCard,
    FeatureBool,
}
#[derive(Serialize, Debug)]
pub struct Item {
    pub name: Ustr,
    pub value: f64,
    pub unsat: bool,
    pub kind: ItemKind,
    pub children: Vec<Item>,
}
#[derive(Serialize, Debug)]
pub struct FileState {
    pub items: Vec<Item>,
    pub uri: Url,
}

#[derive(Serialize, Debug, Default)]
pub struct State {
    pub files: Vec<FileState>,
    pub msg: String,
}
#[derive(Serialize, Debug, Default)]
pub struct Response {
    pub state: State,
    pub timestamp: String,
}

#[derive(Deserialize, Debug, Clone)]
pub struct FileConfig {
    selections: Vec<(String, f64)>,
}
#[derive(Deserialize, Debug, Clone)]
pub struct Config {
    files: Vec<(Url, FileConfig)>,
    base_file: Url,
    timestamp: String,
}
#[derive(Debug)]
pub enum Message {
    Update(Config, oneshot::Sender<Response>, Option<String>),
    Close(String),
}

pub fn config_to_sym(
    conf: Config,
    ctx: &Binding,
) -> Result<(HashMap<RootSymbol, bool>, HashMap<RootSymbol, f64>)> {
    let mut features = HashMap::new();
    let mut attribs = HashMap::new();
    for (uri, conf) in conf.files.iter() {
        if let Some(file) = ctx.root().file_by_uri(uri) {
            let file_id = ctx.root().file_id(uri).unwrap();
            for (path_str, val) in conf.selections.iter() {
                let path: Vec<_> = path_str.split(".").map(|i| Ustr::from(i)).collect();
                if let Some(sym) = file
                    .lookup(Symbol::Root, &path, |sym| {
                        matches!(
                            sym,
                            Symbol::Root | Symbol::Feature(..) | Symbol::Attribute(..)
                        )
                    })
                    .next()
                {
                    match sym {
                        Symbol::Feature(..) => {
                            features.insert(RootSymbol { file: file_id, sym }, *val == 1.0);
                        }
                        Symbol::Attribute(..) => {
                            attribs.insert(RootSymbol { file: file_id, sym }, *val);
                        }
                        _ => Err(format!(
                            "bad config missmatched value for {} in {}",
                            path_str,
                            file.uri.path()
                        ))?,
                    }
                } else {
                    Err(format!(
                        "bad config unresolved path {} in {}",
                        path_str,
                        file.uri.path()
                    ))?
                };
            }
        }
    }
    Ok((features, attribs))
}

struct StateBuildContext<'a> {
    bind: &'a Binding<'a>,
    model: Option<&'a mut SmtModel>,
    unsat_reason: HashSet<RootSymbol>,
    known_values: HashMap<RootSymbol, i8>,
}

async fn compute_feature_value(
    ctx: &mut StateBuildContext<'_>,
    root: RootSymbol,
) -> Result<f64> {
    if let Some(&mut ref mut model) = ctx.model {
        match ctx.known_values.get(&root) {
            Some(1) => {
                model
                    .push(format!(
                        "(push 1) (assert (not {}))",
                        ctx.bind.bind(root.sym, root.file).unwrap()
                    ))
                    .await?;
                let val = if model.check_sat().await? {
                    for (i, v) in ctx.bind.parse_model(&model.instance().await?) {
                        expand(&mut ctx.known_values, i, v);
                    }
                    -1.0
                } else {
                    1.0
                };
                model.push("(pop 1)".into()).await?;
                Ok(val)
            }
            Some(0) => {
                model
                    .push(format!(
                        "(push 1) (assert {})",
                        ctx.bind.bind(root.sym, root.file).unwrap()
                    ))
                    .await?;
                let val = if model.check_sat().await? {
                    for (i, v) in ctx.bind.parse_model(&model.instance().await?) {
                        expand(&mut ctx.known_values, i, v);
                    }
                    -1.0
                } else {
                    0.0
                };
                model.push("(pop 1)".into()).await?;
                Ok(val)
            }
            _ => Ok(-1.0),
        }
    } else {
        Ok(-1.0)
    }
}

async fn compute_value_info(
    ctx: &mut StateBuildContext<'_>,
    file: &AstDocument,
    file_id: FileID,
    sym: Symbol,
) -> Result<Option<(ItemKind, f64)>> {
    let root = RootSymbol { file: file_id, sym };
    match sym {
        Symbol::Feature(..) => {
            Ok(Some((ItemKind::FeatureBool,compute_feature_value(ctx,root).await?)))
        } 
        Symbol::Attribute(..) => {
            if let Some(Value::Number(n)) = file.value(sym) {
                Ok(Some((ItemKind::Attribute, *n)))
            } else {
                Ok(None)
            }
        }
        _ => Ok(None),
    }
}

async fn create_file_state(
    ctx: &mut StateBuildContext<'_>,
    file: &AstDocument,
    file_id: FileID,
) -> Result<FileState> {
    let mut filestate = FileState {
        uri: file.uri.clone(),
        items: Vec::new(),
    };
    let mut children: Vec<(u32, Item)> = Vec::new();
    let mut stack: VecDeque<_> = file
        .direct_children(Symbol::Root)
        .filter(|i| matches!(i, Symbol::Feature(..)))
        .map(|i| (0, i))
        .collect();
    while let Some((depth, sym)) = stack.pop_front() {
        for i in file.direct_children(sym) {
            stack.push_back((depth + 1, i));
        }
        match sym {
            Symbol::Feature(..) | Symbol::Attribute(..) => {
                if let Some((kind, value)) = compute_value_info(ctx, file, file_id, sym).await? {
                    let mut reduce = children.len();
                    while children[reduce - 1].0 > depth {
                        reduce += 1;
                    }
                    if reduce != children.len() {
                        let mut tail = children.split_off(reduce);
                        children.last_mut().unwrap().1.children =
                            tail.drain(..).map(|(i, k)| k).collect();
                    }

                    children.push((
                        depth,
                        Item {
                            name: file.name(sym).unwrap(),
                            unsat: ctx
                                .unsat_reason
                                .contains(&RootSymbol { sym, file: file_id }),
                            value,
                            kind,
                            children: Vec::new(),
                        },
                    ))
                }
            }
            _ => {}
        }
    }
    filestate.items = children.drain(..).map(|(_, k)| k).collect();
    Ok(filestate)
}

fn expand(bool_features: &mut HashMap<RootSymbol, i8>, sym: RootSymbol, v: bool) {
    if let Some(old) = bool_features.get_mut(&sym) {
        *old = match (*old, v) {
            (1, false) | (0, true) => -1,
            _ => *old,
        };
    } else {
        bool_features.insert(sym, if v { 1 } else { 0 });
    }
}
async fn create_state(
    ctx: &Binding<'_>,
    model: Option<&mut SmtModel>,
    conf_features: HashMap<RootSymbol, bool>,
    conf_attributes: HashMap<RootSymbol, f64>,
) -> Result<State> {
    let mut known_values = HashMap::new();
    let mut unsat_reason = HashSet::new();
    if let Some(&mut ref mut model) = model {
        model.push(format!("(pop 1)")).await?;
        model
            .push(format!(
                "(push 1){}{}",
                ctx.encode_config_attributes(&conf_attributes),
                ctx.encode_config_features(&conf_features)
            ))
            .await?;
        if model.check_sat().await? {
            for (i, v) in ctx.parse_model(&model.instance().await?) {
                expand(&mut known_values, i, v);
            }
        } else {
            for i in ctx.parse_core(&model.unsat_core().await?) {
                match i {
                    NamedRootSymbol::Setting(sym) => {
                        unsat_reason.insert(sym);
                    }
                    _ => {}
                }
            }
        }
    }
    let mut ctx = StateBuildContext {
        bind: ctx,
        model,
        known_values,
        unsat_reason,
    };
    let mut state = State::default();
    state.msg = if ctx.model.is_none() {
        "congfiguration basis model is unsat, please fix it first".into()
    } else if ctx.known_values.is_empty() {
        "congfiguration is unsat".into()
    } else {
        String::new()
    };
    for m in ctx.bind.members() {
        let file = ctx.bind.root().file(*m);
        state
            .files
            .push(create_file_state(&mut ctx, file, *m).await?);
    }

    if let Some(&mut ref mut model) = ctx.model {
        model.push("(pop 1)".into()).await?;
    }
    Ok(state)
}
struct SmtSession {
    revision: u64,
    model: Option<SmtModel>,
}
impl SmtSession {
    fn open() -> Self {
        Self {
            revision: u64::MAX,
            model: None,
        }
    }
    async fn update(&mut self, conf: Config, ctx: &Context) -> Result<State> {
        let root = ctx
            .snapshot_sync(&conf.base_file, ctx.drafts.latest_timestamp(&conf.base_file).await.ok_or())
            .await
            .ok_or_else(|| "shutdown")?;
        let base_id = root.file_id(&conf.base_file).ok_or("internal error")?;
        if root
            .models()
            .iter()
            .find(|i| i.members.contains(&base_id))
            .unwrap()
            .state
            != ModelState::Valid
        {
            return Ok(State {
                files: Vec::new(),
                msg: "Invalid syntax please fix the congfiguration model first".into(),
            });
        }

        if self.revision != root.revision() || u64::MAX == self.revision{
            let members = root.fs().recursive_imports(base_id);
            let binding = Binding::new(&root, &members);
            let model_src = smtlib_model(&binding, false)
                .await
                .ok_or("failed to create model source")?;
            let mut model = SmtModel::new(model_src, &root.cancellation_token()).await?;
            let (features, attribs) = config_to_sym(conf, &binding)?;
            model
                .push(format!(
                    "(push 1){}",
                    binding.encode_config_attributes(&HashMap::new())
                ))
                .await?;
            let base_sat = model.check_sat().await?;

            if base_sat {
                self.model = Some(model);
            }
            else{
                self.model = None;
            }
            let state = create_state(&binding,self.model.as_mut(),features,attribs).await?;
            self.revision = root.revision();
            Ok(state)
        } else {
            let members = root.fs().recursive_imports(base_id);
            let binding = Binding::new(&root, &members);
            let (features, attribs) = config_to_sym(conf, &binding)?;
            let state = create_state(&binding,self.model.as_mut(),features,attribs).await?;
            Ok(state)
        }
    }
}

async fn session_loop(
    mut rx: mpsc::Receiver<Message>,
    ctx: Arc<Context>,
    id: String,
    session:SmtSession
) {
    loop {
        let msg = select! {
            _=ctx.shutdown.cancelled()=>break,
            Some(msg) = rx.recv()=>msg,
            else => break
        };
        match msg {
            Message::Update(conf, res, ..) => {}
            Message::Close(..) => {}
        }
    }
}

async fn session(
    rx: mpsc::Receiver<Message>,
    ctx: Arc<Context>,
    id: String,
    initial_conf: Config,
    initial_res: oneshot::Sender<Response>,
) {
    let mut session =  SmtSession::open();
    session_loop(rx, ctx, id,session).await;
}
pub async fn handler(mut rx: mpsc::Receiver<Message>, ctx: Arc<Context>) {
    let mut sessions = HashMap::new();
    let mut counter: u64 = 0;
    loop {
        let msg = select! {
            _=ctx.shutdown.cancelled()=>break,
            Some(msg) = rx.recv()=>msg,
            else => break
        };
        match msg {
            Message::Update(conf, res, None) => {
                let (tx, rx) = mpsc::channel(32);
                let session_id = format!("s{counter}");
                counter += 1;
                sessions.insert(session_id.clone(), tx);
                let _ = spawn(session(rx, ctx.clone(), session_id, conf, res));
            }
            Message::Update(conf, res, Some(id)) => {
                if let Some(tx) = sessions.get(&id) {
                    let _ = tx.send(Message::Update(conf, res, Some(id))).await;
                } else {
                    let _ = res.send(Response {
                        timestamp: conf.timestamp,
                        state: State {
                            msg: "Error: Invalid session".into(),
                            ..Default::default()
                        },
                    });
                }
            }
            Message::Close(id) => {
                if let Some(tx) = sessions.get(&id) {
                    let _ = tx.send(Message::Close(id)).await;
                }
            }
        }
    }
}
