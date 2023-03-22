use crate::{ast::*, config::*, pipeline::AsyncPipeline, semantic::*, smt, util::Result};
use axum::{
    extract::{ws::WebSocketUpgrade, Path},
    response::Html,
    routing::get,
    Router,
};
use dioxus::prelude::*;
use futures_util::StreamExt;
use hashbrown::{HashMap, HashSet};
use indexmap::IndexMap;
use itertools::Itertools;
use log::info;
use serde::Serialize;
use std::sync::Arc;
use std::{collections::BTreeMap, sync::atomic::AtomicU64};
use tokio_util::sync::CancellationToken;

use tokio::{
    select, spawn,
    sync::{mpsc, watch},
    time::Instant,
};
use ustr::Ustr;

#[derive(PartialEq, Clone, Copy, Debug)]
pub enum Icon {
    File,
    Feature,
    Attributes,
    Atribute,
    Expand,
    Collapse,
    Circle,
    CircleCross,
    CircleCheck,
    CirclePlus,
}
#[derive(Clone, Debug)]
pub enum SatState {
    UNKNOWN,
    SAT,
    UNSAT,
    ERR(String),
}

#[derive(Debug, Clone, PartialEq)]
pub enum UIEntryValue {
    Attributes,
    Feature {
        config: Option<ConfigValue>,
        smt_value: Option<ConfigValue>,
        ty: Type,
        unsat: bool,
    },
    Attribute {
        config: Option<ConfigValue>,
        default: ConfigValue,
        unsat: bool,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct UIEntry {
    pub depth: u32,
    pub prefix: Vec<Ustr>,
    pub value: UIEntryValue,
    pub open: bool,
}
impl UIEntry {
    fn update_smt(&mut self, val: Option<ConfigValue>) {
        match &mut self.value {
            UIEntryValue::Feature { smt_value, .. } => {
                *smt_value = val;
            }
            _ => {}
        }
    }
    fn should_open(&self) -> bool {
        match &self.value {
            UIEntryValue::Feature { config, .. } | UIEntryValue::Attribute { config, .. } => {
                config.is_some()
            }
            _ => false,
        }
    }
    fn update_config(&mut self, val: Option<ConfigValue>) {
        match &mut self.value {
            UIEntryValue::Feature { config, .. } | UIEntryValue::Attribute { config, .. } => {
                *config = val;
            }
            _ => {}
        }
    }
    fn unsat(&mut self, arg: bool) {
        match &mut self.value {
            UIEntryValue::Feature { unsat, .. } | UIEntryValue::Attribute { unsat, .. } => {
                *unsat = arg;
            }
            _ => {}
        }
    }
}
#[derive(Debug, Clone)]
pub struct UIFileNode {
    pub uri: FileID,
    pub name: String,
    pub entries: IndexMap<Symbol, UIEntry>,
    pub open: bool,
}
impl UIFileNode {
    fn unfold(&mut self) {
        let mut is_open = HashSet::new();
        for i in self.entries.values_mut().rev() {
            i.open = is_open.remove(&(i.depth)) || i.should_open();
            if i.open {
                is_open.insert(i.depth - 1);
            }
        }
        if is_open.get(&0).is_some() {
            self.open = true;
        }
    }
}
#[derive(Debug, Clone, Default)]
pub struct UIConfigState {
    pub files: IndexMap<FileID, UIFileNode>,
    pub revision: u64,
}
impl UIConfigState {
    fn unfold(&mut self) {
        for i in self.files.values_mut() {
            i.unfold();
        }
    }
}

#[derive(Debug, Clone)]
pub struct UIState {
    pub sat: SatState,
    pub sync: UISyncState,
    pub dir: String,
    pub file_name: String,
}

#[derive(Debug, Clone)]
pub enum UIAction {
    TreeDirty,
    ToggleValue(FileID, Symbol),
    ToggleFile(FileID),
    UpdateRoot(Arc<RootGraph>),
    UpdateSMTModel(smt::SMTModel, Instant),
    UpdateSMTInvalid(String, Instant),
    Set(FileID, Symbol, ConfigValue),
    Unset(FileID, Symbol),
    Save,
    Show,
}
#[derive(Debug, Clone)]
pub enum UISyncState {
    Dirty,
    InternalError(String),
    Valid,
}
#[derive(PartialEq, Clone)]
pub enum AppInitialParams {
    Create(String),
    Load(String),
    InvalidOP,
}
#[derive(Props)]
pub struct AppProps {
    pub pipeline: AsyncPipeline,
    pub initial: AppInitialParams,
    pub id: u64,
}
impl PartialEq for AppProps {
    fn eq(&self, other: &Self) -> bool {
        self.initial == other.initial
    }
}
fn create_file_tree(
    file: &AstDocument,
    config: Option<&HashMap<Vec<Ustr>, ConfigValue>>,
) -> UIFileNode {
    let mut values: IndexMap<Symbol, UIEntry> = IndexMap::new();
    let mut last = Symbol::Root;
    let mut vdir = 0;
    file.visit_named_children_depth(Symbol::Root, true, |sym, prefix, depth| match sym {
        Symbol::Feature(_) | Symbol::Attribute(_) => {
            match file.type_of(sym).unwrap() {
                Type::String | Type::Real | Type::Bool | Type::Attributes => {}
                _ => {
                    return true;
                }
            }
            if matches!((sym, last), (Symbol::Attribute(..), Symbol::Feature(..))) {
                values.insert(
                    Symbol::Dir(vdir),
                    UIEntry {
                        depth: depth as u32,
                        prefix: vec!["attributes".into()],

                        value: UIEntryValue::Attributes,
                        open: false,
                    },
                );
                vdir += 1;
            }
            let depth = if matches!(sym, Symbol::Attribute(..)) {
                depth + 1
            } else {
                depth
            };

            values.insert(
                sym,
                UIEntry {
                    prefix: prefix.to_vec(),
                    open: false,
                    depth: depth as u32,
                    value: match sym {
                        Symbol::Feature(..) => UIEntryValue::Feature {
                            config: config.and_then(|config| config.get(prefix).cloned()),
                            unsat: false,
                            smt_value: None,
                            ty: file.type_of(sym).unwrap(),
                        },
                        Symbol::Attribute(..) => match file.value(sym).unwrap() {
                            Value::Bool(num) => UIEntryValue::Attribute {
                                config: config.and_then(|config| config.get(prefix).cloned()),
                                unsat: false,
                                default: ConfigValue::Bool(*num),
                            },
                            Value::Number(num) => UIEntryValue::Attribute {
                                config: config.and_then(|config| config.get(prefix).cloned()),
                                unsat: false,
                                default: ConfigValue::Number(*num),
                            },
                            Value::String(s) => UIEntryValue::Attribute {
                                config: config.and_then(|config| config.get(prefix).cloned()),
                                unsat: false,
                                default: ConfigValue::String(s.clone()),
                            },
                            Value::Attributes => UIEntryValue::Attributes,
                            _ => unimplemented!(),
                        },
                        _ => unimplemented!(),
                    },
                },
            );
            last = sym;
            true
        }
        _ => false,
    });
    UIFileNode {
        uri: file.id,
        name: file.path[file.path.len() - 1].as_str().into(),
        open: true,
        entries: values,
    }
}

fn rebuild_tree(root: &RootGraph, config: &DirectConfig) -> Option<UIConfigState> {
    let mut members = HashSet::new();
    for &i in config.keys() {
        if root.containes_id(i) {
            for i in root.fs().recursive_imports(i) {
                members.insert(i);
            }
        }
    }
    if members
        .iter()
        .any(|i| !root.cache().modules[root.cache().file2module[i]].ok)
    {
        return None;
    }
    let files = members
        .iter()
        .map(|&m| (m, create_file_tree(root.file(m), config.get(&m))))
        .collect();
    Some(UIConfigState {
        files,
        revision: root.revision(),
    })
}

async fn ui_sync(
    id: u64,
    pipeline: AsyncPipeline,
    tx_sync: mpsc::Sender<UIAction>,
    mut rx_config: watch::Receiver<DirectConfig>,
) -> Result<()> {
    let mut dirty = pipeline.subscribe_dirty_tree();
    let mut root = {
        let root = pipeline.sync_root_global().await?;
        tx_sync.send(UIAction::UpdateRoot(root.clone())).await?;
        root
    };
    let mut cancel = CancellationToken::new();
    loop {
        select! {
            _=dirty.recv()=>{
                info!("dirty");
                tx_sync.send(UIAction::TreeDirty).await?;
                let new_root =pipeline.sync_root_global().await?;
                tx_sync.send(UIAction::UpdateRoot(root.clone())).await?;
                root = new_root;
                cancel.cancel();
                cancel = CancellationToken::new();
                spawn(smt::create_config_model(Instant::now(),root.clone(),cancel.clone(),
                    rx_config.borrow_and_update().clone(),
                    tx_sync.clone(),pipeline.inlay_state().clone(),id));


            },
            Ok(_) = rx_config.changed()=>{
                cancel.cancel();
                cancel = CancellationToken::new();
                spawn(smt::create_config_model(Instant::now(),root.clone(),cancel.clone(),
                    rx_config.borrow_and_update().clone(),
                    tx_sync.clone(),pipeline.inlay_state().clone(),id));
            },
            else =>{
                break;
            }
        }
    }
    Ok(())
}
fn purge_state(root: &RootGraph, config: &mut DirectConfig) {
    config.retain(|k, _| root.containes_id(*k));
    for (k, v) in config.iter_mut() {
        let file = root.file(*k);
        v.retain(|k, _| {
            file.lookup(Symbol::Root, k.as_slice(), |_| true)
                .find(|sym| matches!(sym, Symbol::Attribute(..) | Symbol::Feature(..)))
                .is_some()
        });
    }
}
fn save_config(config: &DirectConfig, dir: String, file_name: String, root: &RootGraph) {
    #[derive(Serialize)]
    struct RawFileConfig {
        file: String,
        config: BTreeMap<String, ConfigValue>,
    }
    let files: Vec<_> = config
        .iter()
        .filter(|(k, _)| root.containes_id(**k))
        .filter_map(|(id, values)| {
            let file_path = &root.file(*id).path;

            let dir_path = dir.split("/").skip(1);
            let common = dir_path
                .zip(file_path.iter())
                .take_while(|(i, k)| *i == k.as_str())
                .count();
            let path = file_path[common..].iter().map(|i| i.as_str()).join(".");
            Some(RawFileConfig {
                file: path,
                config: values
                    .iter()
                    .map(|(k, v)| (k.iter().join("."), v.clone()))
                    .collect(),
            })
        })
        .collect();
    let json = serde_json::to_string(&files).unwrap();
    tokio::task::spawn_blocking(move || {
        let path = if dir.is_empty() {
            format!("{dir}/{file_name}")
        } else {
            file_name.clone()
        };
        let _ = std::fs::write(&path, json);
    });
}

async fn ui_event_loop(
    id: u64,
    tx_config: watch::Sender<DirectConfig>,
    mut rx_ui: UnboundedReceiver<UIAction>,
    mut rx_sync: mpsc::Receiver<UIAction>,
    ui_config: &UseRef<UIConfigState>,
    ui_state: &UseRef<UIState>,
    pipeline: &AsyncPipeline,
) {
    let mut latest_model = Instant::now();
    loop {
        let e = select! {Some(e)=rx_ui.next()=>e,Some(e)=rx_sync.recv()=>e, else=>{break;}};

        match e {
            UIAction::TreeDirty => {
                ui_state.with_mut(|state| {
                    state.sync = UISyncState::Dirty;
                });
            }
            UIAction::UpdateRoot(root) => {
                tx_config.send_modify(|state| purge_state(&root, state));
                ui_config.with_mut(|x| {
                    if let Some(tree) = rebuild_tree(&root, &tx_config.borrow()) {
                        *x = tree;
                        ui_state.with_mut(|state| {
                            state.sync = UISyncState::Valid;
                        });
                        x.unfold();
                    } else {
                        ui_state.with_mut(|state| {
                            state.sync = UISyncState::InternalError("sources invalid".into());
                        });
                    }
                });
            }
            UIAction::ToggleValue(file, index) => {
                ui_config.with_mut(|UIConfigState { files, .. }| {
                    if let Some(v) = files
                        .get_mut(&file)
                        .and_then(|file| file.entries.get_mut(&index))
                    {
                        v.open = !v.open;
                    }
                });
            }
            UIAction::ToggleFile(file) => {
                ui_config.with_mut(|UIConfigState { files, .. }| {
                    if let Some(file) = files.get_mut(&file) {
                        info!("set!");
                        file.open = !file.open;
                    }
                });
            }
            UIAction::Set(file, sym, val) => {
                if matches!(ui_state.read().sync, UISyncState::Dirty) {
                    return;
                }
                if let Some(prefix) = ui_config.with_mut(|UIConfigState { files, .. }| {
                    if let Some(node) = files.get_mut(&file).and_then(|e| e.entries.get_mut(&sym)) {
                        node.update_config(Some(val.clone()));
                        Some(node.prefix.clone())
                    } else {
                        None
                    }
                }) {
                    tx_config.send_modify(|config| {
                        if !config.contains_key(&file) {
                            config.insert(file, HashMap::new());
                        }
                        if let Some(cnode) = config.get_mut(&file) {
                            cnode.insert(prefix, val.clone());
                        }
                    });
                }
            }
            UIAction::Save => {
                let state = ui_state.read();
                save_config(
                    &tx_config.borrow(),
                    state.dir.clone(),
                    state.file_name.clone(),
                    &pipeline.root().borrow(),
                );
            }
            UIAction::Show => {
                pipeline
                    .inlay_state()
                    .set_source(crate::inlays::InlaySource::Web(id))
                    .await;
                tx_config.send_modify(|_| {});
            }
            UIAction::Unset(file, sym) => {
                if let Some(prefix) = ui_config.with_mut(|UIConfigState { files, .. }| {
                    if let Some(node) = files.get_mut(&file).and_then(|e| e.entries.get_mut(&sym)) {
                        node.update_config(None);
                        Some(node.prefix.clone())
                    } else {
                        None
                    }
                }) {
                    tx_config.send_modify(|config| {
                        if !config.contains_key(&file) {
                            config.insert(file, HashMap::new());
                        }
                        if let Some(cnode) = config.get_mut(&file) {
                            cnode.remove(&prefix);
                        }
                    });
                }
            }
            UIAction::UpdateSMTInvalid(msg, timestamp) => {
                if latest_model > timestamp {
                    continue;
                }
                latest_model = timestamp;
                info!("SMT invalid");
                ui_state.with_mut(|state| {
                    state.sat = SatState::ERR(msg);
                });
            }
            UIAction::UpdateSMTModel(model, timestamp) => {
                if latest_model > timestamp {
                    continue;
                }
                latest_model = timestamp;
                ui_config.with_mut(|UIConfigState { files, .. }| match model {
                    smt::SMTModel::SAT { values, .. } => {
                        ui_state.with_mut(|state| state.sat = SatState::SAT);
                        for (k, v) in values {
                            if let Some(file) = files.get_mut(&k.file) {
                                if let Some(entry) = file.entries.get_mut(&k.sym) {
                                    entry.update_smt(Some(v));
                                    entry.unsat(false);
                                }
                            }
                        }
                        for i in files.values_mut() {
                            i.unfold();
                        }
                    }
                    smt::SMTModel::UNSAT { reasons } => {
                        ui_state.with_mut(|state| {
                            state.sat = SatState::UNSAT;
                        });
                        for i in files.values_mut().flat_map(|i| i.entries.values_mut()) {
                            i.update_smt(None);
                            i.unsat(false);
                        }
                        for i in reasons {
                            match i {
                                smt::SmtName::Config(k) | smt::SmtName::Attribute(k) => {
                                    if let Some(file) = files.get_mut(&k.file) {
                                        if let Some(entry) = file.entries.get_mut(&k.sym) {
                                            entry.unsat(true);
                                        }
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                });
            }
        }
    }
    info!("exit event");
}

pub async fn ui_main(
    id: u64,
    pipeline: AsyncPipeline,
    ui_state: UseRef<UIState>,
    ui_config: UseRef<UIConfigState>,
    ui_rx: UnboundedReceiver<UIAction>,
    initial: AppInitialParams,
) -> Result<()> {
    let (initial_config, dest) = match initial {
        AppInitialParams::Create(path) => {
            let root = pipeline.sync_root_global().await?;
            let id = FileID::new(format!("file:///{path}").as_str());

            let mut c = HashMap::new();
            if root.containes_id(id) {
                c.insert(id, HashMap::new());
                for i in root.fs().recursive_imports(id) {
                    c.insert(i, HashMap::new());
                }
                let mut dest = id.url().unwrap().to_file_path().unwrap();
                dest.set_extension("uvl.json");
                Ok((c, dest))
            } else {
                Err("source model not found")
            }
        }
        AppInitialParams::Load(path) => {
            let root = pipeline.sync_root_global().await?;
            let path = FileID::new(format!("file:///{path}").as_str());
            if let Some(src) = root.cache().config_modules.get(&path) {
                let mut dst = HashMap::new();
                for &m in src.members.iter() {
                    let file = root.file(m);
                    let mut file_dst = HashMap::new();
                    file.visit_named_children(Symbol::Root, true, |sym, prefix| match sym {
                        Symbol::Feature(..) => {
                            if let Some(c) = src.features.get(&RootSymbol { sym, file: m }) {
                                file_dst.insert(prefix.to_vec(), c.clone());
                            }
                            true
                        }
                        Symbol::Attribute(..) => {
                            if let Some(c) = src.attributes.get(&RootSymbol { sym, file: m }) {
                                file_dst.insert(prefix.to_vec(), c.clone());
                            }
                            true
                        }
                        _ => false,
                    });
                    dst.insert(m, file_dst);
                }
                Ok((dst, path.url().unwrap().to_file_path().unwrap()))
            } else {
                Err("confuguartion not found")
            }
        }
        AppInitialParams::InvalidOP => Err("invalid server operation"),
    }?;
    ui_state.with_mut(|state| {
        if let Some(p) = dest.parent() {
            state.dir = p.to_str().unwrap().to_string();
        }
        state.file_name = dest.file_name().unwrap().to_str().unwrap().to_string();
    });
    let (tx_sync, rx_sync) = mpsc::channel(32);
    let (tx_config, rx_config) = watch::channel(initial_config);
    spawn(ui_sync(id, pipeline.clone(), tx_sync, rx_config));
    ui_event_loop(
        id, tx_config, ui_rx, rx_sync, &ui_config, &ui_state, &pipeline,
    )
    .await;

    info!("exit main");
    Ok(())
}

pub async fn web_handler(pipeline: AsyncPipeline, port: u16) {
    info!("Starting web handler");
    let addr: std::net::SocketAddr = ([127, 0, 0, 1], port).into();
    let view = dioxus_liveview::LiveViewPool::new();
    let style = include_str!("style.css");

    let app = Router::new()
        // The root route contains the glue code to connect to the WebSocket
        .route(
            "/create/*path",
            get(move |Path(path): Path<String>| async move {
                Html(format!(
                    r#"
                <!DOCTYPE html>
                <html>
                <head> <title>UVL-Feature Config</title> 
                <style>
                    {style}
                </style>
                </head>
                <body> <div id="main"></div> </body>
                {glue}
                </html>
                "#,
                    // Create the glue code to connect to the WebSocket on the "/ws" route
                    glue =
                        dioxus_liveview::interpreter_glue(&format!("ws://{addr}/ws/create/{path}"))
                ))
            }),
        )
        .route(
            "/load/*path",
            get(move |Path(path): Path<String>| async move {
                Html(format!(
                    r#"
                <!DOCTYPE html>
                <html>
                <head> <title>UVL-Feature Config</title>  
                <style>
                    {style}
                </style>
                </head>
                <body> <div id="main"></div> </body>
                {glue}
                </html>
                "#,
                    // Create the glue code to connect to the WebSocket on the "/ws" route
                    glue =
                        dioxus_liveview::interpreter_glue(&format!("ws://{addr}/ws/load/{path}"))
                ))
            }),
        )
        .route(
            "/ws/:op/*path",
            get(
                move |ws: WebSocketUpgrade, Path((op, path)): Path<(String, String)>| async move {
                    ws.on_upgrade(move |socket| async move {
                        // When the WebSocket is upgraded, launch the LiveView with the app component
                        lazy_static::lazy_static! {
                            pub static ref COUNTER:AtomicU64= AtomicU64::new(0);
                        }

                        let id = COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        _ = view
                            .launch_with_props(
                                dioxus_liveview::axum_socket(socket),
                                crate::webview_frontend::App,
                                AppProps {
                                    initial: match op.as_str() {
                                        "create" => AppInitialParams::Create(path),
                                        "load" => AppInitialParams::Load(path),
                                        _ => AppInitialParams::InvalidOP,
                                    },
                                    pipeline: pipeline.clone(),
                                    id,
                                },
                            )
                            .await;

                        if pipeline
                            .inlay_state()
                            .is_active(crate::inlays::InlaySource::Web(id))
                        {
                            pipeline
                                .inlay_state()
                                .set_source(crate::inlays::InlaySource::None)
                                .await;
                        }
                    })
                },
            ),
        );

    axum::Server::bind(&addr.to_string().parse().unwrap())
        .serve(app.into_make_service())
        .await
        .unwrap();
}
