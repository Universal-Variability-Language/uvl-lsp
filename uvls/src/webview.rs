use crate::{core::*, ide, smt};
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
use std::sync::atomic::AtomicU64;
use std::sync::Arc;
use tokio::{
    select, spawn,
    sync::{mpsc, watch},
};
use tokio_util::sync::CancellationToken;
use ustr::Ustr;
mod frontend;
/* This web interface allows simple configuration of uvl models within the sever.
The GUI is written as a html-over-wire liveview, via dioxus. The liveview can then be
accessed directly in vs-code or the native browser. Each server instance has its own localhost
TCP port {p}, configuration is possible over two different entries:
localhost:{p}/create/{uvl_base_file} - Create an empty config from a uvl base file
localhost:{p}/load/{uvl_config_file} - Load a configuration from a json file


The actual GUI is implemented as redux style asynchronous event loop. This is
mainly due to the fact that its simple and requires minimal state management.
Currently the whole tree is redrawn when a value changes since there is only one global
configuration and tree state. This should be separated.
To synchronize the webview with the rest of the server two handlers are used:
ui_sync and smt::web_view_handler. The first detects file changes and rebuilds the target module,
the second handler calculates new smt values when things change.
*/

#[derive(PartialEq, Clone, Copy, Debug)]
pub enum Icon {
    File,
    Feature,
    Attributes,
    Attribute,
    Expand,
    Collapse,
    Circle,
    CircleCross,
    CircleCheck,
    CirclePlus,
    Link,
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
    Attributes(Ustr),
    File {
        alias: Option<Ustr>,
        name: String,
    },
    Feature {
        name: Ustr,
        config: Option<ConfigValue>,
        smt_value: Option<ConfigValue>,
        ty: Type,
        unsat: bool,
    },
    Attribute {
        name: Ustr,
        config: Option<ConfigValue>,
        default: ConfigValue,
        unsat: bool,
    },
    Link {
        tgt: ModuleSymbol,
        name: String,
        config: Option<ConfigValue>,
        smt_value: Option<ConfigValue>,
        ty: Type,
        unsat: bool,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct UIEntry {
    pub depth: u32,

    pub open: bool,
    pub value: UIEntryValue,
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

impl UIConfigState {
    fn unfold(&mut self) {
        let mut is_open = HashSet::new();
        for i in self.entries.values_mut().rev() {
            i.open = is_open.remove(&(i.depth as i32)) || i.should_open();
            if i.open {
                is_open.insert(i.depth as i32 - 1);
            }
        }
    }
}
#[derive(Debug, Clone, Default)]
pub struct UIConfigState {
    pub entries: IndexMap<ModuleSymbol, UIEntry>,
    pub tag: u8,
}

#[derive(Debug, Clone)]
pub struct UIState {
    pub sat: SatState,
    pub sync: UISyncState,
    pub solver_active: bool,
    pub dir: String,
    pub file_name: String,
    pub show: bool,
}
pub struct ConfigSource {
    pub root: FileID,
    pub module: ConfigModule,
    pub tag: u8,
    pub cancel: CancellationToken,
    pub ok: bool,
}

#[derive(Debug, Clone)]
pub enum UIAction {
    TreeDirty,
    ToggleEntry(ModuleSymbol, u8),
    UpdateRoot(Arc<Module>, u8),
    UpdateSMTModel(smt::SMTModel, u8),
    UpdateSMTInvalid(String, u8),
    Set(ModuleSymbol, u8, ConfigValue),
    Unset(ModuleSymbol, u8),
    ShowSym(ModuleSymbol, u8),
    SolverActive,
    Save,
    Show,
    ExpandAll,
    CollapseAll,
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
    module: &Module,
    base_depth: u32,
    instance: InstanceID,
    config: &HashMap<ModuleSymbol, ConfigValue>,
    entries: &mut IndexMap<ModuleSymbol, UIEntry>,
) {
    let mut last = Symbol::Root;
    let mut vdir = 0;
    file.visit_children_depth(Symbol::Root, true, |sym, depth| match sym {
        Symbol::Reference(_) => {
            let depth = depth + base_depth - 1;
            let name = file.path(sym).iter().join(".");
            //Values will be resolved in the frontend
            entries.insert(
                instance.sym(sym),
                UIEntry {
                    depth,
                    open: false,
                    value: UIEntryValue::Link {
                        name,
                        tgt: module.resolve_value(instance.sym(sym)),
                        config: None,
                        ty: Type::Real,
                        smt_value: None,
                        unsat: false,
                    },
                },
            );
            false
        }
        Symbol::Feature(_) | Symbol::Attribute(_) => {
            let depth = depth + base_depth - 1;
            match file.type_of(sym).unwrap() {
                Type::String | Type::Real | Type::Bool | Type::Attributes | Type::Object => {}
                _ => {
                    return true;
                }
            }
            if matches!((sym, last), (Symbol::Attribute(..), Symbol::Feature(..))) {
                entries.insert(
                    instance.sym(Symbol::Dir(vdir)),
                    UIEntry {
                        depth,
                        value: UIEntryValue::Attributes("attributes".into()),
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
            let name = file.name(sym).unwrap();

            let ms = instance.sym(sym);
            let config = config.get(&ms).cloned();

            entries.insert(
                ms,
                UIEntry {
                    open: false,
                    depth,
                    value: match sym {
                        Symbol::Feature(..) => UIEntryValue::Feature {
                            name,
                            unsat: false,
                            config,
                            smt_value: None,
                            ty: file.type_of(sym).unwrap(),
                        },
                        Symbol::Attribute(..) => match file.value(sym).unwrap() {
                            Value::Bool(num) => UIEntryValue::Attribute {
                                name,
                                config,
                                unsat: false,
                                default: ConfigValue::Bool(*num),
                            },
                            Value::Number(num) => UIEntryValue::Attribute {
                                name,
                                config,
                                unsat: false,
                                default: ConfigValue::Number(*num),
                            },
                            Value::String(s) => UIEntryValue::Attribute {
                                name,
                                config,
                                unsat: false,
                                default: ConfigValue::String(s.clone()),
                            },
                            Value::Attributes => UIEntryValue::Attributes(name),
                            _ => unimplemented!(),
                        },
                        _ => unimplemented!(),
                    },
                },
            );
            last = sym;
            true
        }
        _ => true,
    });
}

fn rebuild_tree(source: &ConfigSource) -> Option<UIConfigState> {
    let module = &source.module;
    if !module.ok {
        return None;
    }
    let root_file = source.module.file(InstanceID(0));
    let uri_head = root_file.uri.path().rfind("/").unwrap();
    let file_name = |uri: &tower_lsp::lsp_types::Url| uri.path()[uri_head + 1..].to_string();
    let mut entries: IndexMap<ModuleSymbol, UIEntry> = IndexMap::new();
    let mut content: Vec<(u32, InstanceID)> = vec![];
    for (origin, instance, tgt, depth) in module.instances_depth() {
        loop {
            if content.last().map(|l| l.0 > depth).unwrap_or(false) {
                let (depth, instance) = content.pop().unwrap();
                create_file_tree(
                    module.file(instance),
                    &module,
                    depth,
                    instance,
                    &source.module.values,
                    &mut entries,
                );
            } else {
                break;
            }
        }
        let file = module.file(origin.instance);
        entries.insert(
            origin,
            UIEntry {
                depth,
                open: false,
                value: UIEntryValue::File {
                    alias: if matches!(origin.sym, Symbol::Import(_)) {
                        file.imports()[origin.sym.offset()]
                            .alias
                            .as_ref()
                            .map(|p| p.name)
                    } else {
                        None
                    },
                    name: file_name(&tgt.uri),
                },
            },
        );
        content.push((depth + 1, instance));
    }
    for (depth, instance) in content.into_iter().rev() {
        create_file_tree(
            module.file(instance),
            &module,
            depth,
            instance,
            &source.module.values,
            &mut entries,
        );
    }

    Some(UIConfigState {
        entries,
        tag: source.tag,
    })
}

//Keeps the UI in sync with its context
async fn ui_sync(
    pipeline: AsyncPipeline,
    tx_sync: mpsc::Sender<UIAction>,
    target: FileID,
) -> Result<()> {
    let mut dirty = pipeline.subscribe_dirty_tree();
    loop {
        select! {
            _=dirty.recv()=>{
                info!("dirty");
                tx_sync.send(UIAction::TreeDirty).await?;
                let root =pipeline.sync_root_global().await?;
                if root.contains_id(target){

                tx_sync
                    .send(UIAction::UpdateRoot(
                        Arc::new(Module::new(target, root.fs(), &root.cache().ast)),
                        (root.revision() % 256) as u8,
                    ))

                    .await?;
                }

            },
            else =>{
                break;
            }
        }
    }
    Ok(())
}

fn rebuild_config(
    ui_state: &UseRef<UIState>,
    ui_config: &UseRef<UIConfigState>,
    source: &ConfigSource,
) {
    ui_config.with_mut(|x| {
        if let Some(tree) = rebuild_tree(&source) {
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
//Transfer state from with a new module
fn transfer_config(source: &mut ConfigSource, new: Arc<Module>) {
    if !new.ok {
        source.ok = false;
        return;
    }
    let ser = source.module.serialize();
    let (new_values, _) = new.resolve_config(&ser, |_, _| {});
    source.module.module = new;
    source.module.values = new_values;
    source.ok = true;
}

//redux style state management
async fn ui_event_loop(
    id: u64,
    tx_config: watch::Sender<ConfigSource>, //The current configuration
    mut rx_ui: UnboundedReceiver<UIAction>, //Incoming events from the ui
    mut rx_sync: mpsc::Receiver<UIAction>,  //Incoming events from the server
    ui_config: &UseRef<UIConfigState>,      //Displayed configuration tree
    ui_state: &UseRef<UIState>,             //Displayed meta parameters
    pipeline: &AsyncPipeline,
    tgt_path: String,
) -> Result<()> {
    let mut ctag = tx_config.borrow().tag; //Shortend root revision
    rebuild_config(ui_state, ui_config, &tx_config.borrow());
    loop {
        let e = select! {Some(e)=rx_ui.next()=>e,Some(e)=rx_sync.recv()=>e, else=>{break;}};
        match e {
            UIAction::SolverActive => {
                ui_state.with_mut(|state| {
                    state.solver_active = true;
                    state.sat = SatState::UNKNOWN;
                });
                ui_config.with_mut(|UIConfigState { entries, .. }| {
                    for e in entries.values_mut() {
                        e.unsat(false);
                    }
                });
            }
            UIAction::TreeDirty => {
                ui_state.with_mut(|state| {
                    state.sync = UISyncState::Dirty;
                });
            }
            UIAction::UpdateRoot(root, tag) => {
                ctag = tag;

                let ok = root.ok;
                tx_config.send_modify(|state| {
                    transfer_config(state, root);
                    state.tag = tag;
                    state.cancel.cancel();
                    state.cancel = CancellationToken::new();
                });
                if ok {
                    rebuild_config(ui_state, ui_config, &tx_config.borrow());
                } else {
                    ui_state.with_mut(|x| {
                        x.sync = UISyncState::InternalError("invalid sources".into());
                    });
                }
            }
            UIAction::ExpandAll => {
                ui_config.with_mut(|UIConfigState { entries, .. }| {
                    entries.into_iter().for_each(|(_, entrie)| {
                        entrie.open = true;
                    })
                });
            }
            UIAction::CollapseAll => {
                ui_config.with_mut(|UIConfigState { entries, .. }| {
                    entries.into_iter().for_each(|(_, entrie)| {
                        entrie.open = false;
                    })
                });
            }
            UIAction::Save => {
                let module = tx_config.borrow().module.clone();
                let output_name = ui_state.read().file_name.clone();
                let tgt_path = tgt_path.clone();
                tokio::task::spawn_blocking(move || {
                    if !module.ok {
                        return;
                    }
                    let ser = module.serialize();
                    #[derive(Serialize)]
                    struct RawConfig {
                        file: String,
                        config: ConfigEntry,
                    }
                    let config = RawConfig {
                        file: tgt_path,
                        config: ConfigEntry::Import(Default::default(), ser),
                    };
                    let out = serde_json::to_string_pretty(&config).unwrap();
                    let _ = std::fs::write(output_name, out);
                });
            }
            UIAction::Show => {
                let show = ui_state.with_mut(|state| {
                    state.show = !state.show;
                    state.show
                });

                if !show {
                    pipeline
                        .inlay_state()
                        .set_source(ide::inlays::InlaySource::None)
                        .await;
                } else {
                    pipeline
                        .inlay_state()
                        .set_source(ide::inlays::InlaySource::Web(id))
                        .await;
                    tx_config.send_modify(|config| {
                        config.cancel.cancel();
                        config.cancel = CancellationToken::new();
                    });
                }
            }
            UIAction::ToggleEntry(sym, tag) => {
                if tag != ctag {
                    continue;
                }
                ui_config.with_mut(|UIConfigState { entries, .. }| {
                    if let Some(v) = entries.get_mut(&sym) {
                        v.open = !v.open;
                    }
                });
            }
            UIAction::Set(sym, tag, val) => {
                if tag != ctag {
                    continue;
                }
                ui_config.with_mut(|UIConfigState { entries, .. }| {
                    if let Some(node) = entries.get_mut(&sym) {
                        node.update_config(Some(val.clone()));
                    }
                });
                tx_config.borrow().cancel.cancel();
                tx_config.send_modify(|config| {
                    config.module.values.insert(sym, val);
                    config.cancel.cancel();
                    config.cancel = CancellationToken::new();
                });
            }
            UIAction::Unset(sym, tag) => {
                if tag != ctag {
                    continue;
                }
                ui_config.with_mut(|UIConfigState { entries, .. }| {
                    if let Some(node) = entries.get_mut(&sym) {
                        node.update_config(None);
                    }
                });
                tx_config.borrow().cancel.cancel();
                tx_config.send_modify(|config| {
                    config.module.values.remove(&sym);
                    config.cancel.cancel();
                    config.cancel = CancellationToken::new();
                });
            }

            UIAction::ShowSym(sym, tag) => {
                if tag != ctag {
                    continue;
                }
                let req = {
                    let state = tx_config.borrow();
                    let file = state.module.file(sym.instance);
                    tower_lsp::lsp_types::ShowDocumentParams {
                        uri: file.uri.clone(),
                        external: None,
                        take_focus: Some(true),
                        selection: file.lsp_range(sym.sym),
                    }
                };
                let _ = pipeline
                    .client()
                    .send_request::<tower_lsp::lsp_types::request::ShowDocument>(req)
                    .await;
            }
            UIAction::UpdateSMTInvalid(msg, tag) => {
                if tag != ctag {
                    continue;
                }
                ui_state.with_mut(|state| {
                    state.sat = SatState::ERR(msg);
                    state.solver_active = false;
                })
            }
            UIAction::UpdateSMTModel(model, tag) => {
                if tag != ctag {
                    continue;
                }
                ui_config.with_mut(|UIConfigState { entries, .. }| match model {
                    smt::SMTModel::SAT { values, .. } => {
                        ui_state.with_mut(|state| {
                            state.sat = SatState::SAT;
                            state.solver_active = false
                        });
                        for (k, v) in values {
                            let entry = &mut entries[&k];

                            entry.unsat(false);
                            entry.update_smt(Some(v));
                        }
                    }
                    smt::SMTModel::UNSAT { reasons } => {
                        ui_state.with_mut(|state| {
                            state.sat = SatState::UNSAT;
                            state.solver_active = false;
                        });
                        for i in entries.values_mut() {
                            i.update_smt(None);
                            i.unsat(false);
                        }
                        for i in reasons {
                            match i {
                                smt::AssertInfo(
                                    k,
                                    smt::AssertName::Config | smt::AssertName::Attribute,
                                ) => {
                                    entries[&k].unsat(true);
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
    Ok(())
}
//UI coroutine handles all state managment and creation
pub async fn ui_main(
    id: u64,
    pipeline: AsyncPipeline,
    ui_state: UseRef<UIState>,
    ui_config: UseRef<UIConfigState>,
    ui_rx: UnboundedReceiver<UIAction>,
    initial: AppInitialParams,
) -> Result<()> {
    let (initial_config, dest, tgt_path) = match initial {
        AppInitialParams::Create(path) => {
            let root = pipeline.sync_root_global().await?;
            let id = FileID::new(format!("file:///{path}").as_str());
            if root.contains_id(id) {
                let c = ConfigSource {
                    root: id,
                    module: ConfigModule {
                        module: Arc::new(Module::new(id, root.fs(), &root.cache().ast)),
                        values: HashMap::new(),
                        source_map: HashMap::new(),
                    },
                    tag: (root.revision() % 256) as u8,
                    cancel: CancellationToken::new(),
                    ok: true,
                };
                let path = id.filepath();
                let mut dest = path.clone();
                let tgt_path = path.file_name().unwrap().to_str().unwrap().to_string();
                dest.set_extension("uvl.json");
                Ok((c, dest, tgt_path))
            } else {
                Err("source model not found")
            }
        }
        AppInitialParams::Load(path) => {
            let root = pipeline.sync_root_global().await?;
            let path = FileID::new(format!("file:///{path}").as_str());
            if let Some(src) = root.cache().config_modules.get(&path) {
                if !src.ok {
                    Err("invalid config")?;
                }
                let id = src.file(InstanceID(0)).id;

                let src: &ConfigModule = &**src;
                let c = ConfigSource {
                    root: id,
                    module: src.clone(),
                    tag: (root.revision() % 256) as u8,
                    cancel: CancellationToken::new(),
                    ok: src.ok,
                };
                let dest = path.filepath();
                let tgt_path = src.module.file(InstanceID(0)).id.filepath();
                let tgt_path = tgt_path.strip_prefix(dest.parent().unwrap()).unwrap();
                Ok((c, dest, tgt_path.to_str().unwrap().to_string()))
            } else {
                Err("configuration not found")
            }
        }
        AppInitialParams::InvalidOP => Err("invalid server operation"),
    }?;
    ui_state.with_mut(|state| {
        if let Some(p) = dest.parent() {
            state.dir = p.to_str().unwrap().to_string();
        }
        state.sync = UISyncState::Valid;
        state.file_name = dest.file_name().unwrap().to_str().unwrap().to_string();
    });
    let root = initial_config.root;
    let (tx_sync, rx_sync) = mpsc::channel(32);
    let (tx_config, rx_config) = watch::channel(initial_config);
    //SMT value handler
    spawn(smt::web_view_handler(
        rx_config,
        tx_sync.clone(),
        pipeline.inlay_state().clone(),
        ide::inlays::InlaySource::Web(id),
    ));
    //Sync module with the lsp state
    spawn(ui_sync(pipeline.clone(), tx_sync, root));
    //Run the event loop
    ui_event_loop(
        id, tx_config, ui_rx, rx_sync, &ui_config, &ui_state, &pipeline, tgt_path,
    )
    .await?;

    info!("exit main");
    Ok(())
}
//HTTP server for the configuration interface
pub async fn web_handler(pipeline: AsyncPipeline, port: u16) {
    info!("Starting web handler");
    let addr: std::net::SocketAddr = ([127, 0, 0, 1], port).into();
    let view = dioxus_liveview::LiveViewPool::new();
    let style = include_str!("webview/style.css");

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
                        // When the WebSocket is upgraded, launch the LiveView with the App component
                        lazy_static::lazy_static! {
                            pub static ref COUNTER:AtomicU64= AtomicU64::new(0);
                        }

                        let id = COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        _ = view
                            .launch_with_props(
                                dioxus_liveview::axum_socket(socket),
                                frontend::App,
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
                            .is_active(ide::inlays::InlaySource::Web(id))
                        {
                            pipeline
                                .inlay_state()
                                .set_source(ide::inlays::InlaySource::None)
                                .await;
                        }
                        info!("Exit www");
                    })
                },
            ),
        );

    axum::Server::bind(&addr.to_string().parse().unwrap())
        .serve(app.into_make_service())
        .await
        .unwrap();
}
