#![allow(dead_code)]
#![forbid(unsafe_code)]

use flexi_logger::FileSpec;
use get_port::Ops;

use hashbrown::HashMap;
use log::info;
use percent_encoding::percent_decode_str;
use serde::Serialize;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::SystemTime;
use tokio::{join, spawn};
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};
mod core;
mod ide;
mod smt;
mod webview;
use crate::core::*;
use crate::smt::{smt_lib::Expr, uvl2smt, SmtSolver};
struct Settings {
    //can the client show websites on its own
    //ie client==vscode
    has_webview: bool,
}
impl Default for Settings {
    fn default() -> Self {
        Settings { has_webview: false }
    }
}
//The LSP
struct Backend {
    client: Client,
    coloring: Arc<ide::color::State>,
    pipeline: AsyncPipeline,
    web_handler_uri: String,
    settings: parking_lot::Mutex<Settings>,
}
impl Backend {
    fn load(&self, uri: Url) {
        let pipeline = self.pipeline.clone();
        tokio::task::spawn_blocking(move || {
            load_blocking(uri, &pipeline);
        });
    }
    async fn snapshot(&self, uri: &Url, sync: bool) -> Result<Option<(Draft, Arc<RootGraph>)>> {
        self.pipeline
            .snapshot(uri, sync)
            .await
            .map_err(|_| shutdown_error())
    }
    async fn open_url(&self, uri: String) {
        if self.settings.lock().has_webview {
            #[derive(Serialize)]
            struct OpenArgs {
                uri: String,
            }
            let _ = self
                .client
                .send_request::<request::ExecuteCommand>(ExecuteCommandParams {
                    command: "uvls.open_web".into(),
                    arguments: vec![serde_json::to_value(OpenArgs { uri }).unwrap()],
                    work_done_progress_params: WorkDoneProgressParams {
                        work_done_token: None,
                    },
                })
                .await;
        } else {
            let _ = open::that(uri);
        }
    }
}
//load a file, this is tricky because the editor can also load it at the same time
fn load_blocking(uri: Url, pipeline: &AsyncPipeline) {
    if let Err(e) = std::fs::File::open(uri.to_file_path().unwrap()).and_then(|mut f| {
        let meta = f.metadata()?;
        let modified = meta.modified()?;

        if !pipeline.should_load(&uri, modified) {
            return Ok(());
        }
        let mut data = String::new();
        f.read_to_string(&mut data)?;
        pipeline.open(uri.clone(), data, DocumentState::OwnedByOs(modified));
        Ok(())
    }) {
        info!("Failed to load file {} : {}", uri, e);
    }
}
//load all files under given a path
fn load_all_blocking(path: &Path, pipeline: AsyncPipeline) {
    for e in walkdir::WalkDir::new(path)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().is_file())
        .filter(|e| {
            e.path()
                .extension()
                .map(|e| e == std::ffi::OsStr::new("uvl"))
                .unwrap_or(false)
        })
    {
        load_blocking(Url::from_file_path(e.path()).unwrap(), &pipeline)
    }
}
fn shutdown_error() -> tower_lsp::jsonrpc::Error {
    tower_lsp::jsonrpc::Error {
        code: tower_lsp::jsonrpc::ErrorCode::InternalError,
        message: "".into(),
        data: None,
    }
}
//Handler for different LSP requests
#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(&self, init_params: InitializeParams) -> Result<InitializeResult> {
        #[allow(deprecated)]
        let root_folder = init_params
            .root_path
            .as_deref()
            .or_else(|| init_params.root_uri.as_ref().map(|p| p.path()))
            .map(PathBuf::from);
        if let Some(root_folder) = root_folder {
            let semantic = self.pipeline.clone();
            //cheap fix for better intial load, we should really use priority model to prefer
            //editor owned files
            spawn(async move {
                tokio::task::spawn_blocking(move || {
                    load_all_blocking(&root_folder, semantic);
                })
                .await
            });
        }
        if init_params
            .client_info
            .map(|info| matches!(info.name.as_str(), "Visual Studio Code"))
            .unwrap_or(false)
        {
            self.settings.lock().has_webview = true;
        }

        Ok(InitializeResult {
            server_info: Some(ServerInfo {
                name: String::from("uvl lsp"),
                version: None,
            }),
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::INCREMENTAL,
                )),
                completion_provider: Some(CompletionOptions {
                    resolve_provider: Some(false),
                    all_commit_characters: None,
                    trigger_characters: Some(vec![".".to_string()]),
                    ..Default::default()
                }),
                definition_provider: Some(OneOf::Left(true)),
                semantic_tokens_provider: Some(
                    SemanticTokensServerCapabilities::SemanticTokensOptions(
                        SemanticTokensOptions {
                            work_done_progress_options: WorkDoneProgressOptions {
                                work_done_progress: None,
                            },
                            legend: SemanticTokensLegend {
                                token_types: ide::color::token_types(),
                                token_modifiers: ide::color::modifiers(),
                            },
                            range: None,
                            full: Some(SemanticTokensFullOptions::Delta { delta: Some(true) }),
                        },
                    ),
                ),
                folding_range_provider: Some(FoldingRangeProviderCapability::Simple(true)),
                references_provider: Some(OneOf::Left(true)),
                rename_provider: Some(OneOf::Left(true)),
                code_lens_provider: Some(CodeLensOptions {
                    resolve_provider: Some(true),
                }),
                inlay_hint_provider: Some(OneOf::Left(true)),
                code_action_provider: Some(CodeActionProviderCapability::Simple(true)),
                execute_command_provider: Some(ExecuteCommandOptions {
                    commands: vec![
                        "uvls/show_config".into(),
                        "uvls/hide_config".into(),
                        "uvls/open_config".into(),
                        "uvls/load_config".into(),
                        "uvls/generate_diagram".into(),
                        "uvls/generate_configurations".into(),
                    ],
                    work_done_progress_options: WorkDoneProgressOptions {
                        work_done_progress: None,
                    },
                }),
                ..Default::default()
            },
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "server initialized!")
            .await;

        let watcher_uvl = FileSystemWatcher {
            glob_pattern: GlobPattern::String("**/*.uvl".to_string()),
            kind: None,
        };
        let watcher_config = FileSystemWatcher {
            glob_pattern: GlobPattern::String("**/*.uvl.json".to_string()),
            kind: None,
        };
        let reg = Registration {
            id: "watcher".to_string(),
            method: "workspace/didChangeWatchedFiles".to_string(),
            register_options: serde_json::to_value(DidChangeWatchedFilesRegistrationOptions {
                watchers: vec![watcher_config, watcher_uvl],
            })
            .ok(),
        };
        if self.client.register_capability(vec![reg]).await.is_err() {
            info!("failed to initialize file watchers");
        }
    }
    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        info!("received did_open {:?}", params.text_document.uri);
        self.pipeline.open(
            params.text_document.uri,
            params.text_document.text,
            DocumentState::OwnedByEditor,
        );
        info!("done did_open");
    }
    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let uri = params.text_document.uri.clone();
        self.pipeline.update(params);
        self.client.publish_diagnostics(uri, vec![], None).await;
        info!("done did_change");
    }
    async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        info!("received completion request");
        if let Some((draft, root)) = self
            .snapshot(&params.text_document_position.text_document.uri, false)
            .await?
        {
            return Ok(Some(CompletionResponse::List(
                ide::completion::compute_completions(root, &draft, params.text_document_position),
            )));
        }
        Ok(None)
    }
    async fn folding_range(&self, params: FoldingRangeParams) -> Result<Option<Vec<FoldingRange>>> {
        let uri = params.text_document.uri;
        let root_fileid = FileID::from_uri(&Url::parse(uri.as_str()).unwrap());
        let root_graph = self.pipeline.root().borrow_and_update().clone();
        if !root_graph.contains_id(root_fileid) {
            return Ok(None);
        }

        if let Some(document) = root_graph.files.get(&root_fileid) {
            let c = ast::collapse::Collapse::new(
                document.source.clone(),
                document.tree.clone(),
                uri.clone(),
            );
            return Ok(Some(c.ranges));
        }
        Ok(None)
    }
    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let uri = &params.text_document_position_params.text_document.uri;
        if let Some((draft, root)) = self.snapshot(uri, true).await? {
            Ok(ide::location::goto_definition(
                &root,
                &draft,
                &params.text_document_position_params.position,
                uri,
            ))
        } else {
            Ok(None)
        }
    }
    async fn references(&self, params: ReferenceParams) -> Result<Option<Vec<Location>>> {
        let uri = &params.text_document_position.text_document.uri;
        if let Some((draft, root)) = self.snapshot(uri, true).await? {
            Ok(ide::location::find_references(
                &root,
                &draft,
                &params.text_document_position.position,
                uri,
            ))
        } else {
            return Ok(None);
        }
    }
    async fn rename(&self, params: RenameParams) -> Result<Option<WorkspaceEdit>> {
        info!("[RENAME] params: {:?}", params);
        let uri = &params.text_document_position.text_document.uri;
        if let Some((draft, root)) = self.snapshot(uri, true).await? {
            Ok(ide::location::rename(
                &root,
                &draft,
                uri,
                &params.text_document_position.position,
                params.new_name,
            ))
        } else {
            return Ok(None);
        }
    }
    async fn semantic_tokens_full(
        &self,
        params: SemanticTokensParams,
    ) -> Result<Option<SemanticTokensResult>> {
        let uri = params.text_document.uri;
        if let Some((draft, root)) = self.snapshot(&uri, false).await? {
            let color = self.coloring.clone();
            match draft {
                Draft::UVL { source, tree, .. } => Ok(Some(SemanticTokensResult::Tokens(
                    color.get(root, uri, tree, source),
                ))),
                Draft::JSON { .. } => Ok(None),
            }
        } else {
            Ok(None)
        }
    }
    async fn semantic_tokens_full_delta(
        &self,
        params: SemanticTokensDeltaParams,
    ) -> Result<Option<SemanticTokensFullDeltaResult>> {
        let uri = params.text_document.uri;
        if let Some((draft, root)) = self.snapshot(&uri, false).await? {
            let color = self.coloring.clone();
            match draft {
                Draft::UVL { source, tree, .. } => Ok(Some(color.delta(root, uri, tree, source))),
                Draft::JSON { .. } => Ok(None),
            }
        } else {
            Ok(None)
        }
    }
    async fn did_save(&self, _: DidSaveTextDocumentParams) {
        self.client
            .log_message(MessageType::INFO, "file saved!")
            .await;
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        self.coloring.remove(&params.text_document.uri);
        self.client
            .log_message(MessageType::INFO, "file closed!")
            .await;
        self.pipeline
            .delete(&params.text_document.uri, DocumentState::OwnedByEditor)
            .await;
        self.load(params.text_document.uri);
    }
    async fn did_change_watched_files(&self, params: DidChangeWatchedFilesParams) {
        info!("file change {:?}", params);
        for i in params.changes {
            match i.typ {
                FileChangeType::CREATED => {
                    self.load(i.uri);
                }
                FileChangeType::CHANGED => {
                    self.load(i.uri);
                }
                FileChangeType::DELETED => {
                    self.pipeline
                        .delete(&i.uri, DocumentState::OwnedByOs(SystemTime::now()))
                        .await;
                }
                _ => {}
            }
        }
    }
    async fn execute_command(
        &self,
        params: ExecuteCommandParams,
    ) -> Result<Option<serde_json::Value>> {
        let uri: Url = serde_json::from_value(params.arguments[0].clone()).unwrap();
        match params.command.as_str() {
            "uvls/load_config" => {
                let target = format!("{}/load{}", self.web_handler_uri, uri.path());
                self.open_url(target).await;
            }
            "uvls/open_config" => {
                let target = format!("{}/create{}", self.web_handler_uri, uri.path());
                self.open_url(target).await;
            }
            "uvls/show_config" => {
                self.pipeline
                    .inlay_state()
                    .set_source(ide::inlays::InlaySource::File(semantic::FileID::new(
                        uri.as_str(),
                    )))
                    .await;
                self.pipeline.touch(&uri);
                self.client.code_lens_refresh().await?;
            }
            "uvls/hide_config" => {
                self.pipeline
                    .inlay_state()
                    .set_source(ide::inlays::InlaySource::None)
                    .await;
                self.pipeline.touch(&uri);
                self.client.code_lens_refresh().await?;
            }
            "uvls/generate_diagram" => {
                let root_fileid = FileID::from_uri(&Url::parse(uri.as_str()).unwrap());
                let root_graph = self.pipeline.root().borrow_and_update().clone();
                if !root_graph.contains_id(root_fileid) {
                    {}
                }

                let document = root_graph.files.get(&root_fileid).unwrap();
                let g = ast::graph::Graph::new(
                    document.source.clone(),
                    document.tree.clone(),
                    uri.clone(),
                );

                // write graph script (dot) to file:
                let diagram_file_extension = "dot";
                let re = regex::Regex::new(r"(.*\.)(.*)").unwrap();
                let path = re.replace(uri.path(), |caps: &regex::Captures| {
                    format!("{}{}", &caps[1], diagram_file_extension)
                });
                let file = std::fs::File::create(path.as_ref()).or(std::fs::File::create(
                    percent_decode_str(&path.replacen("/", "", 1))
                        .decode_utf8()
                        .unwrap()
                        .into_owned(),
                )); // windows specific

                if file.is_ok() {
                    file.unwrap()
                        .write_all(g.dot.as_bytes())
                        .expect("Error while writing to dot file");
                } else {
                    return Ok(Some(serde_json::to_value(g.dot).unwrap()));
                }
            }
            "uvls/generate_configurations" => {
                let n: u32 = serde_json::from_value(params.arguments[1].clone()).unwrap_or(0);

                let root_fileid = FileID::from_uri(&Url::parse(uri.as_str()).unwrap());
                let root_graph = self.pipeline.root().borrow_and_update().clone();
                if !root_graph.contains_id(root_fileid) {
                    return Ok(None);
                }
                let module = Module::new(root_fileid, root_graph.fs(), &root_graph.cache().ast);

                let smt_module = uvl2smt(&module, &HashMap::new());

                let solver = SmtSolver::new(
                    smt_module.to_source(&module),
                    &root_graph.cancellation_token(),
                )
                .await;

                match solver {
                    Ok(mut smt_solver) => match smt_solver.check_sat().await {
                        Ok(true) => {
                            let query = smt_module
                                .variables
                                .iter()
                                .enumerate()
                                .fold(String::new(), |acc, (i, _)| format!("{acc} v{i}"));
                            // generate the unique n solutions
                            for i in 1..=n {
                                if !smt_solver.check_sat().await.unwrap_or(false) {
                                    break; // no more solutions
                                }
                                let values = smt_solver
                                    .values(query.clone())
                                    .await
                                    .unwrap_or(String::from(""));

                                let values_parsed: HashMap<ModuleSymbol, ConfigValue> =
                                    smt_module.parse_values(&values, &module).collect();

                                // Store solution in file
                                let config_module = ConfigModule {
                                    module: Arc::new(module.clone()),
                                    values: values_parsed.clone(),
                                    source_map: Default::default(),
                                };
                                let uri = uri.clone();
                                tokio::task::spawn_blocking(move || {
                                    if !config_module.ok {
                                        return;
                                    }
                                    let ser = config_module.serialize();
                                    #[derive(Serialize)]
                                    struct RawConfig {
                                        file: String,
                                        config: ConfigEntry,
                                    }
                                    let config = RawConfig {
                                        file: uri
                                            .to_file_path()
                                            .unwrap()
                                            .file_name()
                                            .unwrap()
                                            .to_str()
                                            .unwrap_or("-")
                                            .to_string(),
                                        config: ConfigEntry::Import(Default::default(), ser),
                                    };

                                    let out = serde_json::to_string_pretty(&config).unwrap();
                                    let _ = std::fs::write(
                                        format!(
                                            "{}-{}.json",
                                            uri.to_file_path()
                                                .unwrap()
                                                .file_name()
                                                .unwrap()
                                                .to_str()
                                                .unwrap(),
                                            i
                                        ),
                                        out,
                                    );
                                });

                                // Generate assertion to make this solution unique
                                if i < n {
                                    let mut assertion: Vec<Expr> = vec![];
                                    values_parsed.into_iter().for_each(
                                        |(sym, config)| match config {
                                            ConfigValue::Bool(bool) => {
                                                assertion.push(Expr::Equal(vec![
                                                    Expr::Var(
                                                        smt_module
                                                            .variables
                                                            .get_index_of(&sym)
                                                            .unwrap_or(0),
                                                    ),
                                                    Expr::Bool(!bool),
                                                ]))
                                            }
                                            _ => (),
                                        },
                                    );

                                    let assertion_string = smt_module.assert_to_source(
                                        0,
                                        &None,
                                        &Expr::Or(assertion.clone()),
                                        false,
                                    );
                                    let _ = smt_solver.push(assertion_string).await;
                                }
                            }
                        }
                        _ => {
                            info!("No SAT solution for file");
                        }
                    },
                    _ => (),
                }
                return Ok(None);
            }
            _ => (),
        }
        Ok(None)
    }

    async fn inlay_hint(&self, params: InlayHintParams) -> Result<Option<Vec<InlayHint>>> {
        let uri = params.text_document.uri;
        if let Some((draft, _)) = self.snapshot(&uri, true).await? {
            let source = draft.source();
            let start = util::byte_offset(&params.range.start, source);
            let end = util::byte_offset(&params.range.end, source);
            info!("update inlays {:?}", params.range);
            Ok(self.pipeline.inlay_state().get(&uri, start..end).await)
        } else {
            Err(tower_lsp::jsonrpc::Error {
                code: tower_lsp::jsonrpc::ErrorCode::ServerError(1),
                message: "failed to get context".into(),
                data: None,
            })?
        }
    }
    async fn code_lens(&self, params: CodeLensParams) -> Result<Option<Vec<CodeLens>>> {
        let uri = params.text_document.uri;
        let uri_json =
            serde_json::to_value(&uri).map_err(|_| tower_lsp::jsonrpc::Error::internal_error())?;
        if util::is_config(&uri) {
            Ok(Some(vec![
                CodeLens {
                    range: Range {
                        start: Position {
                            line: 0,
                            character: 0,
                        },
                        end: Position {
                            line: 0,
                            character: 0,
                        },
                    },
                    command: if self.pipeline.inlay_state().is_active(
                        ide::inlays::InlaySource::File(semantic::FileID::new(uri.as_str())),
                    ) {
                        Some(Command {
                            title: "hide".into(),
                            command: "uvls/hide_config".into(),
                            arguments: Some(vec![uri_json.clone()]),
                        })
                    } else {
                        Some(Command {
                            title: "show".into(),
                            command: "uvls/show_config".into(),
                            arguments: Some(vec![uri_json.clone()]),
                        })
                    },
                    data: None,
                },
                CodeLens {
                    range: Range {
                        start: Position {
                            line: 0,
                            character: 0,
                        },
                        end: Position {
                            line: 0,
                            character: 0,
                        },
                    },
                    command: Some(Command {
                        title: "configure".into(),
                        command: "uvls/load_config".into(),
                        arguments: Some(vec![uri_json.clone()]),
                    }),
                    data: None,
                },
            ]))
        } else {
            Ok(Some(vec![
                CodeLens {
                    range: Range {
                        start: Position {
                            line: 0,
                            character: 0,
                        },
                        end: Position {
                            line: 0,
                            character: 0,
                        },
                    },
                    command: Some(Command {
                        title: "configure".into(),
                        command: "uvls/open_config".into(),
                        arguments: Some(vec![uri_json.clone()]),
                    }),
                    data: None,
                },
                CodeLens {
                    range: Range {
                        start: Position {
                            line: 0,
                            character: 0,
                        },
                        end: Position {
                            line: 0,
                            character: 0,
                        },
                    },
                    command: Some(Command {
                        title: "generate graph".into(),
                        command: "uvls/generate_diagram".into(),
                        arguments: Some(vec![uri_json]),
                    }),
                    data: None,
                },
            ]))
        }
    }

    async fn code_action(&self, params: CodeActionParams) -> Result<Option<CodeActionResponse>> {
        for diagnostic in params.clone().context.diagnostics {
            // Checks if there is a quick fix for the current diagnostic message
            match diagnostic.clone().data {
                Some(serde_json::value::Value::Number(number)) => {
                    match ErrorType::from_u32(number.as_u64().unwrap_or(0) as u32) {
                        ErrorType::Any => info!("No Quickfix for this Error"),
                        ErrorType::FeatureNameContainsDashes => {
                            return actions::rename_dash(
                                params.clone(),
                                diagnostic,
                                self.snapshot(&params.text_document.uri, false).await,
                            )
                        }
                    }
                }
                _ => (),
            }
        }
        return Ok(None);
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }
}

fn main() {
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .thread_stack_size(8 * 1024 * 1024)
        .build()
        .unwrap();
    runtime.block_on(server_main());
}
async fn server_main() {
    std::env::set_var("RUST_BACKTRACE", "1");

    log_panics::Config::new()
        .backtrace_mode(log_panics::BacktraceMode::Unresolved)
        .install_panic_hook();

    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();
    //only needed for vscode auto update
    if std::env::args().any(|a| &a == "-v") {
        println!("v{}", env!("CARGO_PKG_VERSION"));
        return;
    }

    let _logger = flexi_logger::Logger::try_with_env_or_str("info")
        .expect("Log spec string broken")
        .log_to_file(
            FileSpec::default()
                .directory(std::env::temp_dir())
                .basename("UVLS")
                .suppress_timestamp()
                .suffix("log"),
        )
        .write_mode(flexi_logger::WriteMode::Direct)
        .start()
        .expect("Failed to start logger");
    log_panics::init();
    info!("UVLS start");
    let (service, socket) = LspService::new(|client| {
        let pipeline = AsyncPipeline::new(client.clone());
        info!("create service");
        let port = get_port::tcp::TcpPort::in_range(
            "127.0.0.1",
            get_port::Range {
                min: 3000,
                max: 6000,
            },
        )
        .unwrap();
        spawn(webview::web_handler(pipeline.clone(), port));
        Backend {
            settings: parking_lot::Mutex::new(Settings::default()),
            web_handler_uri: format!("http://localhost:{port}"),
            pipeline,
            coloring: Arc::new(ide::color::State::new()),
            client,
        }
    });
    join!(Server::new(stdin, stdout, socket).serve(service));
}
