use crate::ast::*;
use crate::semantic::FileID;
use crate::semantic::RootGraph;
use crate::semantic::RootSymbol;
use crate::smt::SMTModel;
use log::info;
use parking_lot::Mutex;
use std::sync::Arc;
use tokio::sync::{mpsc, oneshot};
use tokio::time::Instant;
use tower_lsp::lsp_types::*;
use tower_lsp::Client;

#[derive(PartialEq, Debug)]
pub enum InlaySource {
    None,
    File(FileID),
    Web(u64),
}
#[derive(Clone)]
pub struct InlayHandler {
    source: Arc<Mutex<InlaySource>>,
    tx: mpsc::Sender<InlayEvent>,
}
impl InlayHandler {
    pub fn new(client: Client) -> Self {
        let (tx, rx) = mpsc::channel(32);
        tokio::spawn(inlay_handler(rx, client));
        Self {
            source: Arc::new(Mutex::new(InlaySource::None)),
            tx,
        }
    }
    pub fn is_active(&self, source: InlaySource) -> bool {
        *self.source.lock() == source
    }
    pub async fn set_source(&self, source: InlaySource) {
        *self.source.lock() = source;
        let _ = self.tx.send(InlayEvent::SetSource).await;
    }
    pub async fn maybe_publish(
        &self,
        source: InlaySource,
        root: &Arc<RootGraph>,
        model: &SMTModel,
        timestamp: Instant,
    ) {
        if *self.source.lock() == source {
            let _ = self
                .tx
                .send(InlayEvent::Publish(model.clone(), root.clone(), timestamp))
                .await;
        }
    }
    pub async fn get(&self, uri: &Url, span: Span) -> Option<Vec<InlayHint>> {
        let (tx, rx) = oneshot::channel();
        let _ = self
            .tx
            .send(InlayEvent::Get(InlayRequest {
                target: FileID::new(uri.as_str()),
                span,
                out: tx,
            }))
            .await;
        rx.await.ok().flatten()
    }
}
struct InlayRequest {
    target: FileID,
    span: Span,
    out: oneshot::Sender<Option<Vec<InlayHint>>>,
}
enum InlayEvent {
    Get(InlayRequest),
    Publish(SMTModel, Arc<RootGraph>, Instant),
    SetSource,
}
fn generate(root: &RootGraph, model: &SMTModel, id: FileID, range: Span) -> Option<Vec<InlayHint>> {
    let doc = root.file(id);
    match model {
        SMTModel::SAT { values, .. } => Some(
            doc.all_features()
                .chain(doc.all_attributes())
                .chain(doc.all_references())
                .filter(|f| range.contains(&doc.span(*f).unwrap().start))
                .filter_map(|sym| {
                    root.resolve_sym(RootSymbol { sym, file: id })
                        .and_then(|rs| values.get(&rs))
                        .map(|val| {
                            let range = doc.lsp_range(sym).unwrap();
                            InlayHint {
                                label: InlayHintLabel::String(format!(": {val}")),
                                position: range.end,
                                kind: Some(InlayHintKind::PARAMETER),
                                data: None,
                                padding_left: Some(true),
                                padding_right: Some(true),
                                tooltip: None,
                                text_edits: None,
                            }
                        })
                })
                .collect(),
        ),
        SMTModel::UNSAT { reasons } => Some(
            reasons
                .iter()
                .filter_map(|i| {
                    if id == i.symbol().file
                        && range.contains(&doc.span(i.symbol().sym).unwrap().start)
                    {
                        let range = doc.lsp_range(i.symbol().sym).unwrap();
                        Some(InlayHint {
                            label: InlayHintLabel::String("UNSAT! ".into()),
                            position: range.end,
                            kind: Some(InlayHintKind::PARAMETER),
                            data: None,
                            padding_left: Some(true),
                            padding_right: Some(true),
                            tooltip: None,
                            text_edits: None,
                        })
                    } else {
                        None
                    }
                })
                .collect(),
        ),
    }
}
async fn inlay_handler(mut rx: mpsc::Receiver<InlayEvent>, client: Client) {
    let mut map: Option<(SMTModel, Arc<RootGraph>)> = None;
    let mut latest = Instant::now();
    let mut initial = false;
    while let Some(e) = rx.recv().await {
        match e {
            InlayEvent::Get(request) => {
                info!("get");
                if let Some((model, root)) = map.as_ref() {
                    let _ = request
                        .out
                        .send(generate(root, model, request.target, request.span));
                } else {
                    let _ = request.out.send(None);
                }
            }
            InlayEvent::Publish(model, root, timestamp) => {
                if timestamp <= latest {
                    continue;
                }
                latest = timestamp;
                info!("publish {model:?}");
                client
                    .send_request::<tower_lsp::lsp_types::request::InlayHintRefreshRequest>(())
                    .await
                    .unwrap();
                if initial {
                    let rs = match &model {
                        SMTModel::SAT { values, .. } => values.keys().next().cloned(),
                        SMTModel::UNSAT { reasons } => reasons.iter().next().map(|i| i.symbol()),
                    };
                    if let Some(rs) = rs {
                        //Force VS-Code to refresh inlays since inlay-hints-refresh is sometimes ingored
                        //When the document had no previous inlays
                        //Currently done via a pseudo edit(TODO this sucks)
                        //Insert a '0'
                        let changes = [(
                            rs.file.url().unwrap(),
                            vec![TextEdit::new(
                                Range {
                                    start: Position::default(),
                                    end: Position {
                                        line: 0,
                                        character: 0,
                                    },
                                },
                                "1".into(),
                            )],
                        )];
                        let _ = client
                            .send_request::<tower_lsp::lsp_types::request::ApplyWorkspaceEdit>(
                                ApplyWorkspaceEditParams {
                                    label: None,
                                    edit: WorkspaceEdit {
                                        changes: Some(changes.into()),
                                        document_changes: None,
                                        change_annotations: None,
                                    },
                                },
                            )
                            .await;

                        //Remove it
                        let changes = [(
                            rs.file.url().unwrap(),
                            vec![TextEdit::new(
                                Range {
                                    start: Position::default(),
                                    end: Position {
                                        line: 0,
                                        character: 1,
                                    },
                                },
                                "".into(),
                            )],
                        )];
                        let _ = client
                            .send_request::<tower_lsp::lsp_types::request::ApplyWorkspaceEdit>(
                                ApplyWorkspaceEditParams {
                                    label: None,
                                    edit: WorkspaceEdit {
                                        changes: Some(changes.into()),
                                        document_changes: None,
                                        change_annotations: None,
                                    },
                                },
                            )
                            .await;

                        let _ = client
                            .show_document(ShowDocumentParams {
                                uri: rs.file.url().unwrap(),
                                external: Some(false),
                                take_focus: Some(true),
                                selection: Some(Range::default()),
                            })
                            .await;
                        info!("focus");
                    }
                    initial = false;
                }
                map = Some((model, root));
                client
                    .send_request::<tower_lsp::lsp_types::request::InlayHintRefreshRequest>(())
                    .await
                    .unwrap();
            }

            InlayEvent::SetSource => {
                initial = true;
                info!("set source");
                map = None;
                client
                    .send_request::<tower_lsp::lsp_types::request::InlayHintRefreshRequest>(())
                    .await
                    .unwrap();
            }
        }
    }
}
