use crate::core::*;
use ast::insert_multi;
use hashbrown::HashMap;
use log::info;
use ropey::Rope;
use tokio::sync::mpsc;
use tokio::time::Instant;
use tower_lsp::lsp_types::*;
use tower_lsp::Client;
use tree_sitter::{Node, QueryCursor, Tree};

// This type is used to provide quickactions for a error
#[derive(Clone, Debug, PartialEq)]
pub enum ErrorType {
    Any = 0,
    FeatureNameContainsDashes,
}

impl ErrorType {
    pub fn from_u32(value: u32) -> ErrorType {
        match value {
            1 => ErrorType::FeatureNameContainsDashes,
            _ => ErrorType::Any,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct ErrorInfo {
    pub location: Range,
    pub severity: DiagnosticSeverity,
    pub weight: u32,
    pub msg: String,
    pub error_type: ErrorType,
}

#[derive(Clone, Debug)]
pub struct FileErrorInfo {
    pub error: ErrorInfo,
    pub file: FileID,
}

impl ErrorInfo {
    fn diagnostic(self) -> Diagnostic {
        Diagnostic {
            range: self.location,
            severity: Some(self.severity),
            message: self.msg,
            data: Some(serde_json::value::Value::Number(
                serde_json::value::Number::from(self.error_type.clone() as i32),
            )),
            ..Default::default()
        }
    }
}
pub async fn publish(client: &Client, uri: &Url, err: &[ErrorInfo]) {
    // reduces cardinality error to one error
    let mut reduced_err = vec![];
    err.iter().for_each(|ele| {
        if !reduced_err.contains(ele) {
            reduced_err.push(ele.clone())
        }
    });
    if let Some(max) = reduced_err.clone().into_iter().max_by_key(|e| e.weight) {
        client
            .publish_diagnostics(
                uri.clone(),
                reduced_err[..]
                    .iter()
                    .rev()
                    .filter(|e| e.weight == max.weight)
                    .map(|i| i.clone().diagnostic())
                    .collect(),
                None,
            )
            .await;
    } else {
        client.publish_diagnostics(uri.clone(), vec![], None).await;
    }
}
//Walk the syntax tree and only go "down" if F is true
fn ts_filterd_visit<F: FnMut(Node) -> bool>(root: Node, mut f: F) {
    let mut reached_root = false;
    let mut cursor = root.walk();
    if !cursor.goto_first_child() {
        return;
    }
    while !reached_root {
        if f(cursor.node()) && cursor.goto_first_child() {
            continue;
        }
        if cursor.goto_next_sibling() {
            continue;
        }
        loop {
            if !cursor.goto_parent() {
                reached_root = true;
                break;
            }
            if cursor.node() == root {
                reached_root = true;
                break;
            }
            if cursor.goto_next_sibling() {
                break;
            }
        }
    }
}
//Check if line breaks are correct eg. inside parenthesis
//This is necessary because the treesitter grammer allows 2 features on the same line under certain
//conditions.
pub fn check_sanity(tree: &Tree, source: &Rope) -> Vec<ErrorInfo> {
    let time = Instant::now();
    let mut cursor = QueryCursor::new();
    let mut error = Vec::new();
    let mut lines = HashMap::new();
    for i in cursor.matches(
        &TS.queries.check_sanity,
        tree.root_node(),
        node_source(source),
    ) {
        let node = i.captures[0].node;
        //We have to check if line breaks in expression are contained by a parenthesis
        if node.kind() == "expr" {
            if node.start_position().row == node.end_position().row {
                continue;
            } else {
                let mut ok_lines = Vec::new();
                ts_filterd_visit(node, |node| {
                    if node.kind() == "nested_expr" {
                        for i in node.start_position().row..node.end_position().row {
                            ok_lines.push(i);
                        }
                        false
                    } else {
                        true
                    }
                });
                for i in node.start_position().row..node.end_position().row {
                    if !ok_lines.iter().any(|k| *k == i) {
                        error.push(ErrorInfo {
                            weight: 100,
                            location: node_range(node, source),
                            severity: DiagnosticSeverity::ERROR,
                            msg: "line breaks are only allowed inside parenthesis".to_string(),
                            error_type: ErrorType::Any,
                        });
                    }
                }
            }
        } else if i.pattern_index == 0 {
            //Header
            if node.start_position().row != node.end_position().row {
                error.push(ErrorInfo {
                    weight: 100,
                    location: node_range(node, source),
                    severity: DiagnosticSeverity::ERROR,
                    msg: "line breaks are only allowed inside parenthesis".to_string(),
                    error_type: ErrorType::Any,
                });
            }
            if lines.insert(node.start_position().row, node).is_some() {
                error.push(ErrorInfo {
                    weight: 100,
                    location: node_range(node, source),
                    severity: DiagnosticSeverity::ERROR,
                    msg: "features have to be in different lines".to_string(),
                    error_type: ErrorType::Any,
                });
            }
        } else {
            //check name or string since quoted names allow line breaks in ts but should not
            if node.start_position().row != node.end_position().row {
                error.push(ErrorInfo {
                    weight: 100,
                    location: node_range(node, source),
                    severity: DiagnosticSeverity::ERROR,
                    msg: "multiline strings are not supported".to_string(),
                    error_type: ErrorType::Any,
                });
            }
        }
    }
    info!(" check sanity in {:?}", time.elapsed());
    error
}

pub fn classify_error(root: Node, source: &Rope) -> ErrorInfo {
    let err_source = source.byte_slice(root.byte_range());
    if root.start_position().row == root.end_position().row {
        let err_raw: String = err_source.into();
        if err_raw.contains("=>")
            || err_raw.contains("<=>")
            || err_raw.contains('&')
            || err_raw.contains('|')
            || err_raw.contains('+')
            || err_raw.contains('-')
            || err_raw.contains('*')
            || err_raw.contains('/')
            || err_raw.contains('>')
            || err_raw.contains('<')
            || err_raw.contains("==")
        {
            return ErrorInfo {
                location: node_range(root, source),
                severity: DiagnosticSeverity::ERROR,
                weight: 80,
                msg: "missing lhs or rhs expression".into(),
                error_type: ErrorType::Any,
            };
        }
    }
    ErrorInfo {
        location: node_range(root, source),
        severity: DiagnosticSeverity::ERROR,
        weight: 80,
        msg: "unknown syntax error".into(),
        error_type: ErrorType::Any,
    }
}
pub fn check_errors(tree: &Tree, source: &Rope) -> Vec<ErrorInfo> {
    let mut err: Vec<ErrorInfo> = Vec::new();
    ts_filterd_visit(tree.root_node(), |i| {
        if i.is_missing() {
            err.push(ErrorInfo {
                location: node_range(i, source),
                severity: DiagnosticSeverity::ERROR,
                weight: 80,
                msg: format!("missing {}", i.kind()),
                error_type: ErrorType::Any,
            });
            false
        } else if i.is_error() {
            err.push(classify_error(i, source));
            false
        } else {
            true
        }
    });
    err
}
#[derive(Debug, Clone)]
pub struct DiagnosticUpdate {
    pub error_state: HashMap<FileID, Vec<ErrorInfo>>,
    pub timestamp: u64,
}

struct DiagnosticState {
    timestamp: u64,
    error: Vec<ErrorInfo>,
}
async fn maybe_publish(
    client: &Client,
    source_map: &mut HashMap<FileID, DiagnosticState>,
    uri: FileID,
    mut err: Vec<ErrorInfo>,
    timestamp: u64,
) {
    if let Some(old) = source_map.get_mut(&uri) {
        if old.timestamp < timestamp {
            publish(client, &uri.url(), &err).await;
            old.timestamp = timestamp;
            old.error = err;
        } else if old.timestamp == timestamp {
            old.timestamp = timestamp;
            old.error.append(&mut err);
            publish(client, &uri.url(), &old.error).await;
        }
    } else {
        publish(client, &uri.url(), &err).await;
        source_map.insert(
            uri,
            DiagnosticState {
                timestamp,
                error: err,
            },
        );
    }
}

pub async fn diagnostic_handler(mut rx: mpsc::Receiver<DiagnosticUpdate>, client: Client) {
    let mut source_map: HashMap<FileID, DiagnosticState> = HashMap::new();
    while let Some(mut update) = rx.recv().await {
        for (uri, err) in update.error_state.drain() {
            if uri.is_virtual() {
                continue;
            }
            maybe_publish(&client, &mut source_map, uri, err, update.timestamp).await
        }
    }
}
pub fn check_includes(_doc: &AstDocument) -> Vec<ErrorInfo> {
    Default::default()
}
//Used to gather errors in compiler stages
pub struct ErrorsAcc<'a> {
    pub errors: HashMap<FileID, Vec<ErrorInfo>>,
    pub files: &'a AstFiles,
    pub configs: &'a ConfigFiles,
}
impl<'a> ErrorsAcc<'a> {
    pub fn new(root: &'a RootGraph) -> Self {
        Self {
            errors: HashMap::new(),
            files: &root.files,
            configs: &root.configs,
        }
    }
    pub fn has_error(&self, file: FileID) -> bool {
        self.errors
            .get(&file)
            .map(|u| !u.is_empty())
            .unwrap_or(false)
    }
    pub fn sym<S: Into<String>>(&mut self, sym: Symbol, file: FileID, weight: u32, s: S) {
        insert_multi(
            &mut self.errors,
            file,
            ErrorInfo {
                location: self.files[&file].lsp_range(sym).unwrap(),
                severity: DiagnosticSeverity::ERROR,
                weight,
                msg: s.into(),
                error_type: ErrorType::Any,
            },
        );
    }

    pub fn sym_info<S: Into<String>>(&mut self, sym: Symbol, file: FileID, weight: u32, s: S) {
        insert_multi(
            &mut self.errors,
            file,
            ErrorInfo {
                location: self.files[&file].lsp_range(sym).unwrap(),
                severity: DiagnosticSeverity::INFORMATION,
                weight,
                msg: s.into(),
                error_type: ErrorType::Any,
            },
        );
    }
    pub fn span<S: Into<String>>(&mut self, span: Span, file: FileID, weight: u32, s: S) {
        let source = self
            .configs
            .get(&file)
            .map(|i| &i.source)
            .or_else(|| self.files.get(&file).map(|i| &i.source))
            .unwrap();
        insert_multi(
            &mut self.errors,
            file,
            ErrorInfo {
                location: lsp_range(span, &source).unwrap(),
                severity: DiagnosticSeverity::ERROR,
                weight,
                msg: s.into(),
                error_type: ErrorType::Any,
            },
        );
    }

    pub fn span_info<S: Into<String>>(&mut self, span: Span, file: FileID, weight: u32, s: S) {
        let source = self
            .configs
            .get(&file)
            .map(|i| &i.source)
            .or_else(|| self.files.get(&file).map(|i| &i.source))
            .unwrap();
        insert_multi(
            &mut self.errors,
            file,
            ErrorInfo {
                location: lsp_range(span, &source).unwrap(),
                severity: DiagnosticSeverity::INFORMATION,
                weight,
                msg: s.into(),
                error_type: ErrorType::Any,
            },
        );
    }
}
