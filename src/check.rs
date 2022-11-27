use itertools::Itertools;
use log::info;
use rayon::prelude::{IndexedParallelIterator, IntoParallelRefIterator};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use tokio_util::sync::CancellationToken;

use tokio::sync::mpsc;

use rayon::prelude::*;
use tokio::time::{Duration, Instant};
use tokio::{select, spawn};
use tower_lsp::lsp_types::{Diagnostic, DiagnosticSeverity, PublishDiagnosticsParams, Range, Url};
use tower_lsp::Client;
use tree_sitter::{Node, Query, QueryCapture, QueryCursor, QueryMatch, TreeCursor};

use crate::{module, semantic, util::*};
use ustr::Ustr;

use crate::semantic::{FileGraph, RootGraph, RootSymbolID, SymbolID, SymbolRef, Type, TS};

#[derive(Clone, Debug)]
struct ErrorInfo {
    location: Range,
    severity: DiagnosticSeverity,
    weight: u32,
    msg: String,
}

impl ErrorInfo {
    fn diagnostic(self) -> Diagnostic {
        Diagnostic {
            range: self.location,
            severity: Some(self.severity),
            message: self.msg,
            ..Default::default()
        }
    }
}
fn ts_filterd_visit<F: FnMut(Node) -> bool>(root: Node, mut f: F) {
    let mut reached_root = false;
    let mut cursor = root.walk();
    if !cursor.goto_first_child() {
        return;
    }
    while !reached_root {
        if f(cursor.node()) {
            if cursor.goto_first_child() {
                continue;
            }
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
//Check if line breaks are correct eg inside parenthesis
fn check_sanity(file: &FileGraph) -> Vec<ErrorInfo> {
    let time = Instant::now();
    let mut cursor = QueryCursor::new();
    let mut error = Vec::new();
    let mut lines = HashMap::new();
    for i in cursor.matches(
        &TS.queries.check_sanity,
        file.tree.root_node(),
        file.source.as_bytes(),
    ) {
        let node = i.captures[0].node;
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
                    if ok_lines.iter().find(|k| **k == i).is_none() {
                        error.push(ErrorInfo {
                            weight: 100,
                            location: node_range(node),
                            severity: DiagnosticSeverity::ERROR,
                            msg: "Line breaks are only allowed inside parenthesis".to_string(),
                        });
                    }
                }
            }
        } else if i.pattern_index == 0 {
            if node.start_position().row != node.end_position().row {
                error.push(ErrorInfo {
                    weight: 100,
                    location: node_range(node),
                    severity: DiagnosticSeverity::ERROR,
                    msg: "Line breaks are only allowed inside parenthesis".to_string(),
                });
            }
            if lines.insert(node.start_position().row, node).is_some() {
                error.push(ErrorInfo {
                    weight: 100,
                    location: node_range(node),
                    severity: DiagnosticSeverity::ERROR,
                    msg: "Features have to be in diffrent lines".to_string(),
                });
            }
        } else {
            if node.start_position().row != node.end_position().row {
                error.push(ErrorInfo {
                    weight: 100,
                    location: node_range(node),
                    severity: DiagnosticSeverity::ERROR,
                    msg: "multiline strings are not supported".to_string(),
                });
            }
        }
    }
    info!(" check sanity in {:?}", time.elapsed());
    error
}
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum DeclContext {
    Import,
    Feature,
    Include,
    Constraints,
    Value,
    Root,
}
fn get_context(node: Node) -> DeclContext {
    match node.kind() {
        "source_file" => DeclContext::Root,
        "features" => DeclContext::Feature,
        "include" => DeclContext::Include,
        "constraints" => DeclContext::Include,
        "value" => DeclContext::Value,
        _ => get_context(node.parent().unwrap()),
    }
}

//A set of logic rules to detect sytax errors in the green tree
fn check_blk_types(parent: Node, child: Node, file: &FileGraph) -> Option<ErrorInfo> {
    let has_children = child
        .parent()
        .unwrap()
        .child_by_field_name("child")
        .is_some();
    let has_attributes = child
        .parent()
        .unwrap()
        .child_by_field_name("attribs")
        .is_some();
    match (parent.kind(), child.kind()) {
        ("constraints", sub) if sub != "expr" && sub != "ref" && sub != "name" => Some(ErrorInfo {
            location: node_range(child),
            severity: DiagnosticSeverity::ERROR,
            weight: 20,
            msg: "only constraints are allowed here".to_string(),
        }),
        ("constraints", sub) if has_children || has_attributes => Some(ErrorInfo {
            location: node_range(child),
            severity: DiagnosticSeverity::ERROR,
            weight: 20,
            msg: "constraints may not have any children or attributes".to_string(),
        }),
        ("imports", sub) if sub != "name" && sub != "ref" => Some(ErrorInfo {
            location: node_range(child),
            severity: DiagnosticSeverity::ERROR,
            weight: 20,
            msg: "only imports are allowed here".to_string(),
        }),
        ("imports", sub) if has_children || has_attributes => Some(ErrorInfo {
            location: node_range(child),
            severity: DiagnosticSeverity::ERROR,
            weight: 20,
            msg: "imports may not have any children or attributes".to_string(),
        }),
        ("include", sub) if sub != "lang_lvl" => Some(ErrorInfo {
            location: node_range(child),
            severity: DiagnosticSeverity::ERROR,
            weight: 20,
            msg: "only language levels are allowed here".to_string(),
        }),
        ("include", sub) if has_children || has_attributes => Some(ErrorInfo {
            location: node_range(child),
            severity: DiagnosticSeverity::ERROR,
            weight: 20,
            msg: "includes may not have any children or attributes".to_string(),
        }),
        (root, "lang_lvl") if root != "include" => Some(ErrorInfo {
            location: node_range(child),
            severity: DiagnosticSeverity::ERROR,
            weight: 20,
            msg: "language levels are only allowed inside a include block".to_string(),
        }),
        (_, "namespace")
        | (_, "constraints")
        | (_, "features")
        | (_, "include")
        | (_, "imports") => Some(ErrorInfo {
            location: node_range(child),
            severity: DiagnosticSeverity::ERROR,
            weight: 20,
            msg: format!("{} block only allowed at document root", child.kind()),
        }),
        ("group_mode", "group_mode") => Some(ErrorInfo {
            location: node_range(child),
            severity: DiagnosticSeverity::ERROR,
            weight: 20,
            msg: "expected a feature".to_string(),
        }),

        (_, "group_mode") if has_attributes || has_attributes => Some(ErrorInfo {
            location: node_range(child),
            severity: DiagnosticSeverity::ERROR,
            weight: 20,
            msg: "groups may not have any children or attributes".to_string(),
        }),
        ("name", "name") | ("ref", "name") | ("name", "ref") | ("ref", "ref") => Some(ErrorInfo {
            location: node_range(child),
            severity: DiagnosticSeverity::ERROR,
            weight: 20,
            msg: "features have to be seperated by a group".to_string(),
        }),
        (root, "ref") if child.child_by_field_name("alias").is_some() && root != "imports" => {
            Some(ErrorInfo {
                location: node_range(child),
                severity: DiagnosticSeverity::ERROR,
                weight: 20,
                msg: "alias only allowed inside a import block".to_string(),
            })
        }
        (root, "expr") if root != "constraints" => Some(ErrorInfo {
            location: node_range(child),
            severity: DiagnosticSeverity::ERROR,
            weight: 20,
            msg: "constrainst are only allowed inside a constraint block".to_string(),
        }),
        ("namespace", _) => Some(ErrorInfo {
            location: node_range(child),
            severity: DiagnosticSeverity::ERROR,
            weight: 20,
            msg: "namespace may not have any children".to_string(),
        }),
        _ => None,
    }
}
fn check_root_blk<'a>(
    node: Node<'a>,
    history: &mut Vec<Node<'a>>,
    file: &FileGraph,
) -> Option<ErrorInfo> {
    match node.kind() {
        "namespace" | "features" | "include" | "imports" | "constraints" => {
            if let Some(other) = history.iter().find(|i| i.kind() == node.kind()) {
                Some(ErrorInfo {
                    location: node_range(node),
                    severity: DiagnosticSeverity::ERROR,
                    weight: 30,
                    msg: format!("duplicate {}", node.kind()),
                })
            } else {
                history.push(node);
                None
            }
        }
        _ => Some(ErrorInfo {
            location: node_range(node),
            severity: DiagnosticSeverity::ERROR,
            weight: 30,
            msg: "only namespace, features, imports, include and constraints are allowed here"
                .to_string(),
        }),
    }
}
fn check_syntax(file: &FileGraph) -> Vec<ErrorInfo> {
    let time = Instant::now();
    let mut cursor = QueryCursor::new();
    let mut err: Vec<ErrorInfo> = Vec::new();
    let mut error_nodes = HashSet::new();
    let mut root_blks = Vec::new();
    for m in cursor.matches(
        &TS.queries.check_syntax,
        file.tree.root_node(),
        file.source.as_bytes(),
    ) {
        match m.pattern_index {
            0 => err.push(ErrorInfo {
                location: node_range(m.captures[0].node),
                severity: DiagnosticSeverity::WARNING,
                weight: 1,
                msg: "tailing dots are not supported".to_string(),
            }),
            1 => {
                err.push(ErrorInfo {
                    location: node_range(m.captures[0].node),
                    severity: DiagnosticSeverity::ERROR,
                    weight: 50,
                    msg: "Missing LHS or RHS argument".to_string(),
                });
                error_nodes.insert(m.captures[0].node);
            }
            2 => {
                if let Some(e) = check_blk_types(m.captures[0].node, m.captures[1].node, file) {
                    err.push(e);
                }
            }
            3 => {
                if let Some(e) = check_root_blk(m.captures[0].node, &mut root_blks, file) {
                    err.push(e)
                }
            }
            4 => {
                err.push(ErrorInfo {
                    location: node_range(m.captures[0].node),
                    severity: DiagnosticSeverity::ERROR,
                    weight: 60,
                    msg: if m.captures[0].node.kind() == "incomplete_ref" {
                        "incomplete alias".to_string()
                    } else {
                        "incomplete namespace".to_string()
                    },
                });
            }

            _ => {}
        }
    }
    for i in tree_sitter_traversal::traverse_tree(&file.tree, tree_sitter_traversal::Order::Pre) {
        if i.is_missing() {
            err.push(ErrorInfo {
                location: node_range(i),
                severity: DiagnosticSeverity::WARNING,
                weight: 80,
                msg: format!("missing {}", i.kind()),
            })
        }
        if i.is_error() && !error_nodes.contains(&i) {
            err.push(ErrorInfo {
                location: node_range(i),
                severity: DiagnosticSeverity::ERROR,
                weight: 80,
                msg: "unknown syntax error".into(),
            });
        }
    }
    let root_order = &["namespace", "include", "imports", "features", "constraints"];
    for i in 1..root_blks.len() {
        let (pi, _) = root_order
            .iter()
            .find_position(|k| *k == &root_blks[i - 1].kind())
            .unwrap();
        let (ni, _) = root_order
            .iter()
            .find_position(|k| *k == &root_blks[i].kind())
            .unwrap();
        if pi > ni {
            err.push(ErrorInfo {
                location: node_range(root_blks[i]),
                severity: DiagnosticSeverity::ERROR,
                weight: 35,
                msg: format!(
                    "{} may not be after {} ",
                    root_blks[i].kind(),
                    root_blks[i - 1].kind()
                ),
            });
        }
    }
    info!("checked syntax in {:?}", time.elapsed());
    err
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum ValidationState {
    Unknown,
    Sane,
    Valid,
}

#[derive(Debug, Clone)]
pub struct DocumentState {
    err: Vec<ErrorInfo>,
    validation: ValidationState,
    uri: Url,
}
impl DocumentState {
    pub fn valid(&self) -> bool {
        self.validation == ValidationState::Valid
    }
    pub fn sane(&self) -> bool {
        self.validation >= ValidationState::Sane
    }
    pub async fn publish(&self, client: &Client) {
        if let Some(max) = self.err.last().map(|e| e.weight) {
            client
                .publish_diagnostics(
                    self.uri.clone(),
                    self.err
                        .iter()
                        .rev()
                        .take_while(|e| e.weight == max)
                        .map(|i| i.clone().diagnostic())
                        .collect(),
                    None,
                )
                .await;
        } else {
            client
                .publish_diagnostics(self.uri.clone(), vec![], None)
                .await;
        }
    }
}
pub fn check_document(file: &FileGraph) -> DocumentState {
    let mut err = check_sanity(file);
    if err.len() > 0 {
        err.sort_by_key(|e| e.severity);
        return DocumentState {
            uri: file.uri.clone(),
            validation: ValidationState::Unknown,
            err,
        };
    }

    err = check_syntax(file);
    if err.len() > 0 {
        err.sort_by_key(|e| e.severity);
        return DocumentState {
            uri: file.uri.clone(),
            validation: ValidationState::Sane,
            err,
        };
    }
    DocumentState {
        uri: file.uri.clone(),
        err,
        validation: ValidationState::Valid,
    }
}

fn check_references(file: &FileGraph, root: &RootGraph) -> Vec<ErrorInfo> {
    let mut err = Vec::new();
    for i in file.store.references.iter() {
        enum ErrState {
            NotFound,
            WrongAttribKind(Type),
            FoundFeature,
            FoundAttrib,
            Success,
        }
        let mut state = ErrState::NotFound;
        root.resolve(file.name, &i.path.names, |sym| match sym {
            RootSymbolID::Symbol(tgt, tgt_id) => {
                match root.files[&tgt].store.get(tgt_id).unwrap() {
                    SymbolRef::Feature(_) => {
                        if i.ty == Type::Feature {
                            state = ErrState::Success;
                            Some(())
                        } else {
                            state = ErrState::FoundFeature;
                            None
                        }
                    }
                    SymbolRef::Attribute(attrib) => {
                        if attrib.ty != Type::Number {
                            state = ErrState::WrongAttribKind(attrib.ty);
                            None
                        } else if i.ty == Type::Feature {
                            state = ErrState::FoundAttrib;
                            None
                        } else {
                            state = ErrState::Success;
                            Some(())
                        }
                    }
                    _ => None,
                }
            }
            _ => None,
        });
        match state {
            ErrState::NotFound => {
                err.push(ErrorInfo {
                    location: lsp_range(i.path.range(), &file.rope).unwrap(),
                    severity: DiagnosticSeverity::ERROR,
                    weight: 10,
                    msg: "unresolved reference".to_string(),
                });
            }
            ErrState::FoundAttrib => {
                err.push(ErrorInfo {
                    location: lsp_range(i.path.range(), &file.rope).unwrap(),
                    severity: DiagnosticSeverity::ERROR,
                    weight: 9,
                    msg: "expected feature found attribute".to_string(),
                });
            }
            ErrState::FoundFeature => {
                err.push(ErrorInfo {
                    location: lsp_range(i.path.range(), &file.rope).unwrap(),
                    severity: DiagnosticSeverity::ERROR,
                    weight: 9,
                    msg: "expected attribute found feature".to_string(),
                });
            }
            ErrState::WrongAttribKind(kind) => {
                err.push(ErrorInfo {
                    location: lsp_range(i.path.range(), &file.rope).unwrap(),
                    severity: DiagnosticSeverity::ERROR,
                    weight: 9,
                    msg: format!("wrong attribute type {:?}", kind),
                });
            }
            _ => {}
        }
    }
    for i in file.store.imports.iter() {
        if root
            .resolve(file.name, &i.path.names, |sym| match sym {
                RootSymbolID::Symbol(..) => None,
                RootSymbolID::Module(m) => match &root.modules[m] {
                    module::Content::File(..) => Some(()),
                    _ => None,
                },
            })
            .is_none()
        {
            err.push(ErrorInfo {
                location: lsp_range(i.path.range(), &file.rope).unwrap(),
                severity: DiagnosticSeverity::ERROR,
                weight: 11,
                msg: format!("unresolved import"),
            });
        }
    }
    err
}
pub async fn fininalize(
    root: RootGraph,
    state: HashMap<Ustr, DocumentState>,
    dirty: Vec<Ustr>,
    ctx: Arc<semantic::Context>,
    revision: u64,
) {
    let all_valid = state.iter().all(|(_, v)| v.valid());
    if all_valid {
        //TODO this is super costly for large projects find a better way
        let time = Instant::now();
        let all_files: Vec<_> = root.files.keys().collect();
        let results: Vec<_> = all_files
            .par_iter()
            .map(|&name| DocumentState {
                err: check_references(&root.files[name], &root),
                validation: ValidationState::Valid,
                uri: root.files[name].uri.clone(),
            })
            .collect();
        info!("Checked all references in {:?}", time.elapsed());
        if revision
            == ctx
                .revison_counter
                .load(std::sync::atomic::Ordering::SeqCst)
        {
            for i in results {
                i.publish(&ctx.client).await
            }
        }
    } else {
        for i in dirty.iter() {
            state[i].publish(&ctx.client).await;
        }
    }
}
