use itertools::Itertools;
use log::info;
use rayon::prelude::*;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::filegraph::{Symbol, Type, TS};
use tokio::time::Instant;
use tower_lsp::lsp_types::{Diagnostic, DiagnosticSeverity, Range, Url};
use tower_lsp::Client;
use tree_sitter::{Node, QueryCursor};

use crate::util::header_kind;
use crate::{semantic, util::*};
use ustr::Ustr;

use crate::filegraph::{FileGraph, SymbolKind};
use crate::semantic::RootGraph;

#[derive(Clone, Debug)]
pub struct ErrorInfo {
    pub location: Range,
    pub severity: DiagnosticSeverity,
    pub weight: u32,
    pub msg: String,
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
                            location: node_range(node, &file.rope),
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
                    location: node_range(node, &file.rope),
                    severity: DiagnosticSeverity::ERROR,
                    msg: "Line breaks are only allowed inside parenthesis".to_string(),
                });
            }
            if lines.insert(node.start_position().row, node).is_some() {
                error.push(ErrorInfo {
                    weight: 100,
                    location: node_range(node, &file.rope),
                    severity: DiagnosticSeverity::ERROR,
                    msg: "Features have to be in diffrent lines".to_string(),
                });
            }
        } else {
            if node.start_position().row != node.end_position().row {
                error.push(ErrorInfo {
                    weight: 100,
                    location: node_range(node, &file.rope),
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
struct Template {
    valid_children: Vec<SymbolKind>,
    allow_card: bool,
    allow_attribs: bool,
}
fn blk_template(blk: Node, file: &FileGraph) -> Template {
    if let Some(sym) = file.ts2sym.get(&blk.id()) {
        match sym.into() {
            SymbolKind::Feature => Template {
                valid_children: vec![SymbolKind::Group],
                allow_card: true,
                allow_attribs: true,
            },
            SymbolKind::Group => Template {
                valid_children: vec![SymbolKind::Feature, SymbolKind::Reference],
                allow_card: false,
                allow_attribs: false,
            },
            _ => Template {
                valid_children: vec![],
                allow_card: false,
                allow_attribs: false,
            },
        }
    } else {
        match header_kind(blk) {
            "include" => Template {
                valid_children: vec![SymbolKind::LangLvl],
                allow_card: false,
                allow_attribs: false,
            },
            "imports" => Template {
                valid_children: vec![SymbolKind::Import],
                allow_card: false,
                allow_attribs: false,
            },
            "features" => Template {
                valid_children: vec![SymbolKind::Feature, SymbolKind::Reference],
                allow_card: false,
                allow_attribs: false,
            },
            "constraints" => Template {
                valid_children: vec![SymbolKind::Constraint],
                allow_card: false,
                allow_attribs: false,
            },
            _ => Template {
                valid_children: vec![],
                allow_card: false,
                allow_attribs: false,
            },
        }
    }
}
fn symbol_name(kind: SymbolKind) -> &'static str {
    match kind {
        SymbolKind::Group => "group",
        SymbolKind::Reference => "reference",
        SymbolKind::LangLvl => "language level",
        SymbolKind::Constraint => "constraint",
        SymbolKind::Dir => "directory",
        SymbolKind::Bool => "bool",
        SymbolKind::Feature => "feature",
        SymbolKind::Import => "import",
        SymbolKind::Void => "void",
        SymbolKind::Number => "number",
        SymbolKind::String => "string",
        SymbolKind::Attributes => "attributes",
        SymbolKind::Root => "root",
        SymbolKind::Vector => "list",
    }
}
fn blk_name<'a>(blk: Node<'a>, file: &FileGraph) -> &'a str {
    if let Some(sym) = file.ts2sym.get(&blk.id()) {
        symbol_name(sym.into())
    } else {
        blk.child_by_field_name("header").unwrap().kind()
    }
}
fn blk_kind(blk: Node, file: &FileGraph) -> SymbolKind {
    if let Some(sym) = file.ts2sym.get(&blk.id()) {
        sym.into()
    } else {
        match header_kind(blk) {
            "ref" => SymbolKind::Reference,
            "name" => SymbolKind::Feature,
            "constraint" => SymbolKind::Constraint,
            _ => SymbolKind::Void,
        }
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
                    location: node_range(node, &file.rope),
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
            location: node_range(node, &file.rope),
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
                location: node_range(m.captures[0].node, &file.rope),
                severity: DiagnosticSeverity::WARNING,
                weight: 1,
                msg: "tailing dots are not supported".to_string(),
            }),
            1 => {
                err.push(ErrorInfo {
                    location: node_range(m.captures[0].node, &file.rope),
                    severity: DiagnosticSeverity::ERROR,
                    weight: 50,
                    msg: "Missing LHS or RHS argument".to_string(),
                });
                error_nodes.insert(m.captures[0].node);
            }
            2 => {}
            3 => {
                if let Some(e) = check_root_blk(m.captures[0].node, &mut root_blks, file) {
                    err.push(e)
                }
            }
            4 => {
                err.push(ErrorInfo {
                    location: node_range(m.captures[0].node, &file.rope),
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
                location: node_range(i, &file.rope),
                severity: DiagnosticSeverity::ERROR,
                weight: 80,
                msg: format!("missing {}", i.kind()),
            })
        }
        if i.is_error() && !error_nodes.contains(&i) {
            err.push(ErrorInfo {
                location: node_range(i, &file.rope),
                severity: DiagnosticSeverity::ERROR,
                weight: 80,
                msg: "unknown syntax error".into(),
            });
        }
        if i.kind() == "blk" {
            let template = blk_template(i, file);
            if i.child_by_field_name("cardinality").is_some() && !template.allow_card {
                err.push(ErrorInfo {
                    location: node_range(i.child_by_field_name("cardinality").unwrap(), &file.rope),
                    severity: DiagnosticSeverity::ERROR,
                    weight: 80,
                    msg: format!("{} may not have cardinality", blk_name(i, file)),
                });
            }
            if i.child_by_field_name("attribs").is_some() && !template.allow_card {
                err.push(ErrorInfo {
                    location: node_range(i.child_by_field_name("attribs").unwrap(), &file.rope),
                    severity: DiagnosticSeverity::ERROR,
                    weight: 40,
                    msg: format!("{} may not have attributes", blk_name(i, file)),
                });
            }
            if let Some(parent_blk) =
                i.parent()
                    .and_then(|p| if p.kind() == "blk" { Some(p) } else { None })
            {
                let parent_template = blk_template(parent_blk, file);

                if !parent_template.valid_children.contains(&blk_kind(i, file)) {
                    err.push(ErrorInfo {
                        location: node_range(i, &file.rope),
                        severity: DiagnosticSeverity::ERROR,
                        weight: 40,
                        msg: if parent_template.valid_children.is_empty() {
                            format!("{} may not have any children", blk_name(parent_blk, file))
                        } else {
                            format!(
                                "expected {}",
                                parent_template
                                    .valid_children
                                    .iter()
                                    .map(|sym| symbol_name(*sym))
                                    .join(" or ")
                            )
                        },
                    });
                }
            }
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
                location: node_range(root_blks[i], &file.rope),
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
    for i in file.parse_errors.iter() {
        err.push(i.clone());
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
    for i in file.references() {
        enum ErrState {
            NotFound,
            WrongAttribKind(SymbolKind),
            FoundFeature,
            FoundAttrib,
            Success,
        }
        let mut state = ErrState::NotFound;
        for r in root.resolve(file.name, &i.path.names) {
            match r.sym {
                Symbol::Feature(..) => {
                    if i.ty == Type::Feature {
                        state = ErrState::Success;
                        break;
                    } else {
                        state = ErrState::FoundFeature;
                    }
                }
                Symbol::Number(..) => {
                    if i.ty == Type::Feature {
                        state = ErrState::FoundAttrib;
                    } else {
                        state = ErrState::Success;
                        break;
                    }
                }
                _ if r.sym.is_value() => state = ErrState::WrongAttribKind(r.sym.into()),

                _ => {}
            }
        }
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
                    msg: format!("wrong attribute type {}", symbol_name(kind)),
                });
            }
            _ => {}
        }
    }
    for i in file.imports() {
        if root
            .fs
            .imports(file.name)
            .find(|(sym, _)| sym == &i)
            .is_none()
        {
            err.push(ErrorInfo {
                location: lsp_range(file.range(i), &file.rope).unwrap(),
                severity: DiagnosticSeverity::ERROR,
                weight: 11,
                msg: format!("unresolved import"),
            });
        }
    }
    for (a,b) in file.duplicate_symboles() {

        err.push(ErrorInfo {
            location: lsp_range(file.range(a), &file.rope).unwrap(),
            severity: DiagnosticSeverity::ERROR,
            weight: 7,
            msg: format!("duplicate {}",symbol_name(b.into())),
        });
        err.push(ErrorInfo {
            location: lsp_range(file.range(b), &file.rope).unwrap(),
            severity: DiagnosticSeverity::ERROR,
            weight: 7,
            msg: format!("duplicate {}",symbol_name(b.into())),
        });
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
