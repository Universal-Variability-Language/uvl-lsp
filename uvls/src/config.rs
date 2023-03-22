use std::{collections::BTreeMap, fmt::Display};

use crate::{
    ast::*,
    check::ErrorInfo,
    completion::*,
    parse::SymbolSlice,
    semantic::{FileID, RootGraph},
    util::*,
};
use log::info;
use ropey::Rope;
use serde::{Deserialize, Serialize};
use tokio::time::Instant;
use tower_lsp::lsp_types::*;
use tree_sitter::{Node, Tree, TreeCursor};
use ustr::Ustr;
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(untagged)]
pub enum ConfigValue {
    Bool(bool),
    Number(f64),
    String(String),
}
impl ConfigValue {
    pub fn ty(&self) -> Type {
        match self {
            Self::Bool(..) => Type::Bool,
            Self::Number(..) => Type::Real,
            Self::String(..) => Type::String,
        }
    }
    pub fn default(ty: Type) -> ConfigValue {
        match ty {
            Type::Bool => ConfigValue::Bool(false),
            Type::Real => ConfigValue::Number(0.0),
            Type::String => ConfigValue::String("".into()),
            _ => unimplemented!(),
        }
    }
    pub fn is_default(&self) -> bool {
        self == &Self::default(self.ty())
    }
}
impl Display for ConfigValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Bool(x) => write!(f, "{x}"),
            Self::Number(x) => write!(f, "{x}"),
            Self::String(x) => write!(f, "{x}"),
        }
    }
}
#[derive(Debug, Clone, Serialize, Deserialize)]
struct FileConfigRaw {
    file: String,
    config: BTreeMap<String, ConfigValue>,
}

#[derive(Debug, Clone)]
pub struct FileConfig {
    pub file: Path,
    pub config: Vec<(Path, ConfigValue)>,
}

#[derive(Debug)]
pub struct ConfigDocument {
    pub files: Vec<FileConfig>,
    pub source: Rope,
    pub uri: Url,
    pub timestamp: Instant,
    pub syntax_errors: Vec<ErrorInfo>,
    pub path: Vec<Ustr>,
    pub id: FileID,
}
struct State<'a> {
    files: Vec<FileConfig>,
    err: Vec<ErrorInfo>,
    cursor: TreeCursor<'a>,
    source: &'a Rope,
}
impl<'a> Visitor<'a> for State<'a> {
    fn cursor(&self) -> &TreeCursor<'a> {
        &self.cursor
    }
    fn cursor_mut(&mut self) -> &mut TreeCursor<'a> {
        &mut self.cursor
    }
    fn source(&self) -> &Rope {
        &self.source
    }
    fn push_err_raw(&mut self, err: ErrorInfo) {
        self.err.push(err);
    }
}

fn opt_configs(state: &mut State) -> Vec<(Path, ConfigValue)> {
    let mut acc = Vec::new();
    visit_siblings(state, |state| {
        if state.kind() == "pair" {
            if let Some(key) = state
                .child_by_name("key")
                .and_then(|k| k.named_child(0))
                .map(|k| parse_json_key(state.source, k.byte_range()))
            {
                let val = state.child_by_name("value").unwrap();
                match val.kind() {
                    "true" => {
                        acc.push((key, ConfigValue::Bool(true)));
                    }

                    "false" => {
                        acc.push((key, ConfigValue::Bool(false)));
                    }
                    "number" => {
                        if let Ok(num) = state.source.slice_raw(val.byte_range()).parse() {
                            acc.push((key, ConfigValue::Number(num)));
                        } else {
                            state.push_error_node(val, 30, "cant parse number");
                        }
                    }
                    "string" => {
                        let text = state
                            .source
                            .slice_raw(val.start_byte() + 1..val.end_byte() - 1)
                            .replace(r#"\""#, "\"");
                        acc.push((key, ConfigValue::String(text)));
                    }
                    _ => {
                        state.push_error_node(val, 30, "expected a number or bool");
                    }
                }
            }
        }
    });
    acc
}
fn visit_file(state: &mut State) {
    visit_children(state, |state| {
        let mut file = None;
        let mut config = None;
        visit_siblings(state, |state| {
            if state.kind() == "pair" {
                match state
                    .child_by_name("key")
                    .and_then(|k| k.named_child(0))
                    .map(|k| state.source.slice_raw(k.byte_range()))
                    .as_deref()
                {
                    Some("file") => {
                        let val = state.child_by_name("value").unwrap();
                        if val.kind() == "string" {
                            file = Some(parse_json_key(
                                state.source,
                                val.named_child(0).unwrap().byte_range(),
                            ))
                        } else {
                            state.push_error_node(val, 30, "expected string");
                        }
                    }
                    Some("config") => visit_children(state, |state| {
                        state.goto_field("value");
                        if state.kind() == "object" {
                            config = Some(visit_children(state, opt_configs));
                        } else {
                            state.push_error(30, "expected object");
                        }
                    }),
                    _ => {
                        state.push_error(40, "unknown key ");
                    }
                }
            }
        });
        if let Some(file) = file {
            let config = config.unwrap_or(Vec::new());
            state.files.push(FileConfig { file, config });
        } else {
            state.push_error(40, "missing file key");
        };
    })
}
fn visit_root(state: &mut State) {
    state.goto_first_child();

    if state.kind() == "array" {
        visit_children(state, |state| {
            visit_siblings(state, |state| {
                if state.kind() == "object" {
                    visit_file(state);
                } else if state.node().is_named() {
                    state.push_error(40, "expected a file object");
                }
            })
        })
    } else {
        state.push_error(40, "expected an array of files");
    }
}
pub fn parse_json(tree: Tree, source: Rope, uri: Url, timestamp: Instant) -> ConfigDocument {
    let (err, files) = {
        let mut state = State {
            cursor: tree.walk(),
            err: Vec::new(),
            files: Vec::new(),
            source: &source,
        };

        if tree_sitter_traversal::traverse_tree(&tree, tree_sitter_traversal::Order::Pre)
            .any(|n| n.is_error() || n.is_missing())
        {
            state.err.push(ErrorInfo {
                location: Range {
                    start: Position {
                        line: 0,
                        character: 0,
                    },
                    end: Position {
                        line: 0,
                        character: 0,
                    },
                },
                weight: 100,
                severity: DiagnosticSeverity::ERROR,
                msg: "JSON syntax errors".into(),
            });
        } else {
            visit_root(&mut state);
        }
        (state.err, state.files)
    };
    ConfigDocument {
        syntax_errors: err,
        path: uri_to_path(&uri).unwrap(),
        files,
        id: FileID::new(uri.as_str()),
        uri,
        timestamp,
        source,
    }
}

fn json_path<'a>(mut node: Node, rope: &'a Rope) -> Vec<std::borrow::Cow<'a, str>> {
    let mut ctx = Vec::new();
    while let Some(p) = node.parent() {
        if node.kind() == "object" && p.kind() == "pair" {
            if let Some(key) = p.child_by_field_name("key").and_then(|k| k.named_child(0)) {
                ctx.push(rope.slice(key.byte_range()).into())
            }
        }
        node = p;
    }
    ctx
}

fn selected_json_object<'a>(tree: &'a Tree, pos: &Position, source: &Rope) -> Option<Node<'a>> {
    let offset = byte_offset(pos, source);
    let mut node = tree
        .root_node()
        .named_descendant_for_byte_range(offset, offset + 1)?;
    let mut obj = None;

    loop {
        if node.kind() == "object" {
            obj = Some(node);
        }
        if let Some(p) = node.parent() {
            node = p;
        } else {
            return obj;
        }
    }
}

fn find_selected_json_key<'a>(
    tree: &'a Tree,
    pos: &Position,
    source: &Rope,
    key: &[Ustr],
) -> Option<Node<'a>> {
    selected_json_object(tree, pos, source).and_then(|obj| find_json_key(obj, source, key))
}

//Try to extract the selected json  value under KEY,
fn find_json_key<'a>(mut root: Node<'a>, source: &Rope, key: &[Ustr]) -> Option<Node<'a>> {
    for k in key {
        let mut cursor = root.walk();
        if cursor.goto_first_child() {
            loop {
                if let Some(name) = cursor.node().child_by_field_name("key") {
                    info!("found key {:?}", name);

                    if source.slice_raw(name.named_child(0)?.byte_range()) == k.as_str() {
                        root = cursor.node().child_by_field_name("value")?;

                        info!("set val {:?}", name);
                        break;
                    }
                }

                if !cursor.goto_next_sibling() {
                    return None;
                }
            }
        } else {
            return None;
        }
    }
    Some(root)
}
fn offset(span: Span, offset: usize) -> Span {
    span.start + offset..span.end + offset
}

#[derive(Debug)]
enum JSONItem {
    Key { key: Span, value: Option<Span> },
    Value { key: Span, value: Span },
    FreeKey(Span),
}
trait Overlaps {
    fn overlaps(&self, offset: usize) -> bool;
}
impl Overlaps for Span {
    fn overlaps(&self, offset: usize) -> bool {
        if self.start == self.end {
            (self.start.saturating_sub(1)..self.end).contains(&offset)
        } else {
            self.contains(&offset)
        }
    }
}
fn estimate_json_item(pos: &Position, source: &Rope) -> Option<JSONItem> {
    use lazy_static::lazy_static;
    use regex::Regex;
    lazy_static! {
        static ref RE: Regex =
            Regex::new(r#"((?:[^"\\]|\\.)*)"\s*:\s*("(?:[^"\\]|\\.)*|[+-]?(?:[0-9]*[.])?[0-9]+|[^\s:,}\n"\}\{]+)?"#)
                .unwrap();
    };
    let line = pos.line as usize;
    let slice: std::borrow::Cow<'_, _> = source.line(line).into();
    let start_byte = source.line_to_byte(line);
    let pos_byte = byte_offset(pos, source) - start_byte;
    info!("estimating json item in {}", slice);
    RE.captures(&slice)
        .iter()
        .find_map(|cap| {
            info!("Cap: {:#?} ", cap);

            match (cap.get(1), cap.get(2)) {
                (Some(key), Some(val)) => {
                    if key.range().overlaps(pos_byte) {
                        Some(JSONItem::Key {
                            key: offset(key.range(), start_byte),
                            value: Some(offset(val.range(), start_byte)),
                        })
                    } else if val.range().overlaps(pos_byte) {
                        Some(JSONItem::Value {
                            key: offset(key.range(), start_byte),
                            value: offset(val.range(), start_byte),
                        })
                    } else {
                        None
                    }
                }
                (Some(key), None) if key.range().overlaps(pos_byte) => Some(JSONItem::Key {
                    key: offset(key.range(), start_byte),
                    value: None,
                }),
                _ => None,
            }
        })
        .or_else(|| {
            lazy_static! {
                static ref RE: Regex = Regex::new(r#""((?:[^"\\]|\\.)*)""#).unwrap();
            };

            info!("no normal matches");

            RE.captures(&slice).iter().find_map(|cap| {
                info!("Cap: {:#?} ", cap);
                cap.get(1).and_then(|key| {
                    if key.range().overlaps(pos_byte) {
                        Some(JSONItem::Key {
                            key: offset(key.range(), start_byte),
                            value: None,
                        })
                    } else {
                        None
                    }
                })
            })
        })
        .or_else(|| {
            if slice
                .chars()
                .all(|c| c.is_alphanumeric() || c.is_whitespace() || c == '.')
            {
                info!("clean line");
                let start = slice
                    .char_indices()
                    .take_while(|(_, c)| c.is_whitespace())
                    .last()
                    .unwrap_or_default()
                    .0;
                let last = slice[start..]
                    .char_indices()
                    .take_while(|(_, c)| !c.is_whitespace())
                    .last()
                    .unwrap_or_default()
                    .0
                    + start;
                info!("P: {} {} {}", start, last, pos_byte);

                if (start..last + 1).contains(&pos_byte) {
                    Some(JSONItem::FreeKey(offset(start..last + 1, start_byte)))
                } else if start == last {
                    Some(JSONItem::FreeKey(offset(pos_byte..pos_byte, start_byte)))
                } else {
                    None
                }
            } else {
                None
            }
        })
}
fn parse_json_key(text: &Rope, key: Span) -> Path {
    //TODO this does not handle escaped strings with dots inside
    //decoding them is not determinstic so we should simply frobid them
    //or use a special token
    let text_raw = text.slice(key.clone()).to_string().replace('"', "");
    text_raw
        .split('.')
        .map(|i| {
            let rel_offset = i.as_ptr() as usize - text_raw.as_ptr() as usize;
            SymbolSpan {
                name: i.into(),
                span: offset(rel_offset..rel_offset + i.len(), key.start),
            }
        })
        .fold(Path::default(), |acc, i| acc.append(&i))
}
pub fn estimate_env_json(
    _key_path: &[Ustr],
    tree: &Tree,
    source: &Rope,
    pos: &Position,
) -> Option<CompletionEnv> {
    let offset = byte_offset(pos, source);
    let node = tree
        .root_node()
        .named_descendant_for_byte_range(offset, offset + 1)?;
    let path = json_path(node, source);
    info!("path {:?}", path);

    if path.len() >= 1 && path.len() <= 2 && path[0] == "config" {
        Some(CompletionEnv::ConfigEntryKey)
    } else if path.len() <= 1 {
        Some(CompletionEnv::ConfigRootKey)
    } else {
        None
    }
}
pub fn completion_query(source: &Rope, tree: &Tree, pos: &Position) -> Option<CompletionQuery> {
    use compact_str::CompactString;
    let pos = Position {
        character: pos.character.saturating_sub(1),
        line: pos.line,
    };
    let char = char_offset(&pos, source);
    let ctx = estimate_json_item(&pos, source);
    info!("{:#?}", ctx);
    match ctx? {
        JSONItem::Key { key, .. } => {
            let path = parse_json_key(source, key.clone());
            if source.char(char) == '.' {
                Some(CompletionQuery {
                    offset: CompletionOffset::Dot,
                    env: estimate_env_json(&path.names, tree, source, &pos)?,
                    format: CompletionFormater::JSONKey {
                        postfix_range: lsp_range(key, source)?,
                    },
                    prefix: path.names,
                    postfix: CompactString::new_inline(""),
                })
            } else {
                Some(CompletionQuery {
                    offset: CompletionOffset::Continous,
                    env: estimate_env_json(&path.names, tree, source, &pos)?,
                    format: CompletionFormater::JSONKey {
                        postfix_range: lsp_range(
                            path.spans.last().cloned().unwrap_or(key),
                            source,
                        )?,
                    },
                    prefix: path.names[..path.names.len().saturating_sub(1)].to_vec(),
                    postfix: path.names.last().map(|s| s.as_str()).unwrap_or("").into(),
                })
            }
        }
        JSONItem::FreeKey(key) => {
            info!(" free {:?}", key);
            let path = parse_json_key(source, key.clone());
            Some(CompletionQuery {
                offset: CompletionOffset::Continous,
                env: estimate_env_json(&path.names, tree, source, &pos)?,
                format: CompletionFormater::FreeJSONKey {
                    whole_key: lsp_range(key, source)?,
                },
                prefix: path.names[..path.names.len().saturating_sub(1)].to_vec(),
                postfix: path.names.last().map(|s| s.as_str()).unwrap_or("").into(),
            })
        }
        _ => None,
    }
}
pub fn find_file_id(
    source: &Rope,
    tree: &Tree,
    pos: &Position,
    uri: &Url,
    root: &RootGraph,
) -> Option<FileID> {
    find_selected_json_key(tree, pos, source, &["file".into()]).and_then(|n| {
        if n.kind() == "string" {
            n.named_child(0)
                .map(|n| parse_json_key(source, n.byte_range()))
                .and_then(|base| {
                    info!("JSON base is {:?}", base);
                    let path = uri_to_path(uri)?;
                    let abs_path = [&path[0..path.len() - 1], &base.names].concat();
                    root.fs().resolve_abs(&abs_path)
                })
        } else {
            None
        }
    })
}
