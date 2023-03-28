use std::{collections::BTreeMap, fmt::Display};

use crate::{
    ast::*,
    check::ErrorInfo,
    completion::*,
    parse::SymbolSlice,
    semantic::{FileID, RootGraph},
    util::*,
};
use itertools::Itertools;
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

#[derive(Debug, Clone, PartialEq)]
pub enum ConfigEntry {
    Value(Path, ConfigValue),
    Import(Path, Vec<ConfigEntry>),
}

impl Serialize for ConfigEntry {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        use serde::ser::SerializeMap;
        info!("{self:?}");

        match self {
            ConfigEntry::Value(..) => panic!(),
            ConfigEntry::Import(_, v) => {
                let mut s = serializer.serialize_map(Some(v.len()))?;
                for i in v.iter() {
                    match i {
                        ConfigEntry::Value(p, k) => {
                            s.serialize_entry(&p.to_string(), k)?;
                        }
                        ConfigEntry::Import(p, _) => {
                            s.serialize_entry(p, i)?;
                        }
                    }
                }
                s.end()
            }
        }
    }
}

impl ConfigEntry {
    pub fn is_empty(&self) -> bool {
        match self {
            ConfigEntry::Value(..) => true,
            ConfigEntry::Import(_, v) => v.is_empty(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct FileConfig {
    pub file: FileID,
    pub file_span: Span,
    pub config: Vec<ConfigEntry>,
}

impl Serialize for Path {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(&self.names.iter().map(|i| i.as_str()).join("."))
    }
}

#[derive(Debug)]
pub struct ConfigDocument {
    pub config: Option<FileConfig>,
    pub source: Rope,
    pub uri: Url,
    pub timestamp: Instant,
    pub syntax_errors: Vec<ErrorInfo>,
    pub path: Vec<Ustr>,
    pub id: FileID,
}
struct State<'a> {
    err: Vec<ErrorInfo>,
    cursor: TreeCursor<'a>,
    source: &'a Rope,
    owner: FileID,
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

fn opt_configs(state: &mut State) -> Vec<ConfigEntry> {
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
                        acc.push(ConfigEntry::Value(key, ConfigValue::Bool(true)));
                    }

                    "false" => {
                        acc.push(ConfigEntry::Value(key, ConfigValue::Bool(false)));
                    }
                    "number" => {
                        if let Ok(num) = state.source.slice_raw(val.byte_range()).parse() {
                            acc.push(ConfigEntry::Value(key, ConfigValue::Number(num)));
                        } else {
                            state.push_error_node(val, 30, "cant parse number");
                        }
                    }
                    "string" => {
                        let text = state
                            .source
                            .slice_raw(val.start_byte() + 1..val.end_byte() - 1)
                            .replace(r#"\""#, "\"");
                        acc.push(ConfigEntry::Value(key, ConfigValue::String(text)));
                    }
                    "object" => {
                        let children = stacker::maybe_grow(32 * 1024, 1024 * 1024, || {
                            visit_children(state, |state| {
                                state.goto_field("value");
                                visit_children(state, opt_configs)
                            })
                        });
                        acc.push(ConfigEntry::Import(key, children));
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
fn visit_file(state: &mut State) -> Option<FileConfig> {
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
                            file = Some((
                                state
                                    .source
                                    .slice(val.named_child(0).unwrap().byte_range())
                                    .to_string(),
                                val.byte_range(),
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
        if let Some((file, span)) = file {
            let config = config.unwrap_or(Vec::new());
            let mut dir = state
                .owner
                .url()?
                .to_file_path()
                .ok()?
                .parent()?
                .to_path_buf();
            dir.push(file);
            Some(FileConfig {
                file: FileID::new(&format!("file://{}", dir.to_str()?)),
                file_span: span,
                config,
            })
        } else {
            state.push_error(40, "missing file key");
            None
        }
    })
}
fn visit_root(state: &mut State) -> Option<FileConfig> {
    state.goto_first_child();
    if state.kind() == "object" {
        visit_file(state)
    } else {
        state.push_error(40, "expected file object");
        None
    }
}
pub fn parse_json(tree: Tree, source: Rope, uri: Url, timestamp: Instant) -> ConfigDocument {
    let id = FileID::new(uri.as_str());
    let (file, err) = {
        let mut state = State {
            cursor: tree.walk(),
            err: Vec::new(),
            source: &source,
            owner: id,
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
            (None, state.err)
        } else {
            (visit_root(&mut state), state.err)
        }
    };
    ConfigDocument {
        syntax_errors: err,
        path: uri_to_path(&uri).unwrap(),
        config: file,
        id,
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
    ctx.reverse();
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
                info!("{slice}");
                info!("clean line");
                let start = slice
                    .char_indices()
                    .take_while(|(_, c)| c.is_whitespace())
                    .last()
                    .unwrap_or_default()
                    .0
                    + 1;
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
    let text_raw = text.slice(key.clone()).to_string().replace('\\', "");
    info!("{text_raw}");
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
pub fn estimate_env_json<'a>(
    _key_path: &[Ustr],
    tree: &Tree,
    source: &'a Rope,
    pos: &Position,
) -> Option<(CompletionEnv, Vec<std::borrow::Cow<'a, str>>)> {
    let offset = byte_offset(pos, source);
    let node = tree
        .root_node()
        .named_descendant_for_byte_range(offset, offset + 1)?;
    let path = json_path(node, source);
    info!("path {:?}", path);
    if path.len() >= 1 && path[0] == "config" {
        Some((CompletionEnv::ConfigEntryKey, path))
    } else if path.len() <= 1 {
        Some((CompletionEnv::ConfigRootKey, path))
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
            let (env, outer_path) = estimate_env_json(&path.names, tree, source, &pos)?;
            let prefix = outer_path
                .iter()
                .skip(1)
                .map(|i| Ustr::from(&*i))
                .chain(path.names.iter().cloned())
                .collect();

            if source.char(char) == '.' {
                Some(CompletionQuery {
                    offset: CompletionOffset::Dot,
                    env,
                    format: CompletionFormater::JSONKey {
                        postfix_range: lsp_range(key, source)?,
                    },
                    prefix,
                    postfix: CompactString::new_inline(""),
                })
            } else {
                Some(CompletionQuery {
                    offset: CompletionOffset::Continous,
                    env,
                    format: CompletionFormater::JSONKey {
                        postfix_range: lsp_range(
                            path.spans.last().cloned().unwrap_or(key),
                            source,
                        )?,
                    },
                    prefix: prefix[..prefix.len().saturating_sub(1)].to_vec(),
                    postfix: path.names.last().map(|s| s.as_str()).unwrap_or("").into(),
                })
            }
        }
        JSONItem::FreeKey(key) => {
            info!(" free {:?}", key);
            let path = parse_json_key(source, key.clone());
            info!("{path:?}");
            let (env, outer_path) = estimate_env_json(&path.names, tree, source, &pos)?;
            let prefix: Vec<Ustr> = outer_path
                .iter()
                .skip(1)
                .flat_map(|i| i.split(".").map(|i| i.replace('\\', "").into()))
                .chain(path.names.iter().cloned())
                .collect();
            Some(CompletionQuery {
                offset: CompletionOffset::Continous,
                env,
                format: CompletionFormater::FreeJSONKey {
                    whole_key: lsp_range(key, source)?,
                },
                prefix: prefix[..prefix.len().saturating_sub(1)].to_vec(),
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
            n.named_child(0).and_then(|base| {
                info!("JSON base is {:?}", base);
                let mut dir = uri.to_file_path().ok()?.parent()?.to_path_buf();
                dir.push(&*source.slice_raw(base.byte_range()));
                let id = FileID::new(Url::from_file_path(dir).unwrap().as_str());
                if root.containes_id(id) {
                    Some(id)
                } else {
                    None
                }
            })
        } else {
            None
        }
    })
}
