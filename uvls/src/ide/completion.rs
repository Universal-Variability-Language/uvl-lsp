use crate::core::*;
use compact_str::CompactString;
use hashbrown::HashMap;
use itertools::{Either, Itertools};
use log::info;
use regex::Regex;
use ropey::Rope;
use std::cmp::Ordering;
use std::ops::Add;
use tokio::time::Instant;
use tower_lsp::lsp_types::*;
use tree_sitter::{Node, Point, Tree};
use ustr::Ustr;
/*
 * All things completion related happen in here, the process is roughly as follows:
 * 1. Find the current context using the latest draft and editor position
 * 2. Find good completions in this context
 *
 * The completion context includes:
 *  - Meta information on the cursor position eg. Are we currently in a path or an empty line etc.
 *  - The semantic context eg. do we need a constraint or a number
 *  - A optional path prefix and suffix. The suffix is used as a weight for completions using the jaro
 *    winkler distance, the prefix is a filter restricting possible completions.
 *
 *  To weigh completions we use a simple weight function with hand picked weights for parameters
 *  like length or type correctness
 * */
static MAX_N: usize = 30;
static W_TYPE: f32 = 2.;
static W_LEN: f32 = 3.0;
static AVG_WEIGHT_THRESHOLD: f32 = 0.2; //Unused
static MIN_WEIGHT: f32 = 0.1;
struct TopN<V> {
    buffer: min_max_heap::MinMaxHeap<V>,
    max: usize,
}
impl<V> TopN<V>
where
    V: Ord,
{
    fn new(max: usize) -> Self {
        Self {
            buffer: min_max_heap::MinMaxHeap::new(),
            max,
        }
    }
    fn push(&mut self, value: V) {
        if self.max == 0 {
            return;
        }
        if self.buffer.len() >= self.max {
            let min = self.buffer.peek_min().unwrap();
            if value > *min {
                let _ = self.buffer.pop_min();
                self.buffer.push(value);
            }
        } else {
            self.buffer.push(value);
        }
    }
    fn into_sorted_vec(self) -> Vec<V> {
        self.buffer.into_vec_desc()
    }
    fn merge(&mut self, mut other: TopN<V>) {
        for i in other.buffer.drain() {
            self.push(i);
        }
    }
    fn best(&self) -> Option<&V> {
        self.buffer.peek_max()
    }
}

pub fn starts_with<T: PartialEq>(path: &[T], prefix: &[T]) -> bool {
    if path.len() < prefix.len() {
        false
    } else {
        path.iter().zip(prefix).all(|(i, k)| i == k)
    }
}

pub fn make_path<T: AsRef<str>, I: Iterator<Item = T>>(i: I) -> CompactString {
    let mut out = CompactString::new_inline("");
    for i in i.filter(|i| !i.as_ref().is_empty()) {
        if out.is_empty() {
            out.push_str(i.as_ref())
        } else {
            out.push('.');
            out.push_str(i.as_ref());
        }
    }
    out
}

//What kind of value is likely required to complete the expression
#[derive(PartialEq, Eq, Debug, Clone)]
pub enum CompletionEnv {
    Numeric,
    Constraint,
    GroupMode,
    Feature,
    Any,
    Toplevel,
    Import,
    SomeName,
    Include,
    ConfigEntryKey,
    ConfigRootKey,
    ConfigModelPath,
    ConfigEntryValue { target: Vec<Ustr> },
    Aggregate { context: Option<Path> },
}
impl CompletionEnv {
    //FIlter completions according to kind
    fn is_relevant(&self, kind: CompletionKind) -> bool {
        match self {
            Self::Feature => matches!(
                kind,
                CompletionKind::Feature
                    | CompletionKind::Import
                    | CompletionKind::Folder
                    | CompletionKind::File
            ),
            Self::Aggregate { .. } => matches!(
                kind,
                CompletionKind::Feature
                    | CompletionKind::Import
                    | CompletionKind::Folder
                    | CompletionKind::File
            ),
            _ => true, //Just pick anything
        }
    }
}

//Top level document section
#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Section {
    Imports,
    Include,
    Features,
    Constraints,
    TopLevel,
    Unknown,
    Attribute,
}
pub fn find_section(node: Node) -> Section {
    match node.kind() {
        "blk" => match node.child_by_field_name("header").unwrap().kind() {
            "constraints" => Section::Constraints,
            "include" => Section::Include,
            "imports" => Section::Imports,
            "features" => Section::Features,
            _ => find_section(node.parent().unwrap()),
        },
        "source_file" => Section::TopLevel,
        "attribute_constraint" | "attribute_constraints" => Section::Constraints,
        "binary_expr" | "unary_expr" | "nested_expr" | "function" => Section::Constraints,
        "attribute_value" => Section::Attribute,
        _ => {
            if let Some(p) = node.parent() {
                find_section(p)
            } else {
                Section::Unknown
            }
        }
    }
}

fn node_at<'a>(node: Node<'a>, line: usize, char: usize, source: &Rope) -> Node<'a> {
    let line_slice = source.line(line);
    let start = Point {
        row: line,
        column: line_slice.char_to_byte(char),
    };
    let end = Point {
        row: line,
        column: line_slice.char_to_byte(char + 1),
    };
    node.named_descendant_for_point_range(start, end).unwrap()
}

pub fn contains(range: Range, pos: &Position) -> bool {
    range.start.character <= pos.character && range.end.character > pos.character
}
//Finde the context inside a constraint
pub fn estimate_expr(node: Node, pos: &Position, source: &Rope) -> CompletionEnv {
    if node.is_error() && node.start_position().row == node.end_position().row {
        let err_raw: String = source.byte_slice(node.byte_range()).into();
        if err_raw.contains("=>")
            || err_raw.contains("<=>")
            || err_raw.contains('&')
            || err_raw.contains('|')
        {
            return CompletionEnv::Constraint;
        }
        if err_raw.contains('+')
            || err_raw.contains('-')
            || err_raw.contains('*')
            || err_raw.contains('/')
            || err_raw.contains('>')
            || err_raw.contains('<')
            || err_raw.contains("==")
        {
            return CompletionEnv::Numeric;
        }
    }
    match node.kind() {
        "number" => CompletionEnv::Numeric,
        "function" => {
            let mut cursor = node.walk();
            cursor.goto_first_child();
            let mut arg_offset = -1;
            let mut args = Vec::new();
            loop {
                if contains(
                    lsp_range(cursor.node().byte_range(), source).unwrap(),
                    &Position {
                        character: pos.character - 1,
                        line: pos.line,
                    },
                ) {
                    arg_offset = args.len() as isize;
                }
                if cursor.field_name().map(|i| i == "arg").unwrap_or(false) {
                    args.push(parse::parse_path(cursor.node(), source));
                }
                info!("{:?}", cursor.node().kind());
                if !cursor.goto_next_sibling() {
                    break;
                }
            }
            info!("args {:?} offset {}", &args, arg_offset);
            match node
                .child_by_field_name("op")
                .map(|op| source.slice_raw(op.byte_range()))
                .as_deref()
            {
                Some("sum" | "avg") => {
                    if arg_offset == 0 && args.len() > 1 {
                        CompletionEnv::Constraint
                    } else if args.len() == 1 && arg_offset == 0 {
                        CompletionEnv::Aggregate { context: None }
                    } else if arg_offset >= 1 {
                        CompletionEnv::Aggregate {
                            context: args[0].clone(),
                        }
                    } else {
                        CompletionEnv::Aggregate { context: None }
                    }
                }
                _ => CompletionEnv::Constraint,
            }
        }
        "binary_expr" => {
            let op: String = source
                .byte_slice(node.child_by_field_name("op").unwrap().byte_range())
                .into();
            match op.as_str() {
                "=>" | "&" | "|" | "<=>" => CompletionEnv::Constraint,
                _ => CompletionEnv::Numeric,
            }
        }
        "nested_expr" | "path" => estimate_expr(node.parent().unwrap(), pos, source),
        _ => CompletionEnv::Constraint,
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CompletionOffset {
    Continuous, // We are in path
    Dot,        //We are in open path ending with a dot
    SameLine,   // We are in a unfinished line
    Cut,        //We are in a empty line
}
//Search for context in the vicinity of the cursor
//first search one char back, then inside the line, then in the previous line etc.
fn position_to_node<'a>(
    source: &Rope,
    tree: &'a Tree,
    pos: &Position,
) -> (CompletionOffset, Node<'a>) {
    let line = source.line(pos.line as usize);
    let rel_char = line.utf16_cu_to_char(pos.character as usize);
    if rel_char == 0 {
        (CompletionOffset::SameLine, tree.root_node())
    } else {
        let base_offset = source.line_to_char(pos.line as usize);
        if !source.char(base_offset + rel_char - 1).is_whitespace() {
            (
                CompletionOffset::Continuous,
                node_at(tree.root_node(), pos.line as usize, rel_char - 1, source),
            )
        } else {
            for i in (0..rel_char - 1).rev() {
                if !source.char(base_offset + i).is_whitespace() {
                    return (
                        CompletionOffset::SameLine,
                        node_at(tree.root_node(), pos.line as usize, i, source),
                    );
                }
            }
            for i in (0..pos.line as usize).rev() {
                if !source
                    .char(source.line_to_char(i) + rel_char - 1)
                    .is_whitespace()
                {
                    return (
                        CompletionOffset::Cut,
                        node_at(tree.root_node(), i, rel_char - 1, source),
                    );
                }
            }

            (
                CompletionOffset::Cut,
                node_at(tree.root_node(), pos.line as usize, rel_char - 1, source),
            )
        }
    }
}
//guess what the user wants to write
fn estimate_env(node: Node, source: &Rope, pos: &Position) -> Option<CompletionEnv> {
    if node.is_extra() && !node.is_error() {
        //Comment?
        return None;
    }
    let section = find_section(node);

    info!("Section: {:?}", section);

    match section {
        Section::TopLevel => Some(CompletionEnv::Toplevel),
        Section::Imports => {
            let blk = containing_blk(node)?;
            if (node.end_position().row as u32) < pos.line {
                Some(CompletionEnv::Import)
            } else {
                match header_kind(blk) {
                    "name" => Some(CompletionEnv::Import),
                    "ref" if node.kind() == "path" => Some(CompletionEnv::Import),
                    _ => None,
                }
            }
        }
        Section::Include => Some(CompletionEnv::Include),
        Section::Features => {
            let owner = if node.start_position().row as u32 == pos.line {
                containing_blk(containing_blk(node)?)?
            } else {
                containing_blk(node)?
            };
            match header_kind(owner) {
                "group_mode" | "cardinality" | "features" => Some(CompletionEnv::Feature),
                "name" | "ref" => Some(CompletionEnv::GroupMode),
                _ => Some(CompletionEnv::Feature),
            }
        }
        Section::Constraints => {
            if (node.end_position().row as u32) < pos.line {
                Some(CompletionEnv::Constraint)
            } else {
                Some(estimate_expr(node, pos, source))
            }
        }
        Section::Attribute => Some(CompletionEnv::SomeName),
        Section::Unknown => Some(CompletionEnv::Any),
    }
}

#[derive(Debug)]
pub enum CompletionFormatter {
    UVL {
        postfix_range: Range,
    },
    JSONKey {
        postfix_range: Range,
    },
    FreeJSONKey {
        postfix_range: Range,
        key_start: Option<Range>,
    },
}
impl CompletionFormatter {
    fn text_edit(&self, _: &[Ustr], postfix: TextOP) -> TextEdit {
        match (self, postfix) {
            (Self::UVL { postfix_range }, TextOP::Put(text)) => TextEdit {
                new_text: text.into(),
                range: postfix_range.clone(),
            },
            (Self::JSONKey { postfix_range }, TextOP::Put(text)) => {
                let text = text.replace('"', r#"\""#);
                TextEdit {
                    new_text: text,
                    range: postfix_range.clone(),
                }
            }
            (
                Self::FreeJSONKey {
                    postfix_range,
                    key_start,
                },
                TextOP::Put(text),
            ) => {
                let key = if key_start.is_some() {
                    format!(r#"{}""#, text.replace('"', r#"\""#))
                } else {
                    format!(r#""{}""#, text.replace('"', r#"\""#))
                };
                TextEdit {
                    new_text: key,
                    range: postfix_range.clone(),
                }
            }
        }
    }
    fn additional_text_edits(&self) -> Option<Vec<TextEdit>> {
        match self {
            Self::FreeJSONKey {
                key_start: Some(key_start),
                ..
            } => Some(vec![TextEdit {
                range: key_start.clone(),
                new_text: "\"".into(),
            }]),
            _ => None,
        }
    }
}
#[derive(Debug)]
pub struct CompletionQuery {
    pub prefix: Vec<Ustr>,
    pub postfix: CompactString,
    pub env: CompletionEnv,
    pub offset: CompletionOffset,
    pub format: CompletionFormatter,
}
impl CompletionQuery {
    fn text_edit(&self, text: TextOP) -> TextEdit {
        self.format.text_edit(&self.prefix, text)
    }
    fn additional_text_edits(&self) -> Option<Vec<TextEdit>> {
        self.format.additional_text_edits()
    }
}

pub fn longest_path<'a>(node: Node<'a>, source: &Rope) -> Option<(Path, Node<'a>)> {
    if let Some(p) = node
        .parent()
        .and_then(|n| parse::parse_or_lang_lvl(n, source))
    {
        Some((p, node.parent().unwrap()))
    } else {
        parse::parse_or_lang_lvl(node, source).map(|p| (p, node))
    }
}
//"smart" completion, find context around the cursor
fn estimate_context(pos: &Position, draft: &Draft) -> Option<CompletionQuery> {
    match draft {
        Draft::JSON { source, tree, .. } => config::completion_query(source, tree, pos),
        Draft::UVL { source, tree, .. } => {
            let (offset, edit_node) = position_to_node(source, tree, pos);
            if let (Some((path, path_node)), CompletionOffset::Continuous) =
                (longest_path(edit_node, source), offset)
            {
                if let Some(tail) = path_node.child_by_field_name("tail") {
                    Some(CompletionQuery {
                        offset: CompletionOffset::Dot,
                        format: CompletionFormatter::UVL {
                            postfix_range: lsp_range(tail.end_byte()..tail.end_byte(), source)?,
                        },
                        postfix: CompactString::new_inline(""),
                        prefix: path.names,
                        env: estimate_env(path_node, source, pos)
                            .unwrap_or(CompletionEnv::SomeName),
                    })
                } else {
                    Some(CompletionQuery {
                        offset,
                        format: CompletionFormatter::UVL {
                            postfix_range: lsp_range(path.spans.last()?.clone(), source)?,
                        },
                        postfix: path.names.last()?.as_str().into(),
                        prefix: path.names[..path.names.len() - 1].to_vec(),
                        env: estimate_env(path_node, source, pos)
                            .unwrap_or(CompletionEnv::SomeName),
                    })
                }
            } else {
                Some(CompletionQuery {
                    offset,
                    prefix: Vec::new(),
                    postfix: "".into(),
                    format: CompletionFormatter::UVL {
                        postfix_range: Range {
                            start: *pos,
                            end: *pos,
                        },
                    },

                    env: estimate_env(edit_node, source, pos).unwrap_or(CompletionEnv::SomeName),
                })
            }
        }
    }
}
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum CompletionKind {
    Feature,
    Namespace,
    Import,
    AttributeNumber,
    AttributeAttributes,
    Keyword,
    Folder,
    File,
    DontCare,
}
impl From<Type> for CompletionKind {
    fn from(s: Type) -> Self {
        match s {
            Type::Bool => Self::Feature,
            Type::String => Self::Feature,
            Type::Namespace => Self::Import,
            Type::Real => Self::AttributeNumber,
            Type::Attributes => Self::AttributeAttributes,
            _ => Self::DontCare,
        }
    }
}

#[derive(PartialEq, Debug)]
enum TextOP {
    Put(CompactString),
}
//A completion option send to the editor
#[derive(PartialEq, Debug)]
struct CompletionOpt {
    rank: f32,
    name: Ustr,
    op: TextOP,
    label: CompactString,
    kind: CompletionKind,
}
impl CompletionOpt {
    fn new(
        kind: CompletionKind,
        name: Ustr,
        label: CompactString,
        depth: usize,
        edit: TextOP,
        query: &CompletionQuery,
    ) -> CompletionOpt {
        CompletionOpt {
            rank: completion_weight(&query.postfix, &name, depth as u32, &query.env, kind),
            op: edit,
            name,
            label,
            kind,
        }
    }
}
impl Eq for CompletionOpt {}
impl PartialOrd for CompletionOpt {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.rank.partial_cmp(&other.rank)
    }
}
impl Ord for CompletionOpt {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.rank.total_cmp(&other.rank)
    }
}

fn add_keywords<const I: usize>(
    query: &str,
    top: &mut TopN<CompletionOpt>,
    w: f32,
    words: [CompactString; I],
) {
    let regex = Regex::new(r"\$\d+|\$\{\d+:.+}").unwrap();
    for word in words {
        top.push(CompletionOpt {
            op: TextOP::Put(word.clone()),
            label: regex.replace_all(word.clone().as_mut_str(), "").into(),
            rank: if query.is_empty() {
                w
            } else {
                strsim::jaro_winkler(query, word.as_str()) as f32 * w
            },
            name: word.as_str().into(),
            kind: CompletionKind::Keyword,
        });
    }
}
fn add_top_lvl_keywords(query: &str, top: &mut TopN<CompletionOpt>, w: f32) {
    add_keywords(
        query,
        top,
        w,
        [
            "namespace".into(),
            "features\n\t".into(),
            "imports\n\t".into(),
            "constraints\n\t".into(),
            "include\n\t".into(),
        ],
    );
}

fn add_group_keywords(query: &str, top: &mut TopN<CompletionOpt>, w: f32) {
    add_keywords(
        query,
        top,
        w,
        [
            "or\n\t".into(),
            "optional\n\t".into(),
            "mandatory\n\t".into(),
            "alternative\n\t".into(),
        ],
    );
}
fn add_lang_lvl_major_keywords(query: &str, top: &mut TopN<CompletionOpt>, w: f32) {
    add_keywords(
        query,
        top,
        w,
        ["Boolean".into(), "Arithmetic".into(), "Type".into()],
    );
}
fn add_lang_lvl_arithmetic(query: &str, top: &mut TopN<CompletionOpt>, w: f32) {
    add_keywords(
        query,
        top,
        w,
        [
            "feature-cardinality".into(),
            "aggregate-function".into(),
            "*".into(),
        ],
    );
}
fn add_lang_lvl_type(query: &str, top: &mut TopN<CompletionOpt>, w: f32) {
    add_keywords(
        query,
        top,
        w,
        [
            "string-constraints".into(),
            "numeric-constraints".into(),
            "*".into(),
        ],
    );
}

fn add_lang_lvl_boolean(query: &str, top: &mut TopN<CompletionOpt>, w: f32) {
    add_keywords(query, top, w, ["group-cardinality".into(), "*".into()]);
}

fn add_logic_op(query: &str, top: &mut TopN<CompletionOpt>, w: f32) {
    add_keywords(
        query,
        top,
        w,
        [
            "& ".into(),
            "| ".into(),
            "=> ".into(),
            "<=> ".into(),
            "> ".into(),
            "< ".into(),
            "== ".into(),
        ],
    );
}
fn add_function_keywords(query: &str, top: &mut TopN<CompletionOpt>, w: f32) {
    add_keywords(
        query,
        top,
        w,
        [
            "sum($1) ".into(),
            "avg($1) ".into(),
            "len($1) ".into(),
            "floor($1) ".into(),
            "ceil($1) ".into(),
            "!".into(),
        ],
    );
}
fn make_relativ_path(path: &[CompactString], origin: &[CompactString]) -> Option<CompactString> {
    if path.len() > origin.len() {
        None
    } else if starts_with(path, origin) {
        let postfix = &origin[path.len()..];
        Some(make_path(postfix.iter()))
    } else {
        None
    }
}
//weight function
fn completion_weight(
    query: &str,
    to_match: &str,
    _depth: u32,
    env: &CompletionEnv,
    kind: CompletionKind,
) -> f32 {
    let w2 = match (env, kind) {
        (CompletionEnv::Numeric, CompletionKind::AttributeNumber)
        | (CompletionEnv::Numeric, CompletionKind::AttributeAttributes)
        | (CompletionEnv::Constraint, CompletionKind::Feature)
        | (CompletionEnv::Import, CompletionKind::Folder)
        | (CompletionEnv::Import, CompletionKind::File)
        | (CompletionEnv::Feature, CompletionKind::Feature) => W_TYPE,
        (_, _) => 1.0,
    };
    if query.is_empty() {
        w2
    } else {
        strsim::jaro_winkler(query, to_match) as f32 * w2
    }
}
//measure text distance for paths
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct ModulePath {
    len: usize,
    word: usize,
}
impl From<&[Ustr]> for ModulePath {
    fn from(p: &[Ustr]) -> Self {
        ModulePath {
            len: p.len(),
            word: path_len(p),
        }
    }
}
impl Add for ModulePath {
    type Output = ModulePath;
    fn add(self, rhs: Self) -> Self::Output {
        ModulePath {
            len: self.len + rhs.len,
            word: self.word + rhs.word,
        }
    }
}
impl Ord for ModulePath {
    fn cmp(&self, other: &Self) -> Ordering {
        self.len
            .cmp(&other.len)
            .then_with(|| self.word.cmp(&other.word))
    }
}
impl PartialOrd for ModulePath {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl pathfinding::num_traits::Zero for ModulePath {
    fn zero() -> Self {
        ModulePath { len: 0, word: 0 }
    }
    fn is_zero(&self) -> bool {
        self.word == 0 && self.len == 0
    }
}
//find completions in a document under a prefix
fn completion_symbol_local(
    snapshot: &RootGraph,
    origin: FileID,
    root: RootSymbol,
    prefix: &[Ustr],
    query: &CompletionQuery,
    top: &mut TopN<CompletionOpt>,
) {
    let file = snapshot.file(root.file);
    info!("Module {:?} under {:?}", root, prefix);
    file.visit_named_children(root.sym, true, |sym, sym_prefix| {
        let ty = file.type_of(sym).unwrap();
        if sym_prefix.is_empty() || !query.env.is_relevant(ty.into()) {
            info!("skip {:?}", sym_prefix);
            return true;
        }
        if matches!(
            query.env,
            CompletionEnv::Numeric | CompletionEnv::Constraint
        ) && matches!(sym, Symbol::Dir(_))
        {
            return true;
        }
        if query.env == CompletionEnv::Feature
            && root.file == origin
            && matches!(sym, Symbol::Feature(..))
        {
            return true;
        }
        let text = make_path(prefix.iter().chain(sym_prefix.iter()));
        top.push(CompletionOpt::new(
            ty.into(),
            *sym_prefix.last().unwrap(),
            text.clone(),
            prefix.len() + sym_prefix.len(),
            TextOP::Put(text),
            query,
        ));
        true
    });
}
fn path_len(path: &[Ustr]) -> usize {
    path.iter().map(|i| i.len()).sum()
}
//find completions in all related documents
fn completion_symbol(
    snapshot: &RootGraph,
    origin: FileID,
    query: &CompletionQuery,
    top: &mut TopN<CompletionOpt>,
) {
    let mut modules: HashMap<_, Vec<Ustr>> = HashMap::new(); //Store reachable documents under the
                                                             //search perfix under a secondary prefix

    for i in snapshot.resolve(origin, &query.prefix) {
        //Find all possible continuations for the
        //search prefix
        match &i.sym {
            Symbol::Root => {
                let _ = modules.insert(i.file, vec![]);
            }
            Symbol::Dir(..) => {
                let file = snapshot.file(i.file);
                file.visit_named_children(i.sym, true, |im_sym, im_prefix| match im_sym {
                    Symbol::Dir(..) => true,
                    Symbol::Import(..) => {
                        if let Some((_, tgt)) =
                            snapshot.fs().imports(i.file).find(|k| k.0 == im_sym)
                        {
                            if let Some(old_len) = modules
                                .get(&tgt)
                                .map(|prefix| ModulePath::from(prefix.as_slice()))
                            {
                                if old_len > im_prefix.into() {
                                    modules.insert(tgt, im_prefix.to_vec());
                                }
                            } else {
                                modules.insert(tgt, im_prefix.to_vec());
                            }
                        }

                        true
                    }
                    _ => false,
                });
            }
            _ => completion_symbol_local(snapshot, origin, i, &[], query, top),
        }
    }
    let root = FileID::max(); //Perform nn from all reachable documents to all other
    let pred = pathfinding::directed::dijkstra::dijkstra_all(&root, |node| {
        if node == &root {
            //reachable under the secondary prefix
            Either::Left(
                modules
                    .iter()
                    .map(|(k, v)| (*k, ModulePath::from(v.as_slice()))),
            )
        } else {
            //reachable under a primary import prefix
            let node = *node;
            Either::Right(
                snapshot
                    .fs()
                    .imports(node)
                    .map(move |(im, tgt)| (tgt, snapshot.file(node).import_prefix(im).into())),
            )
        }
    });
    for &i in pred.keys() {
        let mut next = i;
        let mut path = Vec::new();
        //reconstruct the shortest prefix to document i and provide completions under it
        while let Some((parent, _)) = pred.get(&next) {
            if *parent == root {
                for i in modules[&next].iter().rev() {
                    //Add the secondary prefix
                    path.push(*i);
                }

                break;
            }
            let import = snapshot
                .fs()
                .imports_connecting(*parent, next)
                .map(|im| snapshot.file(*parent).import_prefix(im))
                .min_by_key(|prefix| ModulePath::from(*prefix))
                .unwrap();
            for i in import.iter().rev() {
                path.push(*i);
            }
            next = *parent;
        }

        if path.len() > 5 {
            continue;
        }
        path.reverse();
        completion_symbol_local(
            snapshot,
            origin,
            RootSymbol {
                file: i,
                sym: Symbol::Root,
            },
            &path,
            query,
            top,
        );
    }
    //info!("{:#?}", pred);
}

//Encode float as string keeping order eg: a<b => s(a)<s(b) stolen from clangd
fn encode_float(f: f32) -> u32 {
    let top_bit = !((!0_u32) >> 1);
    let u = f32::to_bits(f);
    if (u & top_bit) != 0 {
        0_u32.wrapping_sub(u)
    } else {
        u.wrapping_add(top_bit)
    }
}

fn compute_completions_impl(
    snapshot: Snapshot,
    _draft: &Draft,
    _pos: TextDocumentPositionParams,
    ctx: &CompletionQuery,
    origin: FileID,
) -> (TopN<CompletionOpt>, bool) {
    let mut top: TopN<CompletionOpt> = TopN::new(MAX_N);

    let mut is_incomplete = false;
    match &ctx.env {
        CompletionEnv::GroupMode => {
            add_group_keywords(&ctx.postfix, &mut top, 2.0);
        }
        CompletionEnv::Toplevel => add_top_lvl_keywords(&ctx.postfix, &mut top, 2.0),

        CompletionEnv::SomeName => {}
        CompletionEnv::ConfigEntryKey => {
            for i in snapshot
                .resolve(origin, &ctx.prefix)
                .filter(|f| f.file == origin)
            {
                completion_symbol_local(&snapshot, origin, i, &[], ctx, &mut top)
            }
        }
        CompletionEnv::Constraint | CompletionEnv::Numeric | CompletionEnv::Feature => {
            match (&ctx.env, &ctx.offset) {
                //heuristic to provide nearly correct predictions, to
                //make it more accurate we need to respect
                //parenthesis
                (CompletionEnv::Feature, offset) => {
                    if matches!(
                        offset,
                        CompletionOffset::SameLine | CompletionOffset::Continuous
                    ) {
                        add_keywords(
                            &ctx.postfix,
                            &mut top,
                            2.0,
                            ["cardinality [${1:0..1}] ".into()],
                        );
                    }
                    if matches!(offset, CompletionOffset::Continuous | CompletionOffset::Cut) {
                        add_keywords(
                            &ctx.postfix,
                            &mut top,
                            2.0,
                            [
                                "Integer ".into(),
                                "String ".into(),
                                "Real ".into(),
                                "Boolean".into(),
                            ],
                        );
                        completion_symbol(&snapshot, origin, &ctx, &mut top);
                    }
                    if matches!(offset, CompletionOffset::Dot) {
                        completion_symbol(&snapshot, origin, &ctx, &mut top);
                    }
                }
                (
                    CompletionEnv::Constraint | CompletionEnv::Numeric,
                    CompletionOffset::SameLine,
                ) => {
                    add_logic_op(&ctx.postfix, &mut top, 6.1);
                    add_function_keywords(&ctx.postfix, &mut top, 2.0);
                    completion_symbol(&snapshot, origin, &ctx, &mut top);
                }
                (
                    CompletionEnv::Constraint | CompletionEnv::Numeric,
                    CompletionOffset::Cut | CompletionOffset::Continuous,
                ) => {
                    add_function_keywords(&ctx.postfix, &mut top, 2.0);
                    completion_symbol(&snapshot, origin, &ctx, &mut top);
                }
                _ => {
                    completion_symbol(&snapshot, origin, &ctx, &mut top);
                }
            }
            is_incomplete = true
        }
        CompletionEnv::Import => {
            for (path, name, node) in snapshot.fs().sub_files(origin, &ctx.prefix) {
                let len = path.as_str().chars().filter(|c| c == &'.').count();
                top.push(CompletionOpt::new(
                    match node {
                        FSNode::Dir => CompletionKind::Folder,
                        _ => CompletionKind::File,
                    },
                    name,
                    path.clone(),
                    len,
                    TextOP::Put(path),
                    &ctx,
                ))
            }
            is_incomplete = true
        }
        CompletionEnv::Include => {
            if !ctx.prefix.is_empty() {
                match ctx.prefix[0].as_str() {
                    "Boolean" => add_lang_lvl_boolean(&ctx.postfix, &mut top, 2.0),
                    "Arithmetic" => add_lang_lvl_arithmetic(&ctx.postfix, &mut top, 2.0),
                    "Type" => add_lang_lvl_type(&ctx.postfix, &mut top, 2.0),
                    _ => {}
                }
            } else {
                add_lang_lvl_major_keywords(&ctx.postfix, &mut top, 2.0);
            }
        }
        CompletionEnv::Aggregate { context } => {
            snapshot.resolve_attributes(
                origin,
                context.as_ref().map(|p| p.names.as_slice()).unwrap_or(&[]),
                |attrib, prefix| {
                    let common = prefix
                        .iter()
                        .zip(ctx.prefix.iter())
                        .take_while(|(i, k)| i == k)
                        .count();
                    if common < ctx.prefix.len() {
                        return;
                    }
                    let file = snapshot.file(attrib.file);
                    let prefix_str = make_path(prefix[common..].iter());
                    let kind = file.type_of(attrib.sym).unwrap().into();
                    if kind != CompletionKind::DontCare {
                        top.push(CompletionOpt::new(
                            kind,
                            *prefix.last().unwrap(),
                            prefix_str.clone(),
                            prefix.len(),
                            TextOP::Put(prefix_str),
                            &ctx,
                        ));
                    }
                },
            );
            if context.is_none() {
                completion_symbol(&snapshot, origin, &ctx, &mut top);
            }
        }
        CompletionEnv::ConfigRootKey => add_keywords(
            &ctx.postfix,
            &mut top,
            2.0,
            ["config".into(), "file".into()],
        ),
        _ => {}
    }

    (top, is_incomplete)
}
pub fn compute_completions(
    snapshot: Snapshot,
    draft: &Draft,
    pos: TextDocumentPositionParams,
) -> CompletionList {
    let timer = Instant::now();
    let ctx = estimate_context(&pos.position, draft);
    let origin = match draft {
        Draft::UVL { .. } => snapshot.file_id(&pos.text_document.uri),
        Draft::JSON { tree, source, .. } => config::find_file_id(
            source,
            tree,
            &pos.position,
            &pos.text_document.uri,
            &snapshot,
        ),
    };
    info!("Stat completion in  {:?} {:#?}", origin, ctx);
    if let (Some(ctx), Some(origin)) = (ctx, origin) {
        let (top, is_incomplete) = compute_completions_impl(snapshot, draft, pos, &ctx, origin);
        let items = top
            .into_sorted_vec()
            .into_iter()
            .unique_by(|c| c.label.clone())
            .filter(|opt| opt.kind != CompletionKind::DontCare)
            .map(|opt| CompletionItem {
                label: opt.label.into(),
                text_edit: Some(CompletionTextEdit::Edit(ctx.text_edit(opt.op))),
                additional_text_edits: ctx.additional_text_edits(),
                sort_text: Some(format!("{:X}", encode_float(-opt.rank))),
                filter_text: Some(opt.name.as_str().into()),
                kind: Some(match opt.kind {
                    CompletionKind::Feature => CompletionItemKind::CLASS,
                    CompletionKind::AttributeAttributes => CompletionItemKind::FIELD,
                    CompletionKind::AttributeNumber => CompletionItemKind::ENUM_MEMBER,
                    CompletionKind::Import => CompletionItemKind::MODULE,
                    CompletionKind::Keyword => CompletionItemKind::KEYWORD,
                    CompletionKind::Namespace => CompletionItemKind::MODULE,
                    CompletionKind::File => CompletionItemKind::FILE,
                    CompletionKind::Folder => CompletionItemKind::FOLDER,
                    _ => CompletionItemKind::TEXT,
                }),
                insert_text_format: Some(InsertTextFormat::SNIPPET),
                ..Default::default()
            })
            .collect();

        info!("Completions: {:?}", timer.elapsed());
        CompletionList {
            items,
            is_incomplete,
        }
    } else {
        CompletionList {
            items: Vec::new(),
            is_incomplete: true,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_top_n() {
        let mut top = TopN::new(10);
        for i in 1..11 {
            top.push(i);
        }
        top.push(100);
        top.push(11);

        top.push(0);

        assert_eq!(
            top.into_sorted_vec(),
            vec![100, 11, 10, 9, 8, 7, 6, 5, 4, 3]
        );
    }
    #[test]
    fn float_order() {
        let t = |a, b| {
            assert!(format!("{}", encode_float(a)) < format!("{}", encode_float(b)));
        };
        t(1.1, 12.0);
        t(0.1, 1.0);
        t(0.1, 0.2);
        t(1223., 121233.0);
        t(-123., 121233.0);
    }
}
