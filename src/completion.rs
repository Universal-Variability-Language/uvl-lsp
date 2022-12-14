use crate::document::Draft;
use crate::filegraph::*;
use crate::util::*;
use crate::{parse, semantic::*};
use compact_str::CompactString;
use itertools::Either;
use log::info;
use ropey::Rope;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::collections::HashSet;
use std::ops::Add;
use tokio::time::Instant;
use tower_lsp::lsp_types::{
    CompletionItem, CompletionItemKind, CompletionList, CompletionTextEdit, Position, Range,
    TextDocumentPositionParams, TextEdit,
};
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
    for i in i.filter(|i| i.as_ref().len() > 0) {
        if out.len() == 0 {
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
}
pub fn find_section(node: Node) -> Section {
    if node.kind() == "blk" {
        match node.child_by_field_name("header").unwrap().kind() {
            "constraints" => Section::Constraints,
            "include" => Section::Include,
            "imports" => Section::Imports,
            "features" => Section::Features,
            _ => find_section(node.parent().unwrap()),
        }
    } else if node.kind() == "source_file" {
        Section::TopLevel
    } else if node.kind() == "attribute_constraints" || node.kind() == "attribute_constraint" {
        Section::Constraints
    } else if let Some(p) = node.parent() {
        find_section(p)
    } else {
        Section::Unknown
    }
}
fn longest_path<'a>(node: Node<'a>, source: &Rope) -> Option<(Path, Node<'a>)> {
    if let Some(p) = node
        .parent()
        .map(|n| parse::parse_path(n, source).or_else(|| parse::parse_lang_lvl_path(n, source)))
        .flatten()
    {
        Some((p, node.parent().unwrap()))
    } else if let Some(p) = parse::parse_path(node, source) {
        Some((p, node))
    } else {
        None
    }
}

pub fn estimate_constraint_env(node: Node, origin: Option<Node>, source: &Rope) -> CompletionEnv {
    if node.is_error() {
        for i in tree_sitter_traversal::traverse(node.walk(), tree_sitter_traversal::Order::Pre) {
            match i.kind() {
                "+" | "-" | "*" | "/" | ">" | "<" | "==" => return CompletionEnv::Numeric,
                "=>" | "&" | "|" | "<=>" => return CompletionEnv::Constraint,
                _ => {}
            }
        }
    }
    match node.kind() {
        "nested_expr" | "path" | "name" => {
            estimate_constraint_env(node.parent().unwrap(), Some(node), source)
        }
        "number" => CompletionEnv::Numeric,
        "aggregate" => {
            if let Some(origin) = origin {
                if node
                    .child_by_field_name("context")
                    .map(|ctx| ctx == origin)
                    .unwrap_or(false)
                {
                    CompletionEnv::Constraint
                } else {
                    CompletionEnv::Aggregate {
                        context: node
                            .child_by_field_name("context")
                            .map(|ctx| parse::parse_path(ctx, source))
                            .flatten(),
                    }
                }
            } else {
                CompletionEnv::Aggregate { context: None }
            }
        }
        "binary_expr" => match node.child_by_field_name("op").unwrap().kind() {
            "=>" | "&" | "|" | "<=>" => return CompletionEnv::Constraint,
            _ => CompletionEnv::Numeric,
        },
        _ => CompletionEnv::Constraint,
    }
}
fn estimate_env(node: Node, source: &Rope, edit_line: u32) -> Option<CompletionEnv> {
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
            if (node.end_position().row as u32) < edit_line {
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
            let owner = if node.start_position().row as u32 == edit_line {
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
            if (node.end_position().row as u32) < edit_line {
                Some(CompletionEnv::Constraint)
            } else {
                Some(estimate_constraint_env(node, None, source))
            }
        }
        Section::Unknown => Some(CompletionEnv::Any),
    }
}

#[derive(Debug)]
struct CompletionQuery {
    perfix: Vec<Ustr>,
    postfix: CompactString,
    postfix_range: Range,
    env: CompletionEnv,
    offset: CompletionOffset,
}
impl CompletionQuery {
    fn text_edit(&self, text: TextOP) -> TextEdit {
        match text {
            TextOP::Put(text) => TextEdit {
                new_text: text.into(),
                range: self.postfix_range,
            },
        }
    }
}
fn node_at(node: Node, pos: tree_sitter::Point) -> Node {
    let mut next = pos;
    next.column += 1;
    node.named_descendant_for_point_range(pos, next).unwrap()
}
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum CompletionOffset {
    Continous, // We are in path
    Dot,       //We are in open path ending with a dot
    SameLine,  // We are in a unfinished line
    Cut,       //We are in a empty line
}
//Search for context in the vicinity of the cursor
//first search on char back, then inside the line, then in the previous line etc.
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
                CompletionOffset::Continous,
                node_at(
                    tree.root_node(),
                    Point {
                        row: pos.line as usize,
                        column: rel_char - 1,
                    },
                ),
            )
        } else {
            for i in (0..rel_char - 1).rev() {
                if !source.char(base_offset + i).is_whitespace() {
                    return (
                        CompletionOffset::SameLine,
                        node_at(
                            tree.root_node(),
                            Point {
                                row: pos.line as usize,
                                column: i,
                            },
                        ),
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
                        node_at(
                            tree.root_node(),
                            Point {
                                row: i,
                                column: rel_char - 1,
                            },
                        ),
                    );
                }
            }

            (
                CompletionOffset::Cut,
                node_at(
                    tree.root_node(),
                    Point {
                        row: pos.line as usize,
                        column: rel_char - 1,
                    },
                ),
            )
        }
    }
}
//"Smart" completion, find context arround the cursor
fn estimate_context(pos: &Position, draft: &Draft) -> Option<CompletionQuery> {
    match draft {
        Draft::Tree { source, tree, .. } => {
            let (offset, edit_node) = position_to_node(source, tree, pos);
            info!("Completion for: {:?}", edit_node);
            if let (Some((path, path_node)), CompletionOffset::Continous) =
                (longest_path(edit_node, source), offset)
            {
                if let Some(tail) = path_node.child_by_field_name("tail") {
                    Some(CompletionQuery {
                        offset: CompletionOffset::Dot,
                        postfix_range: lsp_range(tail.end_byte()..tail.end_byte(), source)?,
                        postfix: CompactString::new_inline(""),
                        perfix: path.names,
                        env: estimate_env(path_node, source, pos.line)
                            .unwrap_or(CompletionEnv::SomeName),
                    })
                } else {
                    Some(CompletionQuery {
                        offset,
                        postfix_range: lsp_range(path.spans.last()?.clone(), source)?,
                        postfix: path.names.last()?.as_str().into(),
                        perfix: path.names[..path.names.len() - 1].to_vec(),
                        env: estimate_env(path_node, source, pos.line)
                            .unwrap_or(CompletionEnv::SomeName),
                    })
                }
            } else {
                Some(CompletionQuery {
                    offset,
                    perfix: Vec::new(),

                    postfix: "".into(),
                    postfix_range: Range {
                        start: pos.clone(),
                        end: pos.clone(),
                    },
                    env: estimate_env(edit_node, source, pos.line)
                        .unwrap_or(CompletionEnv::SomeName),
                })
            }
        }
        _ => None,
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
impl From<Symbol> for CompletionKind {
    fn from(s: Symbol) -> Self {
        match s {
            Symbol::Root => Self::DontCare,
            Symbol::Dir(..) => Self::Folder,
            Symbol::Feature(..) => Self::Feature,
            Symbol::Import(..) => Self::Import,
            Symbol::Number(..) => Self::AttributeNumber,
            Symbol::Attributes(..) => Self::AttributeAttributes,
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
    lable: CompactString,
    kind: CompletionKind,
}
impl CompletionOpt {
    fn new(
        kind: CompletionKind,
        name: Ustr,
        lable: CompactString,
        depth: usize,
        edit: TextOP,
        query: &CompletionQuery,
    ) -> CompletionOpt {
        CompletionOpt {
            rank: completion_weight(&query.postfix, &name, depth as u32, &query.env, kind),
            op: edit,
            name,
            lable,
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
    for word in words {
        top.push(CompletionOpt {
            op: TextOP::Put(word.clone()),
            lable: word.clone(),
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
            "features".into(),
            "imports".into(),
            "constraints".into(),
            "include".into(),
        ],
    );
}

fn add_group_keywords(query: &str, top: &mut TopN<CompletionOpt>, w: f32) {
    add_keywords(
        query,
        top,
        w,
        [
            "or".into(),
            "optional".into(),
            "mandatory".into(),
            "alternative".into(),
        ],
    );
}
fn add_lang_lvl_major_keywords(query: &str, top: &mut TopN<CompletionOpt>, w: f32) {
    add_keywords(query, top, w, ["SMT-level".into(), "SAT-level".into()]);
}
fn add_lang_lvl_smt(query: &str, top: &mut TopN<CompletionOpt>, w: f32) {
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

fn add_lang_lvl_sat(query: &str, top: &mut TopN<CompletionOpt>, w: f32) {
    add_keywords(query, top, w, ["group-cardinality".into(), "*".into()]);
}

fn add_logic_op(query: &str, top: &mut TopN<CompletionOpt>, w: f32) {
    add_keywords(
        query,
        top,
        w,
        [
            "&".into(),
            "|".into(),
            "=>".into(),
            "<=>".into(),
            ">".into(),
            "<".into(),
            "==".into(),
        ],
    );
}

fn add_function_keywords(query: &str, top: &mut TopN<CompletionOpt>, w: f32) {
    add_keywords(query, top, w, ["sum".into(), "avg".into()]);
}
fn make_relativ_path(path: &[CompactString], origin: &[CompactString]) -> Option<CompactString> {
    if path.len() > origin.len() {
        None
    } else {
        if starts_with(path, origin) {
            let postfix = &origin[path.len()..];
            Some(make_path(postfix.iter()))
        } else {
            None
        }
    }
}
//weight function
fn completion_weight(
    query: &str,
    to_match: &str,
    depth: u32,
    env: &CompletionEnv,
    kind: CompletionKind,
) -> f32 {
    let w1 = 1.0 / (depth.saturating_sub(2).max(1)) as f32 * W_LEN;
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
        w2 * w1
    } else {
        strsim::jaro_winkler(&query, &to_match) as f32 * w2 * w1
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
        Some(self.cmp(&other))
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
    origin: Ustr,

    root: RootSymbol,
    prefix: &[Ustr],
    query: &CompletionQuery,
    top: &mut TopN<CompletionOpt>,
) {
    let file = &snapshot.files[&root.file];
    for (sym_prefix, sym) in file.children(root.sym) {
        if matches!(sym, Symbol::Dir(..)) {
            info!("{:?}, {:?}", sym, prefix)
        }
        if sym_prefix.is_empty() || !query.env.is_relevant(sym.into()) {
            continue;
        }
        if query.env == CompletionEnv::Feature
            && root.file == origin
            && matches!(sym, Symbol::Feature(..))
        {
            continue;
        }
        let text = make_path(prefix.iter().chain(sym_prefix.iter()));
        top.push(CompletionOpt::new(
            sym.into(),
            *sym_prefix.last().unwrap(),
            text.clone(),
            prefix.len() + sym_prefix.len(),
            TextOP::Put(text),
            query,
        ))
    }
}
fn path_len(path: &[Ustr]) -> usize {
    path.iter().map(|i| i.len()).sum()
}
//find completions in all related documents
fn completion_symbol(
    snapshot: &RootGraph,
    origin: Ustr,
    query: &CompletionQuery,
    top: &mut TopN<CompletionOpt>,
) {
    let mut modules: HashMap<_, &[Ustr]> = HashMap::new(); //Store reachable documents under the
                                                           //search perfix under a secondary prefix
    let mut visited = HashSet::new(); //Needed for circular references?

    for i in snapshot.resolve(origin, &query.perfix) {
        //Find all possible continuations for the
        //search prefix
        visited.insert(i.file);
        match &i.sym {
            Symbol::Root => {
                let _ = modules.insert(i.file, &[]);
            }
            Symbol::Dir(..) => {
                let file = &snapshot.files[&i.file];
                for im in file.imports_under(i.sym) {
                    if let Some((_, tgt)) = snapshot.fs.imports(i.file).find(|k| k.0 == im) {
                        let prefix = &file.prefix(im)[file.prefix(i.sym).len()..];
                        if let Some(old_len) =
                            modules.get(&tgt).map(|&prefix| ModulePath::from(prefix))
                        {
                            if old_len > prefix.into() {
                                modules.insert(tgt, prefix);
                            }
                        } else {
                            modules.insert(tgt, prefix);
                        }
                    }
                }
            }
            _ => completion_symbol_local(snapshot, origin, i, &[], query, top),
        }
    }
    let root = Ustr::from(""); //Perform nn from all reachable documents to all other
    let pred = pathfinding::directed::dijkstra::dijkstra_all(&root, |node| {
        if node == &root {
            Either::Left(modules.iter().map(|(k, v)| (*k, ModulePath::from(*v))))
        } else {
            let node = *node;
            Either::Right(
                snapshot
                    .fs
                    .imports(node)
                    .map(move |(im, tgt)| (tgt, snapshot.files[&node].prefix(im).into())),
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
                    path.push(*i);
                }

                break;
            }
            let import = snapshot
                .fs
                .imports_connecting(*parent, next)
                .map(|im| snapshot.files[parent].prefix(im))
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

pub fn compute_completions(
    snapshot: RootGraph,
    draft: &Draft,
    pos: TextDocumentPositionParams,
) -> CompletionList {
    info!("Starting completion");
    let timer = Instant::now();
    let origin = Ustr::from(pos.text_document.uri.as_str());
    let ctx = estimate_context(&pos.position, draft);
    info!("Stat completion: {:#?}", ctx);
    if let Some(ctx) = ctx {
        let mut top: TopN<CompletionOpt> = TopN::new(MAX_N);
        let mut is_incomplete = false;
        match &ctx.env {
            CompletionEnv::GroupMode => {
                add_group_keywords(&ctx.postfix, &mut top, 2.0);
            }
            CompletionEnv::Toplevel => add_top_lvl_keywords(&ctx.postfix, &mut top, 2.0),
            CompletionEnv::SomeName => {}
            CompletionEnv::Constraint | CompletionEnv::Numeric | CompletionEnv::Feature => {
                match (&ctx.env, &ctx.offset) {//heuristic to provide nearly correct predictions, to
                                               //make it more accurate we need to respect
                                               //parenthesis
                    (CompletionEnv::Feature, CompletionOffset::SameLine) => {
                        add_keywords(&ctx.postfix, &mut top, 2.0, ["cardinality".into()]);
                    }
                    (CompletionEnv::Constraint|CompletionEnv::Numeric, CompletionOffset::SameLine) => {
                        add_logic_op(&ctx.postfix, &mut top, 6.1);
                        add_function_keywords(&ctx.postfix, &mut top, 4.0);
                        completion_symbol(&snapshot, origin, &ctx, &mut top);
                    }
                    (CompletionEnv::Constraint|CompletionEnv::Numeric, CompletionOffset::Cut|CompletionOffset::Continous)  => {
                        add_function_keywords(&ctx.postfix, &mut top, 4.0);
                        completion_symbol(&snapshot, origin, &ctx, &mut top);
                    }
                    _ => {
                        completion_symbol(&snapshot, origin, &ctx, &mut top);
                    }
                }
                is_incomplete = true
            }
            CompletionEnv::Import => {
                for (path, name, node) in snapshot.fs.sub_files(origin, &ctx.perfix) {
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
                if ctx.perfix.len() > 0 {
                    match ctx.perfix[0].as_str() {
                        "SAT-level" => add_lang_lvl_sat(&ctx.postfix, &mut top, 2.0),
                        "SMT-level" => add_lang_lvl_smt(&ctx.postfix, &mut top, 2.0),
                        _ => {}
                    }
                } else {
                    add_lang_lvl_major_keywords(&ctx.postfix, &mut top, 2.0);
                }
            }
            CompletionEnv::Aggregate { context } => {
                let mut has_context = false;
                if let Some(context) = context.as_ref().and_then(|path| {
                    Some(snapshot.resolve(origin, &path.names).filter(|node| {
                        matches!(
                            node.sym,
                            Symbol::Feature(..) | Symbol::Attributes(..) | Symbol::Root
                        )
                    }))
                }) {
                    for f in context {
                        info!("found context");
                        has_context = true;
                        let file = &snapshot.files[&f.file];
                        for (prefix, i) in file.children_attributes(f.sym) {
                            if CompletionKind::from(i) == CompletionKind::DontCare {
                                continue;
                            }
                            let prefix_str = make_path(prefix.iter());
                            top.push(CompletionOpt::new(
                                i.into(),
                                *prefix.last().unwrap(),
                                prefix_str.clone(),
                                prefix.len(),
                                TextOP::Put(prefix_str),
                                &ctx,
                            ))
                        }
                    }
                }
                if !has_context {
                    let file = &snapshot.files[&origin];
                    for (prefix, i) in file.children_attributes(Symbol::Root) {
                        info!("{:?}, {:?}", prefix, i);
                        if CompletionKind::from(i) == CompletionKind::DontCare {
                            continue;
                        }
                        let prefix_str = make_path(prefix.iter());
                        top.push(CompletionOpt::new(
                            i.into(),
                            *prefix.last().unwrap(),
                            prefix_str.clone(),
                            prefix.len(),
                            TextOP::Put(prefix_str),
                            &ctx,
                        ))
                    }
                }
                if context.is_none() {
                    completion_symbol(&snapshot, origin, &ctx, &mut top);
                }
            }
            _ => {}
        }

        let mut comp = top.into_sorted_vec();
        info!("Completions in {:?}", timer.elapsed());
        let items = comp
            .drain(0..)
            .filter(|opt| opt.kind != CompletionKind::DontCare)
            .map(|opt| CompletionItem {
                label: opt.lable.into(),
                text_edit: Some(CompletionTextEdit::Edit(ctx.text_edit(opt.op))),
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
                ..Default::default()
            })
            .collect();

        //info!("Completions: {:?} in {:?}", items, timer.elapsed());
        CompletionList {
            items,
            is_incomplete,
        }
    } else {
        CompletionList {
            is_incomplete: true,
            items: vec![],
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
