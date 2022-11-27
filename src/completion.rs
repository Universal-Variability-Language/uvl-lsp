use crate::document::Draft;
use crate::module::{self, Content};
use petgraph::graph::NodeIndex;
use tokio::time::Instant;

use crate::symboles::*;
use crate::{parse, semantic::*};
use  crate::util::*;
use compact_str::CompactString;
use log::info;
use ropey::Rope;
use std::cmp::Ordering;
use std::ops::Add;

use tower_lsp::lsp_types::{
    CompletionItem, CompletionItemKind, CompletionList, CompletionTextEdit, Position, Range,
    TextDocumentPositionParams, TextEdit,
};
use tree_sitter::Node;
use ustr::Ustr;
static MAX_N: usize = 30;
static W_PREFIX: f32 = 2.;
static W_TYPE: f32 = 2.;
static W_LEN: f32 = 3.0;
static AVG_WEIGHT_THRESHOLD: f32 = 0.2;
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
#[derive(PartialEq, Eq, Debug, Clone, Copy)]
enum CompletionEnv {
    Numeric,
    Constraint,
    GroupMode,
    Feature,
    Any,
    Toplevel,
    Import,
    SomeName,
    Include,
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
fn estimate_blk_env(blk: Node, source: &Rope) -> CompletionEnv {
    if let Some(p) = blk.parent() {
        match p.kind() {
            "blk" => match p.child_by_field_name("header").unwrap().kind() {
                "group_mode" => CompletionEnv::Feature,
                "name" => CompletionEnv::GroupMode,
                "imports" => CompletionEnv::Import,
                "constraints" => CompletionEnv::Constraint,
                "include" => CompletionEnv::Include,
                "features"=> CompletionEnv::Feature,
                _ => CompletionEnv::Any,
            },
            "source_file" => CompletionEnv::Toplevel,
            _ => CompletionEnv::Any,
        }
    } else {
        CompletionEnv::Any
    }
}
fn estimate_expr(node: Node) -> CompletionEnv {
    match node.kind() {
        "constraint" => CompletionEnv::Constraint,
        "equation" => CompletionEnv::Numeric,
        "numeric" => CompletionEnv::Numeric,
        "nested_expr" => node
            .parent()
            .map(|p| estimate_expr(p))
            .unwrap_or(CompletionEnv::Any),
        _ => CompletionEnv::Any,
    }
}

fn estimate_env(node: Node, source: &Rope) -> CompletionEnv {
    if let Some(p) = node.parent() {
        match p.kind() {
            "blk" => estimate_blk_env(p, source),
            "attribute" => CompletionEnv::SomeName,
            _ => estimate_expr(p),
        }
    } else {
        CompletionEnv::Any
    }
}

#[derive(Debug)]
struct CompletionQuery {
    perfix: Vec<Ustr>,
    postfix: CompactString,
    postfix_range: Range,
    env: CompletionEnv,
}

impl CompletionQuery {
    fn text_edit(&self, text: CompactString) -> TextEdit {
        TextEdit {
            new_text: text.into(),
            range: self.postfix_range,
        }
    }
}
//"Smart" completion
fn estimate_context(pos: &Position, draft: &Draft) -> Option<CompletionQuery> {
    match draft {
        Draft::Tree { source, tree, .. }  => {
            let line = source.line(pos.line as usize);
            let rel_char = line.utf16_cu_to_char(pos.character as usize);
            if rel_char == 0 {
                return None;
            }
            let edit_begin =
                source.line_to_byte(pos.line as usize) + line.char_to_byte(rel_char - 1);
            let edit_end = source.line_to_byte(pos.line as usize) + line.char_to_byte(rel_char);
            let edit_node = tree
                .root_node()
                .named_descendant_for_byte_range(edit_begin, edit_end)?;
            info!("Completion for: {}", edit_node.kind());
            if let Some((path, path_node)) = longest_path(edit_node, source) {
                if let Some(tail) = path_node.child_by_field_name("tail") {
                    Some(CompletionQuery {
                        postfix_range: lsp_range(tail.end_byte()..tail.end_byte(), source)?,
                        postfix: CompactString::new_inline(""),
                        perfix: path.names,
                        env: estimate_env(path_node, source),
                    })
                } else {
                    Some(CompletionQuery {
                        postfix_range: lsp_range(path.spans.last()?.clone(), source)?,
                        postfix: path.names.last()?.as_str().into(),
                        perfix: path.names[..path.names.len() - 1].to_vec(),
                        env: estimate_env(path_node, source),
                    })
                }
            } else {
                None
            }
        }
        _ => None,
    }
}
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum SymbolKind {
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
impl SymbolID {
    fn kind(&self) -> SymbolKind {
        match self {
            SymbolID::Feature(_) => SymbolKind::Feature,
            SymbolID::Namespace => SymbolKind::Namespace,
            SymbolID::Import(_) => SymbolKind::Import,
            SymbolID::AttributeAttributes(id) => SymbolKind::AttributeAttributes,
            SymbolID::AttributeNumber(id) => SymbolKind::AttributeNumber,
            _ => SymbolKind::DontCare,
        }
    }
}

#[derive(PartialEq, Debug)]
struct CompletionOpt {
    rank: f32,
    name: Ustr,
    prefix: CompactString,
    kind: SymbolKind,
}
impl CompletionOpt {
    fn new(
        kind: SymbolKind,
        name: Ustr,
        prefix: CompactString,
        depth: usize,
        query: &CompletionQuery,
    ) -> CompletionOpt {
        CompletionOpt {
            rank: completion_weight(&query.postfix, &name, depth as u32, query.env, kind),
            name,
            prefix,
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
            prefix: word.clone(),
            rank: strsim::jaro_winkler(query, word.as_str()) as f32 * w,
            name: word.as_str().into(),
            kind: SymbolKind::Keyword,
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
fn add_lang_lvl_minor_keyword(query: &str, top: &mut TopN<CompletionOpt>, w: f32) {
    add_keywords(
        query,
        top,
        w,
        [
            "group-cardinality".into(),
            "feature-cardinality".into(),
            "aggregate-function".into(),
            "*".into(),
        ],
    );
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

fn completion_weight(
    query: &str,
    to_match: &str,
    depth: u32,
    env: CompletionEnv,
    kind: SymbolKind,
) -> f32 {
    let w1 = 1.0 / (depth.saturating_sub(2).max(1)) as f32 * W_LEN;
    let w2 = match (env, kind) {
        (CompletionEnv::Numeric, SymbolKind::AttributeNumber)
        | (CompletionEnv::Numeric, SymbolKind::AttributeAttributes)
        | (CompletionEnv::Constraint, SymbolKind::Feature)
        | (CompletionEnv::Import, SymbolKind::Folder)
        | (CompletionEnv::Import, SymbolKind::File)
        | (CompletionEnv::Feature, SymbolKind::Feature) => W_TYPE,
        (_, _) => 1.0,
    };
    if query.is_empty() {
        w2 * w1
    } else {
        strsim::jaro_winkler(&query, &to_match) as f32 * w2 * w1
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct ModulePath {
    len: usize,
    word: usize,
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

fn edit<'a>(prefix: &'a str, path: &'a str) -> Option<&'a str> {
    if path.len() > prefix.len() + 1 && prefix == &path[0..prefix.len()] {
        if prefix.len() == 0 || path[prefix.len()..].starts_with(".") {
            return Some(&path[prefix.len() + 1..]);
        }
    }
    None
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct ModuleBind {
    prefix: CompactString,
    depth: usize,
    name: Ustr,
}

impl Ord for ModuleBind {
    fn cmp(&self, other: &Self) -> Ordering {
        self.depth
            .cmp(&other.depth)
            .then_with(|| self.prefix.len().cmp(&other.prefix.len()))
    }
}
impl PartialOrd for ModuleBind {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
fn completion_local(
    snapshot: &RootGraph,
    file: Ustr,
    sym: SymbolID,
    query: &CompletionQuery,

    top: &mut TopN<CompletionOpt>,
) -> Option<()> {
    let file = snapshot.files.get(&file)?;
    match file.store.get(sym)? {
        SymbolRef::Feature(feature) => {
            for i in file.store.index.prefix(&[feature.name.name]) {
                match file.store.get(*i)? {
                    SymbolRef::Attribute(attrib) => {
                        let scope = &attrib.scope.names[1..];
                        let prefix = make_path(scope.iter());
                        top.push(CompletionOpt::new(
                            i.kind(),
                            attrib.name.name,
                            prefix,
                            scope.len(),
                            query,
                        ));
                    }
                    _ => {}
                }
            }
        }
        SymbolRef::Attribute(attrib0) => {
            for i in file.store.index.prefix(&attrib0.scope.names) {
                match file.store.get(*i)? {
                    SymbolRef::Attribute(attrib) => {
                        let scope = &attrib.scope.names[attrib0.scope.names.len()..];
                        let prefix = make_path(scope.iter());
                        top.push(CompletionOpt::new(
                            i.kind(),
                            attrib.name.name,
                            prefix,
                            scope.len(),
                            query,
                        ));
                    }
                    _ => {}
                }
            }
        }
        _ => {}
    }
    Some(())
}
fn completion_file(
    snapshot: &RootGraph,
    query: &CompletionQuery,
    file_name: Ustr,
    prefix: &[Ustr],
    top: &mut TopN<CompletionOpt>,
) {
    info!("searching in {} under {:?}", file_name, prefix);
    let prefix_str = make_path(prefix.iter());
    let file = &snapshot.files[&file_name];
    for i in file.store.index.iter() {
        match file.store.get(*i).unwrap() {
            SymbolRef::Feature(f) => {
                let sub_prefix = make_path([prefix_str.as_str(), f.name.name.as_str()].iter());
                top.push(CompletionOpt::new(
                    SymbolKind::Feature,
                    f.name.name,
                    sub_prefix,
                    prefix_str.len() + 1,
                    query,
                ));
            }
            SymbolRef::Attribute(a) => {
                let sub_prefix = make_path(
                    std::iter::once(prefix_str.as_str())
                        .chain(a.scope.names.iter().map(|i| i.as_str())),
                );
                top.push(CompletionOpt::new(
                    i.kind(),
                    a.name.name,
                    sub_prefix,
                    prefix.len() + a.scope.names.len(),
                    query,
                ));
            }
            SymbolRef::Import(im) => {
                let sub_prefix = make_path(
                    [
                        prefix_str.as_str(),
                        im.alias.as_ref().unwrap().name.as_str(),
                    ]
                    .iter(),
                );
                top.push(CompletionOpt::new(
                    SymbolKind::Namespace,
                    im.alias.as_ref().unwrap().name,
                    sub_prefix,
                    prefix_str.len() + 1,
                    query,
                ));
            }
            _ => {}
        }
    }
}

fn completion_root(
    snapshot: &RootGraph,
    origin: Ustr,
    query: &CompletionQuery,
    exclude_origin: bool,
    top: &mut TopN<CompletionOpt>,
) {
    let mut source_points = Vec::new();
    snapshot.resolve(origin, &query.perfix, |i| match i {
        RootSymbolID::Module(id) => {
            info!("source {:?}: {:?}", id, snapshot.modules[id]);
            source_points.push(id);
            None::<()>
        }

        RootSymbolID::Symbol(file, sym) => {
            completion_local(snapshot, file, sym, query, top);
            None
        }
    });

    let virtual_root = NodeIndex::new(std::usize::MAX);

    let shortest_paths =
        pathfinding::directed::dijkstra::dijkstra_all(&virtual_root, |node: &NodeIndex| {
            if *node == virtual_root {
                itertools::Either::Left(
                    source_points
                        .iter()
                        .map(|i| (*i, ModulePath { len: 0, word: 0 })),
                )
            } else {
                itertools::Either::Right(
                    snapshot
                        .modules
                        .edges(
                            *node,
                            Some(origin),
                            if source_points.len() > 1 {
                                None
                            } else {
                                Some(snapshot.modules.node_from_file(origin))
                            },
                        )
                        .map(|(name, target)| {
                            (
                                target,
                                ModulePath {
                                    word: if name.as_str() == "#" { 0 } else { name.len() },
                                    len: if name.len() > 0 && name.as_str() != "#" {
                                        1
                                    } else {
                                        0
                                    },
                                },
                            )
                        }),
                )
            }
        });
    fn kind_from_module(c: &Content) -> SymbolKind {
        match c {
            Content::Dir => SymbolKind::Folder,
            Content::File(_) => SymbolKind::File,
            Content::Namespace => SymbolKind::Namespace,
            Content::FileRoot(_) => SymbolKind::DontCare,
        }
    }
    info!("{:?}", shortest_paths);
    for &i in shortest_paths.keys() {
        let mut next = i;
        let mut path = Vec::new();
        while let Some((parent, _)) = shortest_paths.get(&next) {
            if next == *parent || *parent == virtual_root {
                break;
            }
            path.push(snapshot.modules.edge_connecting(*parent, next));
            next = *parent;
        }
        if path.len()>5{
            continue;
        }

        if path.last().map(|p| p.as_str() == "#").unwrap_or(false) {
            path.pop();
        }
        path.reverse();
        let m = &snapshot.modules[i];
        match m {
            Content::Namespace | Content::Dir | Content::File(_) => {
                info!("Found module {:?}", path);
                if path.len() == 0 {
                    continue;
                }
                top.push(CompletionOpt::new(
                    kind_from_module(&m),
                    *path.last().unwrap(),
                    make_path(path.iter()),
                    path.len(),
                    query,
                ));
            }
            Content::FileRoot(file) => {
                if exclude_origin && *file == origin {
                    continue;
                }
                completion_file(snapshot, query, *file, &path, top);
            }
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct Canditate {
    prefix: CompactString,
    file: Ustr,
    depth: u32,
}
impl Ord for Canditate {
    fn cmp(&self, other: &Self) -> Ordering {
        self.depth.cmp(&other.depth).reverse()
    }
}
impl PartialOrd for Canditate {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
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
        match ctx.env {
            CompletionEnv::GroupMode => add_group_keywords(&ctx.postfix, &mut top, 2.0),
            CompletionEnv::Toplevel => add_top_lvl_keywords(&ctx.postfix, &mut top, 2.0),
            CompletionEnv::SomeName => {}
            CompletionEnv::Constraint | CompletionEnv::Numeric => {
                completion_root(&snapshot, origin, &ctx, false, &mut top);
                is_incomplete = true
            }
            CompletionEnv::Feature => {
                completion_root(&snapshot, origin, &ctx, true, &mut top);
                is_incomplete = true
            }
            CompletionEnv::Import => {
                completion_root(&snapshot, origin, &ctx, true, &mut top);
                is_incomplete = true
            }
            CompletionEnv::Include => {
                if ctx.perfix.len() > 0 {
                    add_lang_lvl_minor_keyword(&ctx.postfix, &mut top, 2.0)
                } else {
                    add_lang_lvl_major_keywords(&ctx.postfix, &mut top, 2.0);
                }
            }
            _ => {
                completion_root(&snapshot, origin, &ctx, false, &mut top);

                add_top_lvl_keywords(&ctx.postfix, &mut top, 1.0);
                add_top_lvl_keywords(&ctx.postfix, &mut top, 1.0);
                is_incomplete = true;
            }
        }

        let mut comp = top.into_sorted_vec();
        info!("Completions: {:?} in {:?}", comp, timer.elapsed());
        let items = comp
            .drain(0..)
            .filter(|opt| opt.kind != SymbolKind::DontCare)
            .map(|opt| CompletionItem {
                label: opt.prefix.clone().into(),
                text_edit: Some(CompletionTextEdit::Edit(ctx.text_edit(opt.prefix))),
                sort_text: Some(format!("{:X}", encode_float(-opt.rank))),
                filter_text: Some(opt.name.as_str().into()),
                kind: Some(match opt.kind {
                    SymbolKind::Feature => CompletionItemKind::CLASS,
                    SymbolKind::AttributeAttributes => CompletionItemKind::FIELD,
                    SymbolKind::AttributeNumber => CompletionItemKind::ENUM_MEMBER,
                    SymbolKind::Import => CompletionItemKind::MODULE,
                    SymbolKind::Keyword => CompletionItemKind::KEYWORD,
                    SymbolKind::Namespace => CompletionItemKind::MODULE,
                    SymbolKind::File => CompletionItemKind::FILE,
                    SymbolKind::Folder => CompletionItemKind::FOLDER,
                    _ => CompletionItemKind::TEXT,
                }),
                ..Default::default()
            })
            .collect();
        


        info!("Completions: {:?} in {:?}", items, timer.elapsed());
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
