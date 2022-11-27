use crate::document::{AsyncDraft, DocumentState};
use crate::module::ModuleGraph;
use crate::{check, parse, symboles::*, util};
use dashmap::DashMap;
use parking_lot::RwLock;
use petgraph::graph::NodeIndex;

use log::info;
use petgraph::visit::Dfs;
use petgraph::Directed;
use petgraph::{graphmap::GraphMap, Direction};

use lazy_static::lazy_static;
use rayon::prelude::*;
use ropey::Rope;
use std::collections::HashMap;
use std::fmt::Debug;
use std::path::Component;
use std::sync::atomic::{AtomicI64, AtomicU64};
use std::sync::Arc;
use tokio::sync::mpsc;
use tokio::time::{Duration, Instant};
use tokio::{select, spawn};
use tokio_util::sync::CancellationToken;
use tower_lsp::lsp_types::*;
use tower_lsp::Client;
use tree_sitter::{Node, QueryCursor, Tree};
use ustr::Ustr;
lazy_static! {
    pub static ref TS: util::ParseConstants = util::ParseConstants::new();
}
pub type Span = std::ops::Range<usize>;
#[derive(Clone, Debug)]
pub struct SymbolSpan {
    pub name: Ustr,
    pub span: Span,
}
#[derive(Clone, Debug, Default)]
pub struct Path {
    pub names: Vec<Ustr>,
    pub spans: Vec<Span>,
}

impl Path {
    fn append(&self, arg: &SymbolSpan) -> Path {
        let mut new = self.clone();
        new.names.push(arg.name);
        new.spans.push(arg.span.clone());
        new
    }
    pub fn range(&self) -> Span {
        if self.spans.len() > 0 {
            self.spans[0].start..self.spans.last().unwrap().end
        } else {
            0..0
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Type {
    String,
    Bool,
    Number,
    Vector,
    Attributes,
    Unknown,
    Void,
    Namespace,
    Alias,
    File,
    Directory,
    Feature,
}

#[derive(Clone, Debug)]
pub enum LocalEdge {
    Ref,
    Group,
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Equatation(Span, Box<Expr>, Box<Expr>),
    Numeric(Span, Box<Expr>, Box<Expr>),
    Constraint(Span, Box<Expr>, Box<Expr>),
    Not(Box<Expr>),
    Inner(Box<Expr>),
    Ref(usize),
}

#[derive(Clone, Debug)]
pub struct Expr {}
#[derive(Hash, PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Copy)]
pub enum SymbolID {
    Feature(u32),
    Import(u32),
    Group(u32),
    Reference(u32),
    AttributeBool(u32),
    AttributeNumber(u32),
    AttributeString(u32),
    AttributeVoid(u32),
    AttributeAttributes(u32),
    AttributeVector(u32),
    AttributeUnknown(u32),
    Namespace,
}

#[derive(Clone, Debug)]
pub struct Feature {
    pub name: SymbolSpan,
}
#[derive(Clone, Debug)]
pub struct Import {
    pub path: Path,
    pub alias: Option<SymbolSpan>,
}
#[derive(Clone, Debug)]
pub struct Namespace {
    pub prefix: Path,
}
#[derive(Clone, Debug)]
pub struct Group {
    pub mode: SymbolSpan,
}
#[derive(Clone, Debug)]
pub struct Reference {
    pub path: Path,
    pub ty: Type,
}
#[derive(Clone, Debug)]
pub struct Attribute {
    pub name: SymbolSpan,
    pub scope: Path,
    pub ty: Type,
}
#[derive(Clone, Debug)]
pub enum SymbolRef<'a> {
    Feature(&'a Feature),
    Import(&'a Import),
    Namespace(&'a Namespace),
    Group(&'a Group),
    Reference(&'a Reference),
    Attribute(&'a Attribute),
}

fn uri_to_path(uri: &Url) -> Option<Vec<Ustr>> {
    let mut p = uri.to_file_path().ok()?;
    p.set_extension("");
    p.components()
        .filter_map(|c| match c {
            Component::Normal(os) => os.to_str().map(|s| Some(s.into())),
            _ => None,
        })
        .collect()
}
fn resolve_value_kind(node: Node) -> Type {
    match node.kind() {
        "string" => Type::String,
        "vector" => Type::Vector,
        "attributes" => Type::Attributes,
        "nested_expr" | "attrib_expr" => resolve_value_kind(node.named_child(0).unwrap()),
        "numeric" => Type::Number,
        "constraint" => Type::Bool,
        "equation" => Type::Number,
        _ => Type::Unknown,
    }
}
fn resolve_reference_ty(node: Node) -> Type {
    match node.parent().unwrap().kind() {
        "nested_expr" => resolve_reference_ty(node.parent().unwrap()),
        "numeric" => Type::Number,
        "equation" => Type::Number,
        _ => Type::Feature,
    }
}

#[derive(Clone, Debug, Default)]
pub struct FileGraphStorage {
    pub features: Vec<Feature>,
    pub imports: Vec<Import>,
    pub namespace: Option<Namespace>,
    pub groups: Vec<Group>,
    pub references: Vec<Reference>,
    pub attributes: Vec<Attribute>,
    pub dep: GraphMap<SymbolID, LocalEdge, Directed>,
    pub ts2sym: HashMap<usize, SymbolID>,
    pub index: SymbolTable<SymbolID>,
    pub exprs: Vec<Expr>,
}
impl FileGraphStorage {
    fn add_index(&mut self, path: Vec<Ustr>, id: SymbolID) {
        self.index.insert_unsorted(path, id);
    }

    fn add_feature(&mut self, node: Node, source: &String) {
        let id = SymbolID::Feature(self.features.len() as u32);
        let feature = Feature {
            name: parse::parse_name(node, source).unwrap(),
        };
        let blk = node.parent().unwrap();
        self.ts2sym.insert(blk.id(), id);
        self.add_index(vec![feature.name.name], id);
        //self.add_completion(source[feature.name.span.clone()].into(), id);
        self.features.push(feature);
    }
    fn add_ref(&mut self, blk: Node, path: Node, ty: Type, source: &String) {
        let id = SymbolID::Reference(self.references.len() as u32);
        let reference = Reference {
            path: parse::parse_path(path, source).unwrap(),
            ty,
        };
        self.ts2sym.insert(blk.id(), id);
        self.references.push(reference);
    }
    fn add_import(&mut self, blk: Node, path: Node, alias: Option<Node>, source: &String) {
        let id = SymbolID::Import(self.imports.len() as u32);
        let import = Import {
            path: parse::parse_path(path, source).unwrap(),
            alias: alias.map(|i| parse::parse_name(i, source)).flatten(),
        };
        self.ts2sym.insert(blk.id(), id);

        if let Some(alias) = import.alias.as_ref() {
            //self.add_completion(source[alias.span.clone()].into(), id);
            self.add_index(vec![alias.name], id);
        }
        self.imports.push(import);
    }
    fn add_namespace(&mut self, node: Node, source: &String) {
        if self.namespace.is_none() {
            let prefix = parse::parse_path(node, source).unwrap();
            let namepace = Namespace { prefix };
            let blk = node.parent().unwrap();
            self.ts2sym.insert(blk.id(), SymbolID::Namespace);
            //self.add_index(namepace.prefix.names.clone(), SymbolID::Namespace);
            self.namespace = Some(namepace);
        }
    }
    fn add_group(&mut self, node: Node, source: &String) {
        let id = SymbolID::Group(self.groups.len() as u32);
        let group = Group {
            mode: SymbolSpan {
                name: Ustr::from(&source[node.byte_range()]),
                span: node.byte_range(),
            },
        };
        self.ts2sym.insert(node.parent().unwrap().id(), id);
        self.groups.push(group);
    }
    fn add_attribute(&mut self, node: Node, source: &String) {
        let value = node
            .child_by_field_name("value")
            .map(|n| (n.byte_range(), resolve_value_kind(n)))
            .unwrap_or((0..0, Type::Void));

        let id = match value.1 {
            Type::Bool => SymbolID::AttributeBool(self.attributes.len() as u32),
            Type::String => SymbolID::AttributeString(self.attributes.len() as u32),
            Type::Void => SymbolID::AttributeVoid(self.attributes.len() as u32),
            Type::Unknown => SymbolID::AttributeUnknown(self.attributes.len() as u32),
            Type::Vector => SymbolID::AttributeVector(self.attributes.len() as u32),
            Type::Number => SymbolID::AttributeNumber(self.attributes.len() as u32),
            Type::Attributes => SymbolID::AttributeAttributes(self.attributes.len() as u32),
            _ => panic!("internal error"),
        };
        let name = parse::parse_name(node.child_by_field_name("name").unwrap(), source).unwrap();
        let attribute = Attribute {
            name,
            scope: Path {
                names: Vec::new(),
                spans: Vec::new(),
            },
            ty: node
                .child_by_field_name("value")
                .map(|n| resolve_value_kind(n))
                .unwrap_or(Type::Void),
        };
        self.ts2sym.insert(node.id(), id);
        //self.add_completion(path_str.join_compact("."), id);
        //self.add_index(attribute.scope.names.clone(), id);
        self.attributes.push(attribute);
    }
    pub fn get(&self, id: SymbolID) -> Option<SymbolRef> {
        match id {
            SymbolID::Feature(i) => Some(SymbolRef::Feature(&self.features[i as usize])),
            SymbolID::Import(i) => Some(SymbolRef::Import(&self.imports[i as usize])),
            SymbolID::Namespace => self.namespace.as_ref().map(|i| SymbolRef::Namespace(i)),
            SymbolID::Group(i) => Some(SymbolRef::Group(&self.groups[i as usize])),
            SymbolID::Reference(i) => Some(SymbolRef::Reference(&self.references[i as usize])),
            SymbolID::AttributeVoid(i)
            | SymbolID::AttributeNumber(i)
            | SymbolID::AttributeBool(i)
            | SymbolID::AttributeString(i)
            | SymbolID::AttributeVector(i)
            | SymbolID::AttributeUnknown(i)
            | SymbolID::AttributeAttributes(i) => {
                Some(SymbolRef::Attribute(&self.attributes[i as usize]))
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct FileGraph {
    pub store: FileGraphStorage,
    pub source: String,
    pub name: Ustr,
    pub path: Vec<Ustr>,
    pub timestamp: Instant,
    pub rope: Rope,
    pub tree: Tree,
    pub uri: Url,
}

impl FileGraph {
    pub fn new(timestamp: Instant, tree: Tree, rope: Rope, url: Url) -> FileGraph {
        let t = Instant::now();
        let mut store = FileGraphStorage::default();
        let source = rope.to_string();
        let mut cursor = QueryCursor::new();
        {
            let cap_name = &TS.queries.extract_symboles;
            for i in cursor.matches(
                &TS.queries.extract_symboles,
                tree.root_node(),
                source.as_bytes(),
            ) {
                let m = &i.captures[0];
                let n = m.node;
                match cap_name.capture_names()[m.index as usize].as_str() {
                    "feature" => store.add_feature(n, &source),
                    "ref" => store.add_ref(n.parent().unwrap(), n, Type::Feature, &source),
                    "import_ref" => store.add_import(
                        n.parent().unwrap(),
                        n.child_by_field_name("path").unwrap(),
                        n.child_by_field_name("alias"),
                        &source,
                    ),
                    "import_name" => store.add_import(n.parent().unwrap(), n, None, &source),
                    "namespace" => store.add_namespace(n, &source),
                    "expr_ref" => store.add_ref(n, n, resolve_reference_ty(n), &source),
                    "group" => store.add_group(n, &source),
                    "attrib" => store.add_attribute(n, &source),

                    _ => {}
                }
            }
        }
        let mut scopes: GraphMap<SymbolID, (), Directed> = GraphMap::new();
        let root_scope = SymbolID::Namespace;

        //Add groups and expressions
        for i in cursor.matches(
            &TS.queries.extract_dependencies,
            tree.root_node(),
            source.as_bytes(),
        ) {
            match i.pattern_index {
                0 => {
                    //Add group info
                    if let Some(&inner) = store.ts2sym.get(&i.captures[1].node.id()) {
                        if let Some(&outer) = store.ts2sym.get(&i.captures[0].node.id()) {
                            store.dep.add_edge(outer, inner, LocalEdge::Group);
                        }
                    }
                }
                1 => {
                    //Add constraints
                    if let Some(e) = parse::parse_expr(i.captures[0].node, &store.ts2sym, &source) {
                        store.exprs.push(e)
                    }
                }
                2 => {
                    if let Some(&inner) = store.ts2sym.get(&i.captures[1].node.id()) {
                        if let Some(&outer) = store.ts2sym.get(&i.captures[0].node.id()) {
                            scopes.add_edge(root_scope, outer, ());
                            scopes.add_edge(outer, inner, ());
                        }
                    }
                    //Add scopes for attributes
                }
                3 => {
                    if let Some(&inner) = store.ts2sym.get(&i.captures[1].node.id()) {
                        if let Some(&outer) = store.ts2sym.get(&i.captures[0].node.id()) {
                            scopes.add_edge(outer, inner, ());
                            //Add scopes for attributes
                        }
                    }
                }
                _ => {}
            }
        }
        let mut dfs = Dfs::new(&scopes, root_scope);
        while let Some(i) = dfs.next(&scopes) {
            if let Some(owner) = scopes.neighbors_directed(i, Direction::Incoming).next() {
                match i {
                    SymbolID::AttributeVoid(id)
                    | SymbolID::AttributeNumber(id)
                    | SymbolID::AttributeString(id)
                    | SymbolID::AttributeAttributes(id)
                    | SymbolID::AttributeVector(id)
                    | SymbolID::AttributeBool(id)
                    | SymbolID::AttributeUnknown(id) => {
                        let mut scope = match store.get(owner).unwrap() {
                            SymbolRef::Attribute(a) => a.scope.clone(),
                            SymbolRef::Feature(f) => Path {
                                names: vec![f.name.name],
                                spans: vec![f.name.span.clone()],
                            },
                            _ => {
                                info!("failed to macth attribute");
                                Path::default()
                            }
                        };
                        let name = store.attributes[id as usize].name.clone();
                        scope.names.push(name.name);
                        scope.spans.push(name.span);
                        store.index.insert(scope.names.clone(), i);
                        store.attributes[id as usize].scope = scope;
                    }
                    _ => {}
                }
            }
        }
        store.index.sort();
        let path_raw = uri_to_path(&url).unwrap_or(vec![url.path().into()]);
        info!("Indexed document in {:?}", t.elapsed());

        Self {
            tree: tree.clone(),
            rope: rope.clone(),
            timestamp,
            store,
            source,
            name: Ustr::from(url.as_str()),
            path: path_raw,
            uri: url.clone(),
        }
    }
    pub fn namespace(&self) -> &[Ustr] {
        self.store
            .namespace
            .as_ref()
            .map(|n| n.prefix.names.as_slice())
            .unwrap_or(&[])
    }
}

pub enum RootSymbolID {
    Module(NodeIndex),
    Symbol(Ustr, SymbolID),
}

pub type FileGraphs = im::HashMap<Ustr, FileGraph>;

#[derive(Debug, Clone)]
pub struct RootGraph {
    pub files: im::HashMap<Ustr, FileGraph>,
    pub modules: Arc<ModuleGraph>,
}
impl RootGraph {
    pub fn resolve<K, F: FnMut(RootSymbolID) -> Option<K>>(
        &self,
        origin: Ustr,
        query: &[Ustr],
        fun: F,
    ) -> Option<K> {
        self.modules.resolve(origin, query, &self.files, fun)
    }
    pub fn new(files: im::HashMap<Ustr, FileGraph>) -> Self {
        Self {
            modules: Arc::new(ModuleGraph::new(&files)),
            files,
        }
    }
    pub fn dump(&self) {
        self.modules.dump();
        info!("{:#?}", &self.files);
    }
}
pub enum DraftUpdate {
    Put {
        uri: Url,
        timestamp: Instant,
        tree: Tree,
        source: Rope,
    },

    Delete {
        uri: Ustr,
        timestamp: Instant,
    },
}
pub struct Context {
    pub root: RwLock<RootGraph>,
    pub revison_counter: AtomicU64,
    pub shutdown: CancellationToken,
    pub tx_draft_updates: mpsc::Sender<DraftUpdate>,
    pub client: Client,
}
impl Context {
    pub async fn delete(&self, uri: &Url, timestamp: Instant) {
        self.revison_counter
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let _ = self
            .tx_draft_updates
            .send(DraftUpdate::Delete {
                uri: uri.as_str().into(),
                timestamp,
            })
            .await;
    }
}
struct State {
    files: im::HashMap<Ustr, FileGraph>,
    changes: Vec<DraftUpdate>,
    last_update: Instant,
    revision_counter: u64,
    latest_change: HashMap<Ustr, Instant>,
    check_state: HashMap<Ustr, check::DocumentState>,
}
impl State {
    async fn update(&mut self, change: DraftUpdate, ctx:& Arc<Context>) {
        self.changes.push(change);
        self.revision_counter += 1;
        if ctx
            .revison_counter
            .load(std::sync::atomic::Ordering::SeqCst)
            != self.revision_counter
            && self.last_update.elapsed() < Duration::from_millis(500)
        {
            info!(
                "Dont rebuild modules {} {}",
                self.revision_counter,
                ctx.revison_counter
                    .load(std::sync::atomic::Ordering::SeqCst)
            );
            return;
        }
        let update_timestamp = ctx
            .revison_counter
            .load(std::sync::atomic::Ordering::SeqCst);
        self.changes.sort_by_key(|e| match e {
            DraftUpdate::Put { timestamp, .. } => *timestamp,
            DraftUpdate::Delete { timestamp, .. } => *timestamp,
        });
        let mut to_create = HashMap::new();

        for i in self.changes.drain(0..).rev() {
            let uri = match &i {
                DraftUpdate::Put { uri, .. } => uri.as_str().into(),
                DraftUpdate::Delete { uri, .. } => *uri,
            };
            match i {
                DraftUpdate::Put {
                    uri,
                    timestamp,
                    tree,
                    source,
                } => {
                    if self
                        .latest_change
                        .get(&uri.as_str().into())
                        .map(|old| *old >= timestamp)
                        .unwrap_or(false)
                    {
                        continue;
                    }

                    self.latest_change.insert(uri.as_str().into(), timestamp);
                    to_create.insert(Ustr::from(uri.as_str()), (uri, timestamp, tree, source));
                }
                DraftUpdate::Delete { uri, timestamp } => {
                    if self
                        .latest_change
                        .get(&uri)
                        .map(|old| *old >= timestamp)
                        .unwrap_or(false)
                    {
                        continue;
                    }
                    self.latest_change.insert(uri, timestamp);
                    self.check_state.remove(&uri);
                    self.files.remove(&uri);
                }
            }
        }
        let (dirty, mut new_graphs): (Vec<_>, Vec<_>) = to_create
            .par_drain()
            .map(|(key, (url, timestamp, tree, rope))| {
                (key, FileGraph::new(timestamp, tree, rope, url))
            })
            .collect();

        for i in new_graphs.drain(..) {
            //info!("{:#?}",&i);
            self.files.insert(i.name, i);
        }
        let mut new_check_state: Vec<check::DocumentState> = Vec::new();
        rayon::scope(|s| {
            s.spawn(|_| {
                *ctx.root.write() = RootGraph::new(self.files.clone());
            });
            s.spawn(|_| {
                new_check_state = dirty
                    .par_iter()
                    .map(|fname| check::check_document(&self.files[fname]))
                    .collect();
            })
        });
        if update_timestamp
            != ctx
                .revison_counter
                .load(std::sync::atomic::Ordering::SeqCst)
        {
            return;
        }
        for (i, state) in new_check_state.drain(..).enumerate() {
            self.check_state.insert(dirty[i], state);
        }

        tokio::spawn(check::fininalize(
            ctx.root.read().clone(),
            self.check_state.clone(),
            dirty,
            ctx.clone(),
            update_timestamp
        ));
    }
}

async fn handler_impl(ctx: Arc<Context>, mut rx: mpsc::Receiver<DraftUpdate>) {
    let mut state = State {
        check_state: HashMap::new(),
        latest_change: HashMap::new(),
        revision_counter: 0,
        changes: Vec::new(),
        last_update: Instant::now(),
        files: im::HashMap::new(),
    };

    loop {
        select! {
            _ = ctx.shutdown.cancelled() => return,
            Some(c) = rx.recv()=>state.update(c,&ctx).await

        }
    }
}

pub fn create_handler(
    client: Client,
    shutdown: CancellationToken,
    drafts: Arc<DashMap<Url, AsyncDraft>>,
) -> Arc<Context> {
    let (tx, rx) = mpsc::channel(1024);
    let ctx = Arc::new(Context {
        shutdown,
        tx_draft_updates: tx,
        client,
        revison_counter: AtomicU64::new(0),
        root: RwLock::new(RootGraph {
            files: Default::default(),
            modules: Arc::new(ModuleGraph::default()),
        }),
    });
    spawn(handler_impl(ctx.clone(), rx));
    ctx
}
