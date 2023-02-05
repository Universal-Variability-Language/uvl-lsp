use crate::ast::*;
use crate::check;
use crate::check::ErrorInfo;
use crate::document::{AsyncDraft, DocumentStore};
use crate::smt::check_smt;
use crate::util::lsp_range;
use compact_str::CompactStringExt;
use dashmap::DashMap;
use hashbrown::{HashMap, HashSet};
use log::info;
use parking_lot::Mutex;
use petgraph::prelude::*;
use petgraph::unionfind::UnionFind;
use petgraph::visit::IntoEdges;
use std::borrow::Borrow;
use std::fmt::Debug;
use std::ops::{Deref, Index};
use std::sync::atomic::AtomicU64;
use std::sync::atomic::Ordering;
use std::sync::Arc;
use tokio::sync::Notify;
use tokio::sync::Semaphore;
use tokio::time::{Duration, Instant};
use tokio::{select, spawn};
use tokio_util::sync::CancellationToken;
use tower_lsp::lsp_types::*;
use tower_lsp::Client;
use ustr::Ustr;

#[derive(Hash, PartialEq, Eq, Debug, Clone, Copy)]
pub struct FileID(pub u16);
#[derive(Hash, PartialEq, Eq, Debug, Clone, Copy)]
pub struct RootSymbol {
    pub file: FileID,
    pub sym: Symbol,
}

#[derive(Debug, Clone)]
enum FSEdge {
    Path(Ustr),
    Import(Symbol),
}

#[derive(Debug, Clone)]
pub enum FSNode {
    Dir,
    File(FileID),
}

impl FSNode {
    fn is_dir(&self) -> bool {
        match self {
            Self::Dir => true,
            _ => false,
        }
    }
}
//Simple virtual filesystem for fast completions, resolve and namespaces
#[derive(Debug, Clone)]
pub struct FileSystem {
    graph: DiGraph<FSNode, FSEdge>,
    file2node: HashMap<FileID, NodeIndex>,
}
impl FileSystem {
    fn new(files: &Vec<Arc<Document>>) -> Self {
        let mut graph = DiGraph::new();
        let mut file2node = HashMap::new();
        let root = graph.add_node(FSNode::Dir);
        //create file system
        for (n, f) in files.iter().enumerate().map(|(i, f)| (FileID(i as u16), f)) {
            let mut dir = root;
            for i in f.path[0..f.path.len() - 1].iter() {
                if let Some(old) = graph.edges(dir).find(|e| match e.weight() {
                    FSEdge::Path(name) => name == i && graph[e.target()].is_dir(),
                    _ => false,
                }) {
                    dir = old.target();
                } else {
                    let new = graph.add_node(FSNode::Dir);
                    graph.add_edge(dir, new, FSEdge::Path(*i));
                    dir = new;
                }
            }
            let id = graph.add_node(FSNode::File(n));
            graph.add_edge(dir, id, FSEdge::Path(*f.path.last().unwrap()));
            file2node.insert(n, id);
        }
        //resolve imports
        for (n, f) in files.iter().enumerate().map(|(i, f)| (FileID(i as u16), f)) {
            for i in f.all_imports() {
                let path = f.path(i);
                let mut node = graph
                    .neighbors_directed(file2node[&n], Incoming)
                    .find(|n| matches!(graph[*n], FSNode::Dir))
                    .unwrap();
                let mut ok = true;
                for (k, i) in path.iter().enumerate() {
                    if let Some(e) = graph.edges(node).find(|e| match e.weight() {
                        FSEdge::Path(name) => {
                            name == i && (!(k == path.len() - 1) || !graph[e.target()].is_dir())
                        }
                        _ => false,
                    }) {
                        node = e.target();
                    } else {
                        ok = false;
                        break;
                    }
                }

                if ok {
                    graph.add_edge(file2node[&n], node, FSEdge::Import(i));
                } else {
                    info!("Cant find {:?} ", path);
                }
            }
        }
        Self { graph, file2node }
    }
    //Check an import between a and b
    pub fn imports_connecting<'a>(
        &'a self,
        a: FileID,
        b: FileID,
    ) -> impl Iterator<Item = Symbol> + 'a {
        self.graph
            .edges_connecting(self.file2node[&a], self.file2node[&b])
            .filter_map(|e| match e.weight() {
                FSEdge::Import(sym) => Some(*sym),
                _ => None,
            })
    }
    //all imports from a
    pub fn imports<'a>(&'a self, a: FileID) -> impl Iterator<Item = (Symbol, FileID)> + 'a {
        self.graph.edges(self.file2node[&a]).filter_map(|e| {
            match (e.weight(), &self.graph[e.target()]) {
                (FSEdge::Import(sym), FSNode::File(name)) => Some((*sym, *name)),
                _ => None,
            }
        })
    }

    //all imports to a
    pub fn imported<'a>(&'a self, a: FileID) -> impl Iterator<Item = (Symbol, FileID)> + 'a {
        self.graph.edges_directed(self.file2node[&a],Direction::Incoming).filter_map(|e| {
            match (e.weight(), &self.graph[e.source()]) {
                (FSEdge::Import(sym), FSNode::File(name)) => Some((*sym, *name)),
                _ => None,
            }
        })
    }
    //all subfiles from origin under path, returns (prefix,filename,filenode)
    pub fn sub_files<'a>(
        &'a self,
        origin: FileID,
        path: &[Ustr],
    ) -> impl Iterator<Item = (compact_str::CompactString, Ustr, FSNode)> + 'a {
        let mut dir = self
            .graph
            .neighbors_directed(self.file2node[&origin], Incoming)
            .find(|n| matches!(self.graph[*n], FSNode::Dir))
            .unwrap();
        let mut valid_path = true;
        for i in path.iter() {
            if let Some(e) = self.graph.edges(dir).find(|e| match e.weight() {
                FSEdge::Path(name) => name == i && self.graph[e.target()].is_dir(),
                _ => false,
            }) {
                dir = e.target();
            } else {
                valid_path = false;
            }
        }
        let mut stack: Vec<(compact_str::CompactString, _, _)> = Vec::new();
        if valid_path {
            for i in self.graph.edges(dir) {
                match i.weight() {
                    FSEdge::Path(name) => stack.push((name.as_str().into(), *name, i.target())),
                    _ => {}
                }
            }
        }
        std::iter::from_fn(move || {
            stack.pop().and_then(|(path, name, node)| {
                for i in self.graph.edges(node) {
                    match i.weight() {
                        FSEdge::Path(name) => stack.push((
                            [path.as_str(), name.as_str()].join_compact("."),
                            *name,
                            i.target(),
                        )),
                        _ => {}
                    }
                }
                Some((path, name, self.graph[node].clone()))
            })
        })
        .filter(move |(_, _, node)| match node {
            FSNode::File(tgt) => tgt != &origin,
            _ => true,
        })
    }
}
//1 to N reference relation map
#[derive(Debug, Clone, Default)]
pub struct ReferenceMap {
    resolved: HashMap<RootSymbol, RootSymbol>,
    reverse: HashMap<RootSymbol, Vec<RootSymbol>>,
}
impl ReferenceMap {
    pub fn insert(&mut self, src: RootSymbol, dst: RootSymbol) {
        self.resolved.insert(src.clone(), dst.clone());
        insert_multi(&mut self.reverse, dst, src);
    }
    pub fn resolve(&self, src: RootSymbol) -> Option<RootSymbol> {
        self.resolved.get(&src).cloned()
    }
    pub fn used_by<'a>(&'a self, dst: RootSymbol) -> impl Iterator<Item = RootSymbol> + 'a {
        self.reverse
            .get(&dst)
            .into_iter()
            .flat_map(|i| i.iter().cloned())
    }
    pub fn iter<'a>(&'a self) -> impl Iterator<Item = (RootSymbol, RootSymbol)> + 'a {
        self.resolved.iter().map(|(k, v)| (k.clone(), v.clone()))
    }
}
impl<T> Index<FileID> for Vec<T> {
    type Output = T;
    fn index(&self, index: FileID) -> &Self::Output {
        &self[index.0 as usize]
    }
}
//A fully linked version of all files, computed asynchronously
#[derive(Debug, Clone)]
pub struct RootGraph {
    files: Vec<Arc<Document>>,
    pub fs: FileSystem,
    ref_map: ReferenceMap,
    index: HashMap<Url, FileID>,
    revision: u64,
}
impl RootGraph {
    pub fn file_by_uri(&self, name: &Url) -> Option<&Document> {
        self.index.get(name).map(|id| self.file(*id))
    }
    pub fn file(&self, id: FileID) -> &Document {
        &self.files[id]
    }
    pub fn file_id(&self, name: &Url) -> Option<FileID> {
        self.index.get(name).cloned()
    }
    pub fn resolve_sym<'a>(&'a self, sym: RootSymbol) -> Option<RootSymbol> {
        match sym.sym {
            Symbol::Reference(..) => self.ref_map.resolve(sym).or_else(|| {
                let file = self.file(sym.file);
                let path = file.path(sym.sym);
                let ty = file.type_of(sym.sym);
                for dst in self.resolve(sym.file, path) {
                    if self.file(dst.file).type_of(dst.sym) == ty {
                        return Some(dst);
                    }
                }
                None
            }),
            _ => Some(sym),
        }
    }
    pub fn imported(&self, src: FileID) -> Vec<FileID> {
        let mut out  = HashSet::new();
        let mut stack = vec![src];
        while let Some(src) = stack.pop(){
            for (_,tgt) in self.fs.imported(src){
                stack.push(tgt);
                out.insert(tgt);
            }
        }
        out.drain().collect()
    }
    pub fn connected_components(&self)->Vec<Vec<FileID>>{
        let mut union_find = UnionFind::new(self.files.len());
        for e in self.fs.graph.edge_references().filter(|e|matches!(e.weight(),FSEdge::Import(..))){
            let (a, b) = (e.source(), e.target());
            // union the two vertices of the edge
            union_find.union(a.index(),b.index());
        }
        let mut map = HashMap::new();
        for i in 0..self.files.len() {
            let rep = union_find.find(i);
            insert_multi(&mut map, rep, i);
        }
        map.into_values()
            .map(|i| i.iter().map(|j| FileID(*j as u16)).collect())
            .collect()
    }
    //find all symbols from origin under path
    pub fn resolve<'a>(
        &'a self,
        origin: FileID,
        path: &'a [Ustr],
    ) -> impl Iterator<Item = RootSymbol> + 'a {
        let mut stack = vec![(origin, path)];
        std::iter::from_fn(move || {
            stack.pop().and_then(|(file, tail)| {
                for (sym, tgt) in self.fs.imports(file) {
                    let common_prefix = self.files[file]
                        .import_prefix(sym)
                        .iter()
                        .zip(tail.iter())
                        .take_while(|(i, k)| i == k)
                        .count();

                    if common_prefix == self.files[file].import_prefix(sym).len() {
                        stack.push((tgt, &tail[common_prefix..]));
                    }
                }
                Some(
                    self.files[file]
                        .lookup(Symbol::Root, tail, |_| true)
                        .map(move |sym| RootSymbol { file, sym }),
                )
            })
        })
        .flatten()
    }
    pub fn resolve_with_binding<'a>(
        &'a self,
        origin: FileID,
        path: &'a [Ustr],
    ) -> impl Iterator<Item = Vec<(RootSymbol, usize)>> + 'a {
        let mut stack = vec![(origin, path, vec![])];
        std::iter::from_fn(move || {
            stack.pop().and_then(|(file, tail, binding)| {
                let src_file = &self.files[file];
                for (sym, tgt) in self.fs.imports(file) {
                    let common_prefix = src_file
                        .import_prefix(sym)
                        .iter()
                        .zip(tail.iter())
                        .take_while(|(i, k)| i == k)
                        .count();

                    if common_prefix == src_file.import_prefix(sym).len() {
                        stack.push((
                            tgt,
                            &tail[common_prefix..],
                            [
                                binding.as_slice(),
                                &[(RootSymbol { sym, file }, common_prefix)],
                            ]
                            .concat(),
                        ));
                    }
                }
                Some(
                    src_file
                        .lookup_with_binding(Symbol::Root, tail, |_| true)
                        .map(move |sub_binding| {
                            let mut offset = 0;
                            binding
                                .iter()
                                .cloned()
                                .chain(
                                    sub_binding
                                        .iter()
                                        .map(|i| (RootSymbol { file, sym: *i }, 1)),
                                )
                                .map(move |(sym, len)| {
                                    offset += len;
                                    (sym, offset)
                                })
                                .collect()
                        }),
                )
            })
        })
        .flatten()
    }
    //find all attributes from origin under context, usefull for aggregates
    pub fn resolve_attributes<'a, F: FnMut(RootSymbol, &[Ustr])>(
        &'a self,
        origin: FileID,
        context: &'a [Ustr],
        mut f: F,
    ) {
        self.resolve_attributes_with_feature(origin, context, |_, attrib, prefix, _| {
            f(attrib, prefix)
        });
    }
    pub fn resolve_attributes_with_feature<
        'a,
        F: FnMut(RootSymbol, RootSymbol, &[Ustr], &Document),
    >(
        &'a self,
        origin: FileID,
        context: &'a [Ustr],
        mut f: F,
    ) {
        for root in self.resolve(origin, context) {
            let file = &self.files[root.file];
            //info!("resolved {:?}", root);
            let mut owner = None;
            file.visit_named_children(root.sym, false, |i, prefix| match i {
                Symbol::Feature(..) => {
                    owner = Some(RootSymbol {
                        file: root.file,
                        sym: i,
                    });
                    true
                }
                Symbol::Attribute(..) => {
                    info!("attrib {:?}", prefix);
                    f(
                        owner.unwrap(),
                        RootSymbol {
                            sym: i,
                            file: root.file,
                        },
                        &prefix[1..],
                        file,
                    );
                    true
                }
                _ => false,
            });
        }
    }
    pub fn iter_files<'a>(&'a self) -> impl Iterator<Item = (FileID, &'a Document)> + 'a {
        self.files
            .iter()
            .enumerate()
            .map(|(i, f)| (FileID(i as u16), f.borrow()))
    }
    pub fn iter_file_ids(&self) -> impl Iterator<Item = FileID> {
        (0..self.files.len()).map(|i| FileID(i as u16))
    }
    pub fn new(file_map: &HashMap<Url, Arc<Document>>, revision: u64) -> Self {
        let files = file_map.values().cloned().collect();
        Self {
            fs: FileSystem::new(&files),
            index: file_map
                .keys()
                .enumerate()
                .map(|(i, k)| (k.clone(), FileID(i as u16)))
                .collect(),
            files,
            ref_map: Default::default(),
            revision,
        }
    }
    pub fn dump(&self) {
        info!("{:#?}", &self.files);
    }
    fn link_file(&mut self, src_file_id: FileID) -> Vec<ErrorInfo> {
        enum ReferenceResolveState {
            Unresolved,
            WrongType(Type),
            Resolved(RootSymbol),
        }
        let src = &self.files[src_file_id.0 as usize];
        let mut errors = Vec::new();
        for (id, i) in src
            .references()
            .iter()
            .enumerate()
            .map(|(i, k)| (Symbol::Reference(i as u32), k))
        {
            let mut state = ReferenceResolveState::Unresolved;
            for k in self.resolve(src_file_id, &i.path.names) {
                let dst = self.file(k.file);
                if i.ty == dst.type_of(k.sym).unwrap() {
                    state = ReferenceResolveState::Resolved(k);
                    break;
                } else {
                    state = ReferenceResolveState::WrongType(dst.type_of(k.sym).unwrap());
                }
            }
            match state {
                ReferenceResolveState::Unresolved => errors.push(ErrorInfo {
                    location: lsp_range(i.path.range(), &src.source).unwrap(),
                    severity: DiagnosticSeverity::ERROR,
                    weight: 30,
                    msg: "unresolved reference".into(),
                }),
                ReferenceResolveState::WrongType(ty) => errors.push(ErrorInfo {
                    location: lsp_range(i.path.range(), &src.source).unwrap(),
                    severity: DiagnosticSeverity::ERROR,
                    weight: 30,
                    msg: format!("expected a {:?} got {:?}", i.ty, ty),
                }),
                ReferenceResolveState::Resolved(sym) => {
                    self.ref_map.insert(
                        RootSymbol {
                            sym: id,
                            file: src_file_id,
                        },
                        sym,
                    );
                }
            }
        }
        errors
    }
    async fn link(&mut self, ctx: &Context) {
        for i in self.iter_file_ids() {
            let err = self.link_file(i);
            let file = self.file(i);
            if file.errors.len() == 0 && ctx.ready() {
                check::publish(&ctx.client, &file.uri, &err).await;
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct Snapshot {
    revision: u64,
    lock: Arc<tokio::sync::OwnedRwLockReadGuard<RootGraph>>,
    revison_counter_linked: Arc<AtomicU64>,
}
impl Snapshot {
    async fn new(ctx: &Context) -> Self {
        let lock = tokio::sync::RwLock::read_owned(ctx.root.clone()).await;
        Self {
            revision: lock.revision,
            lock: Arc::new(lock),
            revison_counter_linked: ctx.revison_counter_linked.clone(),
        }
    }
}
impl Deref for Snapshot {
    type Target = RootGraph;
    fn deref(&self) -> &Self::Target {
        &*self.lock
    }
}
//Central synchronisation provider
pub struct Context {
    //latest red trees
    pub documents: Mutex<DocumentStore>,
    //notified when there is a changed red tree
    pub dirty: Notify,
    //latest linked version
    pub root: Arc<tokio::sync::RwLock<RootGraph>>,
    pub revison_counter: AtomicU64,
    pub revison_counter_parsed: AtomicU64,
    pub revison_counter_linked: Arc<AtomicU64>,
    pub shutdown: CancellationToken,
    pub client: Client,
    //limit the amount of parallel background tasks to keep the server responsiv
    //TODO find a better way
    pub load_files_sema: Semaphore,
}
impl Context {
    //Make sure uri is inside the snapshot
    pub async fn snapshot(&self, uri: &Url) -> Snapshot {
        let time = Instant::now();
        loop {
            {
                let snap = Snapshot::new(self).await;
                if snap.index.contains_key(uri) {
                    info!("waited {:?} for root", time.elapsed());
                    return snap;
                }
            }
            tokio::time::sleep(Duration::from_millis(5)).await;
        }
    }
    //Assure uri exists and wait for till the linker catched up
    pub async fn snapshot_sync(&self, uri: &Url) -> Snapshot {
        let time = Instant::now();
        let base = self
            .revison_counter
            .load(std::sync::atomic::Ordering::SeqCst);
        loop {
            {
                let snap = Snapshot::new(self).await;
                if snap.index.contains_key(uri) && snap.revision >= base {
                    info!("waited {:?} for root", time.elapsed());
                    return snap;
                }
            }
            tokio::time::sleep(Duration::from_millis(5)).await;
        }
    }
    pub fn ready(&self) -> bool {
        self.revison_counter
            .load(std::sync::atomic::Ordering::SeqCst)
            == self
                .revison_counter_parsed
                .load(std::sync::atomic::Ordering::SeqCst)
    }
}
async fn check_namespaces(ctx: &Context, root: &RootGraph) {
    let mut file_paths = HashSet::new();
    for file in root.files.iter() {
        if !file_paths.insert(file.path.as_slice()) {
            if let Some(ns) = file.namespace() {
                check::publish(
                    &ctx.client,
                    &file.uri,
                    &[check::ErrorInfo {
                        location: lsp_range(ns.range(), &file.source).unwrap(),
                        severity: DiagnosticSeverity::ERROR,
                        weight: 100,
                        msg: "namespace already defined".into(),
                    }],
                )
                .await
            }
        }
    }
}
async fn publish_syntax_error(
    ctx: &Context,
    root: &RootGraph,
    check_state: &mut HashMap<Ustr, Instant>,
) {
    for file in root.files.iter() {
        if check_state
            .get(&file.name)
            .map(|old| old < &file.timestamp)
            .unwrap_or(true)
            && file.errors.len() > 0
        {
            check_state.insert(file.name, file.timestamp);
            if ctx.ready() {
                check::publish(&ctx.client, &file.uri, &file.errors).await;
            }
        }
    }
}

async fn update_root_graph(ctx: &Context, check_state: &mut HashMap<Ustr, Instant>) -> RootGraph {
    let timer = Instant::now();
    let mut root = {
        let docs = ctx.documents.lock();
        RootGraph::new(&docs.ast, docs.revision)
    };
    publish_syntax_error(ctx, &root, check_state).await;
    root.link(ctx).await;
    info!("updated root graph {:?}", timer.elapsed());

    root
}

async fn handler_impl(ctx: Arc<Context>) {
    let mut check_state = HashMap::new();
    loop {
        select! {
            _ = ctx.shutdown.cancelled() => return,
            _ = ctx.dirty.notified() =>{
                let new= update_root_graph(&ctx,&mut check_state).await;
                ctx.revison_counter_linked.fetch_add(1,Ordering::SeqCst);
                *ctx.root.write().await = new;
            }
        }
    }
}

pub fn create_handler(
    client: Client,
    shutdown: CancellationToken,
    _: Arc<DashMap<Url, AsyncDraft>>,
) -> Arc<Context> {
    let root = Arc::new(tokio::sync::RwLock::new(RootGraph {
        ref_map: ReferenceMap::default(),
        index: HashMap::new(),
        fs: FileSystem {
            graph: Default::default(),
            file2node: HashMap::new(),
        },
        files: Default::default(),
        revision: 0,
    }));
    let ctx = Arc::new(Context {
        load_files_sema: Semaphore::new((num_cpus::get() - 1).max(1)),
        shutdown,
        dirty: Notify::new(),
        client,
        revison_counter: AtomicU64::new(0),
        revison_counter_parsed: AtomicU64::new(0),
        revison_counter_linked: Arc::new(AtomicU64::new(0)),
        documents: Mutex::new(DocumentStore::default()),
        root,
    });
    spawn(handler_impl(ctx.clone()));
    ctx
}
