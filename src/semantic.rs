use crate::ast::*;
use crate::check;
use crate::check::DiagnosticUpdate;
use crate::check::ErrorInfo;
use crate::document::{AsyncDraft, DocumentStore};
use crate::smt::check_smt;
use crate::util::lsp_range;
use crate::util::AtomicSemaphore;
use compact_str::CompactStringExt;
use dashmap::DashMap;
use hashbrown::{HashMap, HashSet};
use log::info;
use parking_lot::Mutex;
use petgraph::prelude::*;
use petgraph::unionfind::UnionFind;
use std::borrow::Borrow;
use std::collections::BTreeSet;
use std::fmt::Debug;
use std::ops::Index;
use std::sync::Arc;
use tokio::sync::mpsc;
use tokio::sync::{watch, RwLock, RwLockReadGuard, Semaphore};
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
//Central synchronisation provider
pub struct Context {
    //latest red trees
    pub documents: Mutex<watch::Sender<DocumentStore>>,
    //latest linked state
    pub root: Arc<RwLock<RootGraph>>,
    pub tx_err: mpsc::Sender<DiagnosticUpdate>,
    pub shutdown: CancellationToken,
    pub client: Client,
    //limit the amount of parallel background tasks to keep the server responsiv
    //TODO find a better way
    pub load_files_sema: Semaphore,
    pub parser_active: AtomicSemaphore,
}
pub type Snapshot<'a> = RwLockReadGuard<'a, RootGraph>;
impl Context {
    //Make sure uri is inside the snapshot
    pub async fn snapshot(&self, uri: &Url) -> Option<Snapshot> {
        let time = Instant::now();
        loop {
            {
                let snap = self.root.read().await;
                if snap.index.contains_key(uri) {
                    info!("waited {:?} for root", time.elapsed());
                    return Some(snap);
                }
            }
            tokio::time::sleep(Duration::from_millis(5)).await;
            if self.shutdown.is_cancelled() {
                return None;
            }
        }
    }
    //Assure uri exists and wait for the linker to catched up
    pub async fn snapshot_sync(&self, uri: &Url, timestamp: Instant) -> Option<Snapshot> {
        let time = Instant::now();
        loop {
            {
                let snap = self.root.read().await;
                if snap
                    .file_by_uri(uri)
                    .map(|file| file.timestamp >= timestamp)
                    .unwrap_or(false)
                {
                    info!("waited {:?} for root", time.elapsed());
                    return Some(snap);
                }
            }
            tokio::time::sleep(Duration::from_millis(5)).await;
            if self.shutdown.is_cancelled() {
                return None;
            }
        }
    }
    pub async fn publish_err(&self, mut err: HashMap<FileID, Vec<ErrorInfo>>, root: &RootGraph) {
        let _ = self
            .tx_err
            .send(DiagnosticUpdate {
                error_state: err
                    .drain()
                    .map(|(file, err)| (root.file(file).uri.clone(), err))
                    .collect(),
                timestamp: root.revision,
            })
            .await;
    }
}

#[derive(Debug, Clone, PartialEq)]
enum FSEdge {
    Path(Ustr),
    Import(Symbol),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FSNode {
    Dir,
    File(FileID),
}

impl FSNode {
    fn is_dir(&self) -> bool {
        matches!(self, Self::Dir)
    }
}
//Simple virtual filesystem for fast completions, resolve and namespaces
#[derive(Debug, Clone)]
pub struct FileSystem {
    graph: DiGraph<FSNode, FSEdge>,
    file2node: HashMap<FileID, NodeIndex>,
}
impl FileSystem {
    fn new(files: &[Arc<Document>]) -> Self {
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
                            name == i && (k != path.len() - 1 || !graph[e.target()].is_dir())
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
    pub fn imports_connecting(&self, a: FileID, b: FileID) -> impl Iterator<Item = Symbol> + '_ {
        self.graph
            .edges_connecting(self.file2node[&a], self.file2node[&b])
            .filter_map(|e| match e.weight() {
                FSEdge::Import(sym) => Some(*sym),
                _ => None,
            })
    }
    //all imports from a
    pub fn imports(&self, a: FileID) -> impl Iterator<Item = (Symbol, FileID)> + '_ {
        self.graph.edges(self.file2node[&a]).filter_map(|e| {
            match (e.weight(), &self.graph[e.target()]) {
                (FSEdge::Import(sym), FSNode::File(name)) => Some((*sym, *name)),
                _ => None,
            }
        })
    }

    //all imports to a
    pub fn imported(&self, a: FileID) -> impl Iterator<Item = (Symbol, FileID)> + '_ {
        self.graph
            .edges_directed(self.file2node[&a], Direction::Incoming)
            .filter_map(|e| match (e.weight(), &self.graph[e.source()]) {
                (FSEdge::Import(sym), FSNode::File(name)) => Some((*sym, *name)),
                _ => None,
            })
    }

    pub fn resolve(&self, origin: FileID, path: &[Ustr]) -> Option<FileID> {
        let mut dir = self
            .graph
            .neighbors_directed(self.file2node[&origin], Incoming)
            .find(|n| matches!(self.graph[*n], FSNode::Dir))
            .unwrap();
        for i in path[0..path.len() - 1].iter() {
            if let Some(e) = self.graph.edges(dir).find(|e| match e.weight() {
                FSEdge::Path(name) => name == i && self.graph[e.target()].is_dir(),
                _ => false,
            }) {
                dir = e.target();
            } else {
                return None
            }
        }
        self.graph.edges(dir).find_map(|e| {
            if let FSEdge::Path(name) = e.weight() {
                if name == path.last().unwrap() {
                    if let FSNode::File(id) = self.graph[e.target()] {
                        return Some(id);
                    }
                }
            }
            None
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
            stack.pop().map(|(path, name, node)| {
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
                (path, name, self.graph[node].clone())
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
}
impl ReferenceMap {
    pub fn insert(&mut self, src: RootSymbol, dst: RootSymbol) {
        self.resolved.insert(src, dst);
    }
    pub fn resolve(&self, src: RootSymbol) -> Option<RootSymbol> {
        self.resolved.get(&src).cloned()
    }
    pub fn iter(&self) -> impl Iterator<Item = (RootSymbol, RootSymbol)> + '_ {
        self.resolved.iter().map(|(k, v)| (*k, *v))
    }
}
impl<T> Index<FileID> for Vec<T> {
    type Output = T;
    fn index(&self, index: FileID) -> &Self::Output {
        &self[index.0 as usize]
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ComponentErrorState {
    SyntaxError,
    LinkError,
    Valid,
}

#[derive(Debug, Clone)]
pub struct Component {
    pub members: Vec<FileID>,
    pub error: ComponentErrorState,
    pub dirty: bool,
}
//A fully linked version of all files, computed asynchronously
#[derive(Debug, Clone)]
pub struct RootGraph {
    files: Vec<Arc<Document>>,
    pub fs: FileSystem,
    pub revision: u64,
    ref_map: ReferenceMap,
    index: HashMap<Url, FileID>,
    components: Vec<Component>,
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
    pub fn resolve_sym(&self, sym: RootSymbol) -> Option<RootSymbol> {
        match sym.sym {
            Symbol::Reference(..) => self.ref_map.resolve(sym).or_else(|| {
                let file = self.file(sym.file);
                let path = file.path(sym.sym);
                let ty = file.type_of(sym.sym);
                self.resolve(sym.file, path)
                    .find(|&dst| self.file(dst.file).type_of(dst.sym) == ty)
            }),
            _ => Some(sym),
        }
    }
    pub fn components(&self) -> &[Component] {
        &self.components[..]
    }
    pub fn imported(&self, src: FileID) -> Vec<FileID> {
        let mut out = HashSet::new();
        out.insert(src);
        let mut stack = vec![src];
        while let Some(src) = stack.pop() {
            for (_, tgt) in self.fs.imported(src) {
                stack.push(tgt);
                out.insert(tgt);
            }
        }
        out.drain().collect()
    }
    pub fn importes(&self, src: FileID) -> Vec<FileID> {
        let mut out = HashSet::new();
        out.insert(src);
        let mut stack = vec![src];
        while let Some(src) = stack.pop() {
            for (_, tgt) in self.fs.imports(src) {
                stack.push(tgt);
                out.insert(tgt);
            }
        }
        out.drain().collect()
    }
    pub fn connected_components(&self) -> Vec<Vec<FileID>> {
        let mut union_find = UnionFind::new(self.files.len());
        for e in self
            .fs
            .graph
            .edge_references()
            .filter(|e| matches!(e.weight(), FSEdge::Import(..)))
        {
            let (a, b) = (e.source(), e.target());
            // union the two vertices of the edge
            if let (FSNode::File(a), FSNode::File(b)) = (&self.fs.graph[a], &self.fs.graph[b]) {
                union_find.union(a.0, b.0);
            }
        }
        let mut map = HashMap::new();
        for i in 0..self.files.len() {
            let rep = union_find.find(i as u16);
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
            stack.pop().map(|(file, tail)| {
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
                self.files[file]
                    .lookup(Symbol::Root, tail, |_| true)
                    .map(move |sym| RootSymbol { file, sym })
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
            stack.pop().map(|(file, tail, binding)| {
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
                    })
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
    pub fn iter_files(&self) -> impl Iterator<Item = (FileID, &'_ Document)> + '_ {
        self.files
            .iter()
            .enumerate()
            .map(|(i, f)| (FileID(i as u16), f.borrow()))
    }
    pub fn iter_file_ids(&self) -> impl Iterator<Item = FileID> {
        (0..self.files.len()).map(|i| FileID(i as u16))
    }
    pub fn file_paths(&self) -> BTreeSet<Vec<Ustr>> {
        self.files.iter().map(|f| f.path.clone()).collect()
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
        for id in src.all_references() {
            let path = src.path(id);
            let r_ty = src.type_of(id);
            let mut state = ReferenceResolveState::Unresolved;
            for k in self.resolve(src_file_id, path) {
                let dst = self.file(k.file);
                if r_ty == dst.type_of(k.sym) {
                    state = ReferenceResolveState::Resolved(k);
                    break;
                } else {
                    state = ReferenceResolveState::WrongType(dst.type_of(k.sym).unwrap());
                }
            }
            match state {
                ReferenceResolveState::Unresolved => errors.push(ErrorInfo {
                    location: src.lsp_range(id).unwrap(),
                    severity: DiagnosticSeverity::ERROR,
                    weight: 30,
                    msg: "unresolved reference".into(),
                }),
                ReferenceResolveState::WrongType(ty) => errors.push(ErrorInfo {
                    location: src.lsp_range(id).unwrap(),
                    severity: DiagnosticSeverity::ERROR,
                    weight: 30,
                    msg: format!("expected a {:?} got {:?}", r_ty, ty),
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
    pub fn new(file_map: &HashMap<Url, Arc<Document>>, revision: u64) -> Self {
        let files: Vec<_> = file_map.values().cloned().collect();
        Self {
            components: Vec::new(),
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
}

#[derive(Default)]
struct RootGraphHandler {
    check_state: HashMap<Ustr, Instant>,
    cancel_smt: Option<CancellationToken>,
}
impl RootGraphHandler {
    pub fn collect_changes(&mut self, root: &RootGraph) -> HashMap<FileID, Vec<ErrorInfo>> {
        let mut err = HashMap::new();
        for file in root.files.iter() {
            if self
                .check_state
                .get(&file.name)
                .map(|old| old < &file.timestamp)
                .unwrap_or(true)
            {
                self.check_state.insert(file.name, file.timestamp);
                err.insert(root.file_id(&file.uri).unwrap(), file.errors.clone());
            }
        }
        err
    }
    fn check_namespaces(&self, root: &RootGraph, err_out: &mut HashMap<FileID, Vec<ErrorInfo>>) {
        let mut file_paths = HashSet::new();
        for file in root.files.iter() {
            if !file_paths.insert(file.path.as_slice()) {
                info!("{:?}", file.namespace());
                if let Some(ns) = file.namespace() {
                    let id = root.file_id(&file.uri).unwrap();
                    if let Some(old) = err_out.get_mut(&id) {
                        old.push(check::ErrorInfo {
                            location: lsp_range(ns.range(), &file.source).unwrap(),
                            severity: DiagnosticSeverity::ERROR,
                            weight: 100,
                            msg: "namespace already defined".into(),
                        });
                    }
                }
            }
        }
    }
    pub fn link(
        &self,
        root: &mut RootGraph,
        err_out: &mut HashMap<FileID, Vec<ErrorInfo>>,
        dirty: &HashSet<FileID>,
        dirty_fs: bool,
    ) {
        let mut components: Vec<_> = root
            .connected_components()
            .drain(..)
            .map(|files| Component {
                error: if files
                    .iter()
                    .any(|f| err_out.get(f).map(|err| err.len() > 0).unwrap_or(false))
                {
                    ComponentErrorState::SyntaxError
                } else {
                    ComponentErrorState::Valid
                },
                dirty: files.iter().any(|f| dirty.contains(f)) || dirty_fs,
                members: files,
            })
            .collect();
        //info!("components {:#?}",components);
        for c in components.iter_mut() {
            if c.error == ComponentErrorState::Valid && c.dirty {
                let mut all_ok = true;
                for f in c.members.iter() {
                    if dirty_fs || root.importes(*f).iter().any(|im| dirty.contains(im)) {
                        let err = root.link_file(*f);
                        if err.len() > 0 {
                            all_ok = false;
                        }
                        err_out.insert(*f, err);
                    }
                }
                if !all_ok {
                    c.error = ComponentErrorState::LinkError;
                }
            }
        }
        root.components = components;
    }
    pub async fn update(
        &mut self,
        ctx: &Arc<Context>,
        documents: &mut watch::Receiver<DocumentStore>,
    ) {
        if let Some(token) = self.cancel_smt.take() {
            token.cancel();
        }
        let mut new_root = {
            let docs = documents.borrow_and_update();
            RootGraph::new(&docs.ast, docs.revision)
        };
        if ctx.parser_active.zero() {
            let timer = Instant::now();
            let mut err = self.collect_changes(&new_root);
            self.check_namespaces(&new_root, &mut err);
            let dirty_fs = ctx.root.read().await.file_paths() != new_root.file_paths();
            let dirty_files = err.keys().cloned().collect();
            self.link(&mut new_root, &mut err, &dirty_files, dirty_fs);
            ctx.publish_err(err, &new_root).await;
            info!("linked root graph {:?}", timer.elapsed());
        }
        *ctx.root.write().await = new_root;
        if ctx.parser_active.zero() {
            let token = CancellationToken::new();
            let _ = spawn(check_smt(ctx.clone(), token.clone()));
            self.cancel_smt = Some(token);
        }
    }
}

async fn handler_impl(ctx: Arc<Context>, mut documents: watch::Receiver<DocumentStore>) {
    let mut handler = RootGraphHandler::default();
    loop {
        select! {
            _ = ctx.shutdown.cancelled() => return,
            _ =  documents.changed()=>{
                handler.update(&ctx, &mut documents).await
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
        components: Vec::new(),
        ref_map: ReferenceMap::default(),
        index: HashMap::new(),
        fs: FileSystem {
            graph: Default::default(),
            file2node: HashMap::new(),
        },
        files: Default::default(),
        revision: 0,
    }));
    let (tx_doc, rx_doc) = watch::channel(DocumentStore::default());
    let (tx_err, rx_err) = mpsc::channel(32);

    let ctx = Arc::new(Context {
        load_files_sema: Semaphore::new((num_cpus::get() - 1).max(1)),
        parser_active: AtomicSemaphore::new(),
        tx_err,
        shutdown,
        client,
        documents: Mutex::new(tx_doc),
        root,
    });
    spawn(handler_impl(ctx.clone(), rx_doc));
    spawn(check::diagnostic_handler(ctx.clone(), rx_err));
    ctx
}
