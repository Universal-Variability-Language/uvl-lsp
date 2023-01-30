use crate::ast::*;
use crate::check;
use crate::document::{AsyncDraft, DocumentStore};
use crate::util::lsp_range;
use compact_str::CompactStringExt;
use hashbrown::{HashMap, HashSet};
use parking_lot::Mutex;
use parking_lot::RwLock;

use dashmap::DashMap;
use log::info;
use petgraph::prelude::*;
use std::fmt::Debug;
use std::sync::atomic::AtomicU64;
use std::sync::Arc;
use tokio::sync::Notify;
use tokio::sync::Semaphore;
use tokio::time::{Duration, Instant};
use tokio::{select, spawn};
use tokio_util::sync::CancellationToken;
use tower_lsp::lsp_types::*;
use tower_lsp::Client;
use ustr::Ustr;

#[derive(Hash, PartialEq, Eq, Debug, Clone)]
pub struct RootSymbol {
    pub file: Ustr,
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
    File(Ustr),
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
    graph: Graph<FSNode, FSEdge>,
    file2node: HashMap<Ustr, NodeIndex>,
}
impl FileSystem {
    fn new(files: &im::HashMap<Ustr, Document>) -> Self {
        let mut graph = Graph::new();
        let mut file2node = HashMap::new();
        let root = graph.add_node(FSNode::Dir);
        //create file system
        for (n, f) in files.iter() {
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
            let id = graph.add_node(FSNode::File(*n));
            graph.add_edge(dir, id, FSEdge::Path(*f.path.last().unwrap()));
            file2node.insert(*n, id);
        }
        //resolve imports
        for (n, f) in files.iter() {
            for i in f.imports_iter() {
                let path = f.import_path(i);
                let mut node = graph
                    .neighbors_directed(file2node[n], Incoming)
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
                    graph.add_edge(file2node[n], node, FSEdge::Import(i));
                } else {
                    info!("Cant find {:?} ", path);
                }
            }
        }
        Self { graph, file2node }
    }
    //Check an import between a and b
    pub fn imports_connecting<'a>(&'a self, a: Ustr, b: Ustr) -> impl Iterator<Item = Symbol> + 'a {
        self.graph
            .edges_connecting(self.file2node[&a], self.file2node[&b])
            .filter_map(|e| match e.weight() {
                FSEdge::Import(sym) => Some(*sym),
                _ => None,
            })
    }
    //all imports from a
    pub fn imports<'a>(&'a self, a: Ustr) -> impl Iterator<Item = (Symbol, Ustr)> + 'a {
        self.graph.edges(self.file2node[&a]).filter_map(|e| {
            match (e.weight(), &self.graph[e.target()]) {
                (FSEdge::Import(sym), FSNode::File(name)) => Some((*sym, *name)),
                _ => None,
            }
        })
    }
    //all subfiles from origin under path
    pub fn sub_files<'a>(
        &'a self,
        origin: Ustr,
        path: &[Ustr],
    ) -> impl Iterator<Item = (compact_str::CompactString, Ustr, FSNode)> + 'a {
        let mut dir = self
            .graph
            .neighbors_directed(self.file2node[&origin], Incoming)
            .find(|n| matches!(self.graph[*n], FSNode::Dir))
            .unwrap();
        let mut ok = true;
        for i in path.iter() {
            if let Some(e) = self.graph.edges(dir).find(|e| match e.weight() {
                FSEdge::Path(name) => name == i && self.graph[e.target()].is_dir(),
                _ => false,
            }) {
                dir = e.target();
            } else {
                ok = false;
            }
        }
        let mut stack: Vec<(compact_str::CompactString, _, _)> = Vec::new();
        if ok {
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
    pub fn resolve(&mut self, src: RootSymbol) -> Option<RootSymbol> {
        self.resolved.get(&src).cloned()
    }
    pub fn used_by<'a>(&'a self, dst: RootSymbol) -> impl Iterator<Item = RootSymbol> + 'a {
        self.reverse
            .get(&dst)
            .into_iter()
            .flat_map(|i| i.iter().cloned())
    }
}

#[derive(Debug, Clone)]
pub struct RootGraph {
    pub files: im::HashMap<Ustr, Document>,
    pub fs: Arc<FileSystem>,
    pub ref_map: ReferenceMap,
}
impl RootGraph {
    //find all symbols from origin under path
    pub fn resolve<'a>(
        &'a self,
        origin: Ustr,
        path: &'a [Ustr],
    ) -> impl Iterator<Item = RootSymbol> + 'a {
        let mut stack = vec![(origin, path)];
        std::iter::from_fn(move || {
            stack.pop().and_then(|(file, tail)| {
                for (sym, tgt) in self.fs.imports(file) {
                    let common_prefix = self.files[&file]
                        .import_prefix(sym)
                        .iter()
                        .zip(tail.iter())
                        .take_while(|(i, k)| i == k)
                        .count();

                    if common_prefix == self.files[&file].import_prefix(sym).len() {
                        stack.push((tgt, &tail[common_prefix..]));
                    }
                }
                Some(
                    self.files[&file]
                        .lookup(Symbol::Root, tail, |_| true)
                        .map(move |sym| RootSymbol { file, sym }),
                )
            })
        })
        .flatten()
    }
    pub fn resolve_with_binding<'a>(
        &'a self,
        origin: Ustr,
        path: &'a [Ustr],
    ) -> impl Iterator<Item = Vec<(RootSymbol,usize)>> + 'a {
        let mut stack = vec![(origin, path, vec![])];
        std::iter::from_fn(move || {
            stack.pop().and_then(|(file, tail, binding)| {
                let src_file = &self.files[&file];
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
                                .map(move |(sym,len)|{
                                    offset +=len;
                                    (sym,offset)
                                })
                                .collect()
                        }),
                )
            })
        })
        .flatten()
    }

    pub fn resolve_attributes<'a, F: FnMut(RootSymbol, &[Ustr])>(
        &'a self,
        origin: Ustr,
        context: &'a [Ustr],
        mut f: F,
    ) {
        for root in self.resolve(origin, context) {
            let file = &self.files[&root.file];
            info!("resolved {:?}", root);
            file.visit_named_children(root.sym, false, |i, prefix| match i {
                Symbol::Feature(..) => true,
                Symbol::Attribute(..) => {
                    info!("attrib {:?}", prefix);
                    f(
                        RootSymbol {
                            sym: i,
                            file: root.file,
                        },
                        &prefix[1..],
                    );
                    true
                }
                _ => false,
            });
        }
    }
    pub fn new(files: im::HashMap<Ustr, Document>) -> Self {
        Self {
            fs: Arc::new(FileSystem::new(&files)),
            files,
            ref_map: Default::default(),
        }
    }
    pub fn dump(&self) {
        info!("{:#?}", &self.files);
    }
}
//Central synchronisation provider
pub struct Context {
    pub root: RwLock<RootGraph>,
    pub revison_counter: AtomicU64,
    pub revison_counter_parsed: AtomicU64,
    pub dirty: Notify,
    pub shutdown: CancellationToken,
    pub documents: Mutex<DocumentStore>,
    pub client: Client,
    pub load_files_sema: Semaphore,
}
impl Context {
    //Make sure uri is inside the snapshot
    pub async fn snapshot(&self, uri: &Url) -> RootGraph {
        let time = Instant::now();
        loop {
            let snap = self.root.read().clone();
            if snap.files.contains_key(&uri.as_str().into()) {
                info!("waited {:?} for root", time.elapsed());
                return snap;
            }
            tokio::time::sleep(tokio::time::Duration::from_millis(1)).await;
        }
    }
    pub async fn snapshot_version(&self, uri: &Url, min_version: Instant) -> RootGraph {
        let time = Instant::now();
        loop {
            let snap = self.root.read().clone();
            if snap
                .files
                .get(&uri.as_str().into())
                .map(|file| file.timestamp >= min_version)
                .unwrap_or(false)
            {
                info!("waited {:?} for root", time.elapsed());
                return snap;
            }
            tokio::time::sleep(tokio::time::Duration::from_millis(1)).await;
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
async fn update_root_graph(
    ctx: &Context,
    _local_revision: u64,
    check_state: &mut HashMap<Ustr, Instant>,
) {
    let timer = Instant::now();
    let mut root = RootGraph::new(ctx.documents.lock().ast.clone());
    let mut ref_map = ReferenceMap::default();
    let publish = ctx.ready();
    {
        let mut file_paths = HashSet::new();
        for (_, file) in root.files.iter() {
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
            } else if check_state
                .get(&file.name)
                .map(|old| old < &file.timestamp)
                .unwrap_or(true)
                && file.errors.len() > 0
            {
                check_state.insert(file.name, file.timestamp);
                if publish {
                    check::publish(&ctx.client, &file.uri, &file.errors).await;
                }
            } else if file.errors.len() == 0 {
                let timer = Instant::now();
                let err = check::check_references(&root, file.name, &mut ref_map);
                check::publish(&ctx.client, &file.uri, &err).await;
                info!("checked refs {:?}", timer.elapsed());
            }
        }
    }
    info!("updated root graph {:?}", timer.elapsed());
    root.ref_map = ref_map;
    *ctx.root.write() = root;
}

async fn handler_impl(ctx: Arc<Context>) {
    let mut local_revision = 0;
    let mut check_state = HashMap::new();
    loop {
        select! {
            _ = ctx.shutdown.cancelled() => return,
            _ = ctx.dirty.notified() =>{
                update_root_graph(&ctx,local_revision,&mut check_state).await
            }
        }
    }
}

pub fn create_handler(
    client: Client,
    shutdown: CancellationToken,
    _: Arc<DashMap<Url, AsyncDraft>>,
) -> Arc<Context> {
    let ctx = Arc::new(Context {
        load_files_sema: Semaphore::new((num_cpus::get() - 1).max(1)),
        shutdown,
        dirty: Notify::new(),
        client,
        revison_counter: AtomicU64::new(0),
        revison_counter_parsed: AtomicU64::new(0),
        documents: Mutex::new(DocumentStore::default()),
        root: RwLock::new(RootGraph {
            ref_map: ReferenceMap::default(),
            fs: Arc::new(FileSystem {
                graph: Default::default(),
                file2node: HashMap::new(),
            }),
            files: Default::default(),
        }),
    });
    spawn(handler_impl(ctx.clone()));
    ctx
}
