use crate::document::AsyncDraft;
use crate::check;
use compact_str::CompactStringExt;
use parking_lot::RwLock;

use dashmap::DashMap;

use log::info;

use crate::filegraph::*;
use petgraph::prelude::*;
use rayon::prelude::*;
use ropey::Rope;
use std::collections::HashMap;
use std::fmt::Debug;
use std::sync::atomic::AtomicU64;
use std::sync::Arc;
use tokio::sync::mpsc;
use tokio::time::{Duration, Instant};
use tokio::{select, spawn};
use tokio_util::sync::CancellationToken;
use tower_lsp::lsp_types::*;
use tower_lsp::Client;
use tree_sitter::Tree;
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

#[derive(Debug, Clone)]
pub struct FileSystem {
    graph: Graph<FSNode, FSEdge>,
    file2node: HashMap<Ustr, NodeIndex>,
}
impl FileSystem {
    fn new(files: &im::HashMap<Ustr, FileGraph>) -> Self {
        let mut graph = Graph::new();
        let mut file2node = HashMap::new();
        let root = graph.add_node(FSNode::Dir);
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

        for (n, f) in files.iter() {
            for i in f.imports() {
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
    pub fn imports_connecting<'a>(&'a self, a: Ustr, b: Ustr) -> impl Iterator<Item = Symbol> + 'a {
        self.graph
            .edges_connecting(self.file2node[&a], self.file2node[&b])
            .filter_map(|e| match e.weight() {
                FSEdge::Import(sym) => Some(*sym),
                _ => None,
            })
    }
    pub fn imports<'a>(&'a self, a: Ustr) -> impl Iterator<Item = (Symbol, Ustr)> + 'a {
        self.graph.edges(self.file2node[&a]).filter_map(|e| {
            match (e.weight(), &self.graph[e.target()]) {
                (FSEdge::Import(sym), FSNode::File(name)) => Some((*sym, *name)),
                _ => None,
            }
        })
    }
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
    }
}

#[derive(Debug, Clone)]
pub struct RootGraph {
    pub files: im::HashMap<Ustr, FileGraph>,
    pub fs: Arc<FileSystem>,
}
impl RootGraph {
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
                        .prefix(sym)
                        .iter()
                        .zip(tail.iter())
                        .take_while(|(i, k)| i == k)
                        .count();

                    if common_prefix == self.files[&file].prefix(sym).len() {
                        stack.push((tgt, &tail[common_prefix..]));
                    }
                }
                Some(
                    self.files[&file]
                        .lookup(tail)
                        .map(move |sym| RootSymbol { file, sym }),
                )
            })
        })
        .flatten()
    }
    pub fn new(files: im::HashMap<Ustr, FileGraph>) -> Self {
        Self {
            fs: Arc::new(FileSystem::new(&files)),

            files,
        }
    }
    pub fn dump(&self) {
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
    //Make sure uri is inside the snapshot
    pub async fn snapshot(&self, uri: &Url) -> RootGraph {
        loop {
            let snap = self.root.read().clone();
            if snap.files.contains_key(&uri.as_str().into()) {
                return snap;
            }
            tokio::time::sleep(tokio::time::Duration::from_millis(1)).await;
        }
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
    async fn update(&mut self, change: DraftUpdate, ctx: &Arc<Context>) {
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
            self.files.insert(i.name, i);
        }
        *ctx.root.write() = RootGraph::new(self.files.clone());
        let mut new_check_state: Vec<check::DocumentState> = dirty
            .par_iter()
            .map(|fname| check::check_document(&self.files[fname]))
            .collect();

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
            update_timestamp,
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
    _: Arc<DashMap<Url, AsyncDraft>>,
) -> Arc<Context> {
    let (tx, rx) = mpsc::channel(1024);
    let ctx = Arc::new(Context {
        shutdown,
        tx_draft_updates: tx,
        client,
        revison_counter: AtomicU64::new(0),
        root: RwLock::new(RootGraph {
            fs: Arc::new(FileSystem {
                graph: Default::default(),
                file2node: HashMap::new(),
            }),
            files: Default::default(),
        }),
    });
    spawn(handler_impl(ctx.clone(), rx));
    ctx
}
