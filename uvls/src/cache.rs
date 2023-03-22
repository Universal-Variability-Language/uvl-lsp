use crate::ast::*;
use crate::check::ErrorsAcc;
use crate::config::ConfigDocument;
use crate::config::ConfigValue;
use crate::resolve::*;
use crate::semantic::*;
use indexmap::IndexMap;

use compact_str::CompactStringExt;
use hashbrown::{HashMap, HashSet};
use log::info;
use petgraph::prelude::*;
use petgraph::unionfind::UnionFind;
use std::sync::Arc;
use tokio::time::Instant;
use ustr::Ustr;
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
#[derive(Debug, Clone, Default)]
pub struct FileSystem {
    graph: DiGraph<FSNode, FSEdge>,
    file2node: HashMap<FileID, NodeIndex>,
}
impl FileSystem {
    fn goto_dir(
        graph: &DiGraph<FSNode, FSEdge>,
        mut root: NodeIndex,
        path: &[Ustr],
    ) -> Option<NodeIndex> {
        if !graph[root].is_dir() {
            root = graph
                .neighbors_directed(root, Incoming)
                .find(|n| matches!(graph[*n], FSNode::Dir))
                .unwrap();
        }

        let mut ok = true;
        for (_, i) in path.iter().enumerate() {
            if let Some(e) = graph.edges(root).find(|e| match e.weight() {
                FSEdge::Path(name) => name == i && graph[e.target()].is_dir(),
                _ => false,
            }) {
                root = e.target();
            } else {
                ok = false;
                break;
            }
        }
        if ok {
            Some(root)
        } else {
            None
        }
    }
    fn goto_file(
        graph: &DiGraph<FSNode, FSEdge>,
        root: NodeIndex,
        path: &[Ustr],
    ) -> Option<NodeIndex> {
        Self::goto_dir(graph, root, &path[0..path.len() - 1]).and_then(|dir| {
            graph.edges(dir).find_map(|e| match e.weight() {
                FSEdge::Path(name)
                    if name == &path[path.len() - 1] && !graph[e.target()].is_dir() =>
                {
                    Some(e.target())
                }
                _ => None,
            })
        })
    }
    fn new(files: &AstFiles, errors: &mut ErrorsAcc) -> Self {
        let mut graph = DiGraph::new();
        let mut file2node = HashMap::new();
        let root = graph.add_node(FSNode::Dir);
        //create file system
        for (&n, f) in files.iter() {
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
        for (&n, f) in files.iter() {
            for i in f.all_imports() {
                if let Some(node) = Self::goto_file(&graph, file2node[&n], f.path(i)) {
                    graph.add_edge(file2node[&n], node, FSEdge::Import(i));
                } else {
                    errors.sym(i, n, 50, "unresolved import");
                    info!("Cant find {:?} ", f.path(i));
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
    pub fn recursive_imports(&self, src: FileID) -> Vec<FileID> {
        let mut out = HashSet::new();
        out.insert(src);
        let mut stack = vec![src];
        while let Some(src) = stack.pop() {
            for (_, tgt) in self.imports(src) {
                stack.push(tgt);
                out.insert(tgt);
            }
        }
        out.drain().collect()
    }

    pub fn recursive_imported(&self, src: FileID) -> Vec<FileID> {
        let mut out = HashSet::new();
        out.insert(src);
        let mut stack = vec![src];
        while let Some(src) = stack.pop() {
            for (_, tgt) in self.imported(src) {
                stack.push(tgt);
                out.insert(tgt);
            }
        }
        out.drain().collect()
    }
    pub fn resolve_abs(&self, path: &[Ustr]) -> Option<FileID> {
        Self::goto_file(&self.graph, NodeIndex::new(0), path).and_then(|f| match &self.graph[f] {
            FSNode::File(id) => Some(*id),
            _ => None,
        })
    }
    pub fn resolve_abs_dir(&self, path: &[Ustr]) -> Option<NodeIndex> {
        Self::goto_dir(&self.graph, NodeIndex::new(0), path)
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
    //find a file under path from origin
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
                return None;
            }
        }
        Self::goto_file(&self.graph, self.file2node[&origin], path).and_then(|node| {
            match &self.graph[node] {
                FSNode::File(id) => Some(*id),
                _ => None,
            }
        })
    }
    pub fn dir_files<'a>(
        &'a self,
        mut dir: NodeIndex,
        path: &[Ustr],
    ) -> impl Iterator<Item = (compact_str::CompactString, Ustr, FSNode)> + 'a {
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
    }
    pub fn dir_of(&self, file: FileID) -> NodeIndex {
        self.graph
            .neighbors_directed(self.file2node[&file], Incoming)
            .find(|n| matches!(self.graph[*n], FSNode::Dir))
            .unwrap()
    }
    //all subfiles from origin under path, returns (prefix,filename,filenode)
    pub fn sub_files<'a>(
        &'a self,
        origin: FileID,
        path: &[Ustr],
    ) -> impl Iterator<Item = (compact_str::CompactString, Ustr, FSNode)> + 'a {
        let dir = self.dir_of(origin);
        self.dir_files(dir, path)
            .filter(move |(_, _, node)| match node {
                FSNode::File(tgt) => tgt != &origin,
                _ => true,
            })
    }
}


#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModelErrorState {
    SyntaxError,
    LinkError,
    Valid,
}
//When to files are related through imports they form a module
//Modules are linked and cached
#[derive(Debug, Clone)]
pub struct ModuleState {
    pub members: Vec<FileID>,
    pub state: ModelErrorState,
}

#[derive(Debug, Clone)]
pub struct LinkedModule {
    pub ok: bool,
    pub revision: u64,
    pub ref_map: HashMap<RootSymbol, RootSymbol>,
}
//each config file forms a special module with preset values for attributes and features
//also cached between iterations
#[derive(Clone, Debug)]
pub struct ConfigModule {
    pub revision: u64,
    pub ok: bool,
    pub members: HashSet<FileID>,
    pub source_map: HashMap<RootSymbol, Span>,
    pub attributes: HashMap<RootSymbol, ConfigValue>,
    pub features: HashMap<RootSymbol, ConfigValue>,
    pub doc: Arc<ConfigDocument>,
}
fn find_modules(files: &AstFiles, fs: &FileSystem) -> impl Iterator<Item = Vec<FileID>> {
    let file_names: Vec<FileID> = files.keys().cloned().collect();
    let file_index: HashMap<FileID, usize> = file_names
        .iter()
        .enumerate()
        .map(|(i, f)| (*f, i))
        .collect();
    let mut union_find = UnionFind::new(files.len());
    for e in fs
        .graph
        .edge_references()
        .filter(|e| matches!(e.weight(), FSEdge::Import(..)))
    {
        let (a, b) = (e.source(), e.target());
        // union the two vertices of the edge
        if let (FSNode::File(a), FSNode::File(b)) = (&fs.graph[a], &fs.graph[b]) {
            union_find.union(file_index[a], file_index[b]);
        }
    }
    let mut map = HashMap::new();
    for i in 0..files.len() {
        let rep = union_find.find(i);
        insert_multi(&mut map, rep, i);
    }
    map.into_values()
        .map(move |i| i.iter().map(|j| file_names[*j]).collect::<Vec<_>>())
}
fn config_members(
    fs: &FileSystem,
    doc: &ConfigDocument,
    errors: &mut ErrorsAcc,
) -> (HashSet<FileID>, HashMap<usize, FileID>) {
    let mut members = HashSet::new();
    let mut resolved = HashMap::new();
    for (i, c) in doc.files.iter().enumerate() {
        let path = [&doc.path[0..doc.path.len() - 1], &c.file.names].concat();
        if let Some(tgt) = fs.resolve_abs(&path) {
            resolved.insert(i, tgt);
            if members.insert(tgt) {
                for i in fs.recursive_imports(tgt) {
                    members.insert(i);
                }
            }
        } else {
            errors.span(c.file.range(), doc.id, 50, "unresolved file");
        }
    }
    (members, resolved)
}

fn link_config(
    files: &AstFiles,
    doc: &ConfigDocument,
    resolved: HashMap<usize, FileID>,
    fs: &FileSystem,
    err: &mut ErrorsAcc,
) -> (
    HashMap<RootSymbol, ConfigValue>,
    HashMap<RootSymbol, ConfigValue>,
    HashMap<RootSymbol, Span>,
) {
    let mut attributes = HashMap::new();
    let mut features = HashMap::new();
    let mut source_map = HashMap::new();
    for (file_id, conf) in doc
        .files
        .iter()
        .enumerate()
        .flat_map(|(i, c)| resolved.get(&i).into_iter().map(move |k| (*k, c)))
    {
        for (path, val) in conf.config.iter() {
            let mut state = ResolveState::Unresolved;
            for sym in resolve(files, fs, file_id, &path.names) {
                let dst_file = &files[&sym.file];
                if dst_file.type_of(sym.sym).unwrap() == val.ty() {
                    state = ResolveState::Resolved(sym)
                } else {
                    state = ResolveState::WrongType {
                        expected: val.ty(),
                        found: dst_file.type_of(sym.sym).unwrap(),
                    }
                }
            }

            match state {
                ResolveState::Resolved(sym) => {
                    source_map.insert(sym, path.range());
                    match sym.sym {
                        Symbol::Feature(..) => features.insert(sym, val.clone()),

                        Symbol::Attribute(..) => attributes.insert(sym, val.clone()),
                        _ => unimplemented!(),
                    };
                }
                ResolveState::WrongType { expected, found } => {
                    err.span(
                        path.range(),
                        doc.id,
                        40,
                        format!("expected {:?} only found {:?}", expected, found),
                    );
                }
                ResolveState::Unresolved => {
                    err.span(path.range(), doc.id, 40, "unresolved reference");
                }
            }
        }
    }
    (features, attributes, source_map)
}

#[derive(Clone, Debug, Default)]
pub struct Cache {
    pub fs: FileSystem,
    pub files: AstFiles,
    pub configs: ConfigFiles,
    pub modules: IndexMap<Vec<FileID>, Arc<LinkedModule>>,
    pub config_modules: HashMap<FileID, Arc<ConfigModule>>,
    pub file2module: HashMap<FileID, usize>,
}
impl Cache {
    pub fn new(
        old: &Cache,
        files: &AstFiles,
        configs: &ConfigFiles,
        dirty: &HashSet<FileID>,
        revision: u64,
        errors: &mut ErrorsAcc,
    ) -> Cache {
        let fs = FileSystem::new(&files, errors);
        info!("updating cache dirty {:?}", dirty);
        let time = Instant::now();
        let mut file2module = HashMap::new();
        //build modules
        let modules: IndexMap<Vec<FileID>, Arc<LinkedModule>> = find_modules(&files, &fs)
            .map(|members| {
                let dirty = members.iter().any(|f| dirty.contains(f));
                if !dirty {
                    if let Some(old) = old.modules.get(&members).cloned() {
                        return (members, old);
                    }
                }
                let ref_map = resolve_files(&members, &fs, errors);
                let ok = !members.iter().any(|f| errors.has_error(*f));
                (
                    members,
                    Arc::new(LinkedModule {
                        ok,
                        revision,
                        ref_map,
                    }),
                )
            })
            .enumerate()
            .map(|(l, (k, v))| {
                for i in k.iter() {
                    file2module.insert(*i, l);
                }
                (k, v)
            })
            .collect();
        //build cached modules
        let config_modules = configs
            .values()
            .map(|doc| {
                let (members, resolved) = config_members(&fs, doc, errors);

                info!("{:?} members: {:?}", doc.id, members);
                let dirty = members.iter().any(|f| dirty.contains(f)) || dirty.contains(&doc.id);
                info!("{:?} dirty: {dirty}", doc.id);
                if !dirty {
                    if let Some(old) = old.config_modules.get(&doc.id) {
                        if old.members == members {
                            return (doc.id, old.clone());
                        }
                    }
                }
                let (features, attribs, source_map) =
                    link_config(&files, doc, resolved, &fs, errors);
                let ok = !members.iter().any(|f| errors.has_error(*f)) && !errors.has_error(doc.id);
                info!("{:?} ok: {ok}", doc.id);
                (
                    doc.id,
                    Arc::new(ConfigModule {
                        members,
                        ok,
                        doc: doc.clone(),
                        revision,
                        features,
                        attributes: attribs,
                        source_map,
                    }),
                )
            })
            .collect();
        info!("Updated cache in {:?}", time.elapsed());
        Cache {
            files: files.clone(),
            file2module,
            config_modules,
            modules,
            configs: configs.clone(),
            fs,
        }
    }
}
