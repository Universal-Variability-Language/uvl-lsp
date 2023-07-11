use crate::core::*;
use check::ErrorsAcc;
use compact_str::CompactStringExt;
use hashbrown::{HashMap, HashSet};
use log::info;
use module::{ConfigModule, Module};
use petgraph::prelude::*;
use resolve::*;
use std::sync::Arc;
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
            for i in f.all_imports().rev() {
                if let Some(node) = Self::goto_file(&graph, file2node[&n], f.path(i)) {
                    if graph.contains_edge(node, file2node[&n]) {
                        errors.sym(i, n, 50, "cyclic import not allowed");
                    } else {
                        graph.add_edge(file2node[&n], node, FSEdge::Import(i));
                    }
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

#[derive(Debug, Clone)]
pub struct LinkedAstDocument {
    pub content: Arc<AstDocument>,
    pub resolved: HashMap<Symbol, RootSymbol>,
    pub revision: u64,
    pub ok: bool,
}
//A file that is not imported by any other is root file
fn find_root_files<'a>(fs: &FileSystem, files: &'a AstFiles) -> impl Iterator<Item = FileID> + 'a {
    let mut not_root = HashSet::new();
    for i in files.keys().cloned() {
        for (_, tgt) in fs.imports(i) {
            not_root.insert(tgt);
        }
    }
    files
        .keys()
        .filter(move |&i| !not_root.contains(i))
        .cloned()
}

#[derive(Clone, Debug, Default)]
pub struct Cache {
    pub fs: FileSystem,
    pub config_modules: HashMap<FileID, Arc<ConfigModule>>,
    pub ast: HashMap<FileID, Arc<LinkedAstDocument>>,
    pub modules: HashMap<FileID, Arc<Module>>,
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
        let mut trans_dirty = dirty.clone();
        let fs = FileSystem::new(files, errors);
        for i in dirty.iter() {
            if !i.is_config() {
                for k in fs.recursive_imported(*i) {
                    trans_dirty.insert(k);
                }
            }
        }
        for i in trans_dirty.iter() {
            if !errors.errors.contains_key(i) {
                errors.errors.insert(*i, Vec::new()); //Remove old errors when dependencies change
                                                      //but not the file
            }
        }
        let mut linked_ast: HashMap<_, _> = old
            .ast
            .iter()
            .filter(|(k, _)| files.contains_key(*k))
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();

        info!("updating cache dirty {:?}", trans_dirty);
        //Link ASTs
        for i in trans_dirty.iter() {
            if !i.is_config() {
                linked_ast.insert(
                    *i,
                    Arc::new(LinkedAstDocument {
                        content: files[i].clone(),
                        revision,
                        resolved: resolve_file(*i, &fs, errors),
                        ok: !errors.has_error(*i),
                    }),
                );
            }
        }
        //Create linked instances of root files
        let modules: HashMap<_, _> = find_root_files(&fs, files)
            .map(|root| {
                let imports = fs.recursive_imports(root);
                if imports.iter().any(|i| trans_dirty.contains(i))
                    || !old.modules.contains_key(&root)
                {
                    (root, Arc::new(Module::new(root, &fs, &linked_ast)))
                } else {
                    (root, old.modules[&root].clone())
                }
            })
            .collect();
        let mut config_modules = HashMap::new();
        //Create linked configuration for the json files in the project
        for (k, v) in configs.iter() {
            if let Some(content) = v.config.as_ref() {
                info!("uri {}", content.file.as_str());
                if files.contains_key(&content.file) {
                    let dirty = trans_dirty.contains(&content.file)
                        || dirty.contains(k)
                        || !old.config_modules.contains_key(k);
                    if dirty {
                        //recreate
                        let mut module = Module::new(content.file, &fs, &linked_ast);
                        if !module.ok {
                            config_modules.insert(
                                *k,
                                Arc::new(ConfigModule {
                                    module: Arc::new(module),
                                    values: Default::default(),
                                    source_map: Default::default(),
                                }),
                            );
                        } else {
                            let (values, source_map) = module
                                .resolve_config(&content.config, |span, err| {
                                    errors.span(span, *k, 20, err)
                                });
                            module.ok &= !errors.has_error(*k);
                            config_modules.insert(
                                *k,
                                Arc::new(ConfigModule {
                                    module: Arc::new(module),
                                    values,
                                    source_map,
                                }),
                            );
                        }
                    } else {
                        //reuse
                        config_modules.insert(*k, old.config_modules[k].clone());
                    }
                } else {
                    errors.span(content.file_span.clone(), *k, 100, "file no found");
                }
            }
        }

        Cache {
            fs,
            config_modules,
            ast: linked_ast,
            modules,
        }
    }
}
