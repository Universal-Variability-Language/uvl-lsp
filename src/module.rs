use crate::semantic::{FileGraphs, RootGraph, RootSymbolID, SymbolID};
use log::info;
use petgraph::graph::{DiGraph, NodeIndex};
use petgraph::visit::*;
use std::path::PathBuf;
use std::{
    borrow::Borrow,
    collections::HashMap,
    ops::{Index, IndexMut},
};
use std::{collections::HashSet, fmt::Display};
use tokio::sync::mpsc;
use tower_lsp::lsp_types::Url;
use ustr::Ustr;
#[derive(PartialEq, Eq, Debug, Clone, Copy)]

pub enum Content {
    Namespace,
    Dir,
    File(Ustr),
    FileRoot(Ustr),
}
impl Content {
    pub fn is_file(&self, file: Ustr) -> bool {
        match self {
            Content::File(f) => *f == file,

            _ => false,
        }
    }
}
impl Display for Content {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Namespace => f.write_str("namespace"),
            Self::Dir => f.write_str("dir"),
            Self::File(_) => f.write_str("file"),
            Self::FileRoot(file) => f.write_str(file.as_str()),
        }
    }
}
#[derive(Debug)]
pub struct ModuleGraph {
    content: HashMap<Ustr, NodeIndex>,
    graph: petgraph::graph::DiGraph<Content, Ustr>,
}

impl ModuleGraph {
    fn trace_file(&mut self, mut tail: &[Ustr], file_name: Ustr) -> (NodeIndex, NodeIndex) {
        let mut node = NodeIndex::new(0);
        loop {
            let mut ok = false;
            for next in self.get(node, tail[0]) {
                if tail.len() == 1 && matches!(self[next], Content::File(_)) {
                    return (node, next);
                } else {
                    node = next;
                    tail = &tail[1..];
                    ok = true;
                    break;
                }
            }
            if !ok {
                break;
            }
        }

        while tail.len() > 1 {
            let next = self.add(Content::Dir);
            self.add_edge(node, next, tail[0]);
            tail = &tail[1..];
            node = next;
        }
        let file = self.add(Content::File(file_name));

        self.add_edge(node, file, tail[0]);
        (node, file)
    }
    fn trace_namespace(&mut self, mut node: NodeIndex, mut tail: &[Ustr]) -> NodeIndex {
        for _ in 0..tail.len() {
            let next = self.add(Content::Namespace);
            self.add_edge(node, next, tail[0]);
            tail = &tail[1..];
            node = next;
        }
        node
    }
    fn add(&mut self, content: Content) -> NodeIndex {
        self.graph.add_node(content)
    }
    pub fn node_from_file(&self, file: Ustr) -> NodeIndex {
        self.content[&file]
    }
    pub fn new(files: &FileGraphs) -> Self {
        let mut graph = Self {
            graph: DiGraph::new(),
            content: HashMap::new(),
        };
        graph.add(Content::Dir);
        info!("creating a new module graph");
        let mut file2node = HashMap::new();
        for (_, file) in files.iter() {
            let (dir, file_node) = graph.trace_file(&file.path, file.name);
            file2node.insert(file.name, file_node);
            let inner_namespace = graph.trace_namespace(file_node, &file.namespace());
            let content = graph.add(Content::FileRoot(file.name));
            graph.content.insert(file.name, content);
            graph.add_edge(inner_namespace, content, "".into());
            graph.add_edge(content, dir, "#".into());
        }
        for (_, src) in files.iter() {
            for i in src.store.imports.iter() {
                if let Some(imorted_name) =
                    graph.resolve(src.name, &i.path.names, files, |sym| match sym {
                        RootSymbolID::Module(id) => {
                            info!("found import {:?}", &graph[id]);
                            match &graph[id] {
                                Content::File(name) => return Some(name),
                                _ => {}
                            }
                            None
                        }
                        _ => None,
                    })
                {
                    let dst = &files[&imorted_name];
                    if src.name == dst.name {
                        info!("Loop import detected");
                        continue;
                    }
                    if let Some(alias) = i.alias.as_ref() {
                        let src = graph.content[&src.name];
                        let dst = graph.content[&dst.name];
                        graph.add_edge(src, dst, alias.name);
                    } else {
                        let src_namespace = src.namespace();
                        let dst_namespace = dst.namespace();
                        match (src_namespace.len(), dst_namespace.len()) {
                            (.., 0) | (0, ..) => {
                                let src_id = graph.content[&src.name];
                                let dst_id = file2node[&dst.name];
                                graph.add_edge(src_id, dst_id, "".into());
                            }
                            (_, _) => {
                                let src_id = graph.content[&src.name];
                                let mut dst_id = file2node[&dst.name];
                                let shared_prefix = src_namespace
                                    .iter()
                                    .zip(dst_namespace.iter())
                                    .take_while(|(i, k)| i == k)
                                    .count();
                                for i in 0..shared_prefix {
                                    dst_id = graph.get(dst_id, dst_namespace[i]).next().unwrap();
                                }
                                graph.add_edge(src_id, dst_id, "".into());
                            }
                        }
                    }
                } else {
                    info!("cant resolve {:?} in {}", &i.path.names, &src.name);
                }
            }
        }
        graph
    }
    pub fn edges<'a>(
        &'a self,
        node: NodeIndex,
        exclude_file: Option<Ustr>,
        origin: Option<NodeIndex>,
    ) -> impl Iterator<Item = (Ustr, NodeIndex)> + 'a {
        self.graph
            .edges(node)
            .map(|e| (*e.weight(), e.target()))
            .filter(move |(name, _)| {
                origin.as_ref().map(|&o| o == node).unwrap_or(false) || name.as_str() != "#"
            })
            .filter(move |(_, v)| {
                exclude_file
                    .map(|name| !self[*v].is_file(name))
                    .unwrap_or(true)
            })
    }
    pub fn len(&self) -> usize {
        self.graph.node_count()
    }
    fn add_edge(&mut self, a: NodeIndex, b: NodeIndex, e: Ustr) {
        self.graph.add_edge(a, b, e);
    }
    pub fn edge_connecting(&self, a: NodeIndex, b: NodeIndex) -> Ustr {
        *self.graph.edges_connecting(a, b).next().unwrap().weight()
    }
    pub fn resolve<K, F: FnMut(RootSymbolID) -> Option<K>>(
        &self,
        origin_file: Ustr,
        path: &[Ustr],
        files: &FileGraphs,
        mut f: F,
    ) -> Option<K> {
        let origin = self.node_from_file(origin_file);
        let mut stack = vec![(origin, path)];
        let mut visited = HashSet::new();

        while let Some((node, tail)) = stack.pop() {
            if !visited.insert((node, tail.len())) {
                continue;
            }
            if self[node].is_file(origin_file) {
                continue;
            }
            if tail.len() == 0 {
                if let Some(k) = f(RootSymbolID::Module(node)) {
                    return Some(k);
                } else {
                    continue;
                }
            }
            match &self[node] {
                Content::FileRoot(file) => {
                    let file = &files[file];
                    for i in file.store.index.get(tail) {
                        if let Some(k) = f(RootSymbolID::Symbol(file.name, *i)) {
                            return Some(k);
                        }
                    }
                }
                _ => {}
            }
            for i in self.get(node, tail[0]) {
                stack.push((i, &tail[1..]));
            }
            for i in self.get(node, "".into()) {
                stack.push((i, &tail[..]));
            }
            if node == origin {
                for i in self.get(node, "#".into()) {
                    stack.push((i, &tail[..]));
                }
            }
        }
        None
    }
    pub fn get<'a>(&'a self, src: NodeIndex, name: Ustr) -> impl Iterator<Item = NodeIndex> + 'a {
        self.graph.edges(src).filter_map(move |e| {
            if e.weight() == &name {
                Some(e.target())
            } else {
                None
            }
        })
    }

    pub fn dump(&self) {
        use petgraph_graphml::GraphMl;
        let graphml = GraphMl::new(&self.graph)
            .pretty_print(true)
            .export_edge_weights_display()
            .export_node_weights_display();
        use std::fs::File;
        use std::io::Write;
        let mut file = File::create("/home/carad/graph123.graphml").unwrap();
        file.write_all(graphml.to_string().as_bytes()).unwrap();
    }
}
impl Default for ModuleGraph {
    fn default() -> Self {
        let mut g = DiGraph::new();
        g.add_node(Content::Dir);
        Self {
            graph: g,
            content: HashMap::new(),
        }
    }
}

impl Index<NodeIndex> for ModuleGraph {
    type Output = Content;
    fn index(&self, index: NodeIndex) -> &Self::Output {
        &self.graph[index]
    }
}

impl IndexMut<NodeIndex> for ModuleGraph {
    fn index_mut(&mut self, index: NodeIndex) -> &mut Self::Output {
        &mut self.graph[index]
    }
}
