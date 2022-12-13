use halfbrown::HashMap;
use std::{cell::RefCell, fmt::Debug, hash::Hash, ops::Index, ops::IndexMut};

use ustr::Ustr;
#[derive(Clone, Debug)]
struct SymbolNode<V> {
    path: Vec<Ustr>,
    value: V,
}
impl<V> PartialEq for SymbolNode<V> {
    fn eq(&self, other: &Self) -> bool {
        other.path == self.path
    }
}
impl<V> Eq for SymbolNode<V> {}
impl<V> Ord for SymbolNode<V> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.path.cmp(&other.path)
    }
}
impl<V> PartialOrd for SymbolNode<V> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.path.cmp(&other.path))
    }
}

#[derive(Clone, Debug)]
pub struct SymbolTable<V> {
    table: Vec<SymbolNode<V>>,
}
impl<V> Default for SymbolTable<V> {
    fn default() -> Self {
        SymbolTable { table: Vec::new() }
    }
}
impl<V> SymbolTable<V> {
    pub fn get<'a>(&'a self, path: &'a [Ustr]) -> impl Iterator<Item = &'a V> {
        let offset = self.table.partition_point(|x| x.path.as_slice() < path);
        self.table[offset..]
            .iter()
            .take_while(move |node| node.path == path)
            .map(|node| &node.value)
    }
    pub fn insert_unsorted(&mut self, path: Vec<Ustr>, value: V) {
        self.table.push(SymbolNode { path, value });
    }
    pub fn iter<'a>(&'a self) -> impl Iterator<Item = &'a V> {
        self.table.iter().map(|s| &s.value)
    }
    pub fn sort(&mut self) {
        self.table.sort();
    }
    pub fn insert(&mut self, path: Vec<Ustr>, value: V) {
        let node = SymbolNode { path, value };
        match self.table.binary_search(&node) {
            Err(pos) | Ok(pos) => self.table.insert(pos, node),
        }
    }
    pub fn delete<F: Fn(&V) -> bool>(&mut self, path: &[Ustr], fun: F) {
        let mut offset = self.table.partition_point(|x| x.path.as_slice() < path);
        let mut kill_list = Vec::new();
        for i in self.table[offset..]
            .iter()
            .take_while(move |node| node.path == path)
        {
            if fun(&i.value) {
                kill_list.push(offset)
            }
            offset += 1;
        }
        for i in kill_list.iter().rev() {
            self.table.remove(*i);
        }
    }
    pub fn prefix<'a>(&'a self, prefix: &'a [Ustr]) -> impl Iterator<Item = &'a V> {
        let offset = self.table.partition_point(|x| x.path.as_slice() <= prefix);
        self.table[offset..]
            .iter()
            .take_while(move |node| starts_with(node.path.as_slice(), prefix))
            .map(|node| &node.value)
    }
    pub fn new() -> Self {
        Self { table: Vec::new() }
    }
    //fn prefix(&self, path: &[Ustr]) -> impl Iterator<Item = V> {}
}
pub fn starts_with<T: PartialEq>(path: &[T], prefix: &[T]) -> bool {
    if path.len() < prefix.len() {
        false
    } else {
        path.iter().zip(prefix).all(|(i, k)| i == k)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn symtable() {
        let s1 = Ustr::from("s1");
        let s2 = Ustr::from("s2");
        let s3 = Ustr::from("s3");
        let s4 = Ustr::from("s4");
        let s5 = Ustr::from("s5");
        let mut st = SymbolTable::new();
        st.insert(vec![s1, s2], 1);
        st.insert(vec![s1, s2], 3);
        st.insert(vec![s1, s3], 4);
        st.insert(vec![s1, s2, s3], 89);
        st.insert(vec![s4, s1, s2], 9);
        st.insert(vec![s5, s1, s2, s3, s1], 19);
        st.insert(vec![s5, s1, s2, s3, s1, s2], 10);
        st.insert(vec![s1, s1, s2, s3, s1, s2], 42);
        st.insert(vec![s2, s3, s1, s2], 12);
        st.insert(vec![s2, s1], 324);
        st.insert(vec![s4, s1], 34);
        for i in st.get(&[s1, s2]) {
            println!("{}", i);
        }
        for i in st.get(&[s4, s1]) {
            println!("{}", i);
        }
        for i in st.prefix(&[s1, s2]) {
            println!("prefix {}", i);
        }

        for i in st.prefix(&[s1, s1]) {
            println!("prefix {}", i);
        }

        for i in st.prefix(&[s1]) {
            println!("prefix s1 {}", i);
        }
        st.delete(&[s1], |_| true);
        st.delete(&[s1, s2], |_| true);
        println!("{:#?}", st);
    }
}
/*
//A datastructure to model a performant DFA Graph, this is used tp represent feature graphs with fast lookup.
//It supports O(k) path resolution where k is the path length(ignoring no determistic cases as) as
//they are rare in correct UVL. TODO optimize for singular values
#[derive(Clone, Debug)]
struct SymNode<V, E>
where
    V: Debug + Clone,
    E: Debug,
{
    content: V,
    edges: HashMap<E, Vec<NodeIndex>>,
}
#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct NodeIndex(pub usize);
#[derive(Clone, Debug)]
pub struct IndexGraph<V, E>
where
    V: Debug + Clone,
    E: Debug,
{
    nodes: Vec<SymNode<V, E>>,
    connections: HashMap<(NodeIndex, NodeIndex), E>,
}
pub fn insert_multi<K, V>(map: &mut HashMap<K, Vec<V>>, k: K, v: V)
where
    K: Hash + Eq,
{
    if let Some(old) = map.get_mut(&k) {
        old.push(v)
    } else {
        map.insert(k, vec![v]);
    }
}

impl<V, E> IndexGraph<V, E>
where
    E: Copy + Eq + Hash + Debug + Copy,
    V: Debug + Clone,
{
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            connections: HashMap::new(),
        }
    }
    pub fn add_node(&mut self, content: V) -> NodeIndex {
        self.nodes.push(SymNode {
            content,
            edges: HashMap::new(),
        });
        NodeIndex(self.nodes.len() - 1)
    }
    pub fn add_edge(&mut self, a: NodeIndex, b: NodeIndex, e: E) {
        insert_multi(&mut self.nodes[a.0].edges, e, b);
        self.connections.insert((a, b), e);
    }
    pub fn edge_between(&self, a: NodeIndex, b: NodeIndex) -> Option<E> {
        self.connections.get(&(a, b)).cloned()
    }
    pub fn edge_to<'a>(&'a self, a: NodeIndex, e: E) -> impl Iterator<Item = NodeIndex> + 'a {
        self.nodes[a.0]
            .edges
            .get(&e)
            .into_iter()
            .map(|i| i.iter())
            .flatten()
            .cloned()
    }
    pub fn edges<'a>(&'a self, a: NodeIndex) -> impl Iterator<Item = (NodeIndex, E, &'a V)> + 'a {
        self.nodes[a.0]
            .edges
            .iter()
            .map(|(k, v)| v.iter().map(|i| (*i, *k, &self[*i])))
            .flatten()
    }
    pub fn visit_children<'a, F: FnMut(NodeIndex, &[E], &V) -> bool + 'a>(
        &'a self,
        a: NodeIndex,
        mut filter: F,
    ) {
    }
}
impl<V, E> Index<NodeIndex> for IndexGraph<V, E>
where
    V: Debug + Clone,
    E: Debug,
{
    type Output = V;
    fn index(&self, index: NodeIndex) -> &Self::Output {
        &self.nodes[index.0].content
    }
}

impl<V, E> IndexMut<NodeIndex> for IndexGraph<V, E>
where
    V: Debug + Clone,
    E: Debug,
{
    fn index_mut(&mut self, index: NodeIndex) -> &mut Self::Output {
        &mut self.nodes[index.0].content
    }
}*/
