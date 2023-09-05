use crate::core::*;
use check::ErrorInfo;
use hashbrown::HashMap;
use itertools::Itertools;
use ropey::Rope;
use semantic::FileID;
use std::hash::Hash;
use std::path::Component;
use tokio::time::Instant;
use tower_lsp::lsp_types::Url;
use tree_sitter::Tree;
use ustr::Ustr;
use util::lsp_range;
pub mod collapse;
mod def;
pub mod graph;
mod transform;
mod visitor;
pub use def::*;
pub use visitor::*;
//Easy to work with AST parsing and util.
//The AST is stored as an ECS like structure
//This allows fast queries over all features groups etc.
//Features, Attributes, Imports and Directories are stored in a typed radix tree.
//The radix tree is represented via a map (sym0,name,ty) -> sym1
//where ty is the type of sym1. Using this representation lowers total
//memory consumption by a nice 20%
pub fn uri_to_path(uri: &Url) -> Option<Vec<Ustr>> {
    let mut p = uri.to_file_path().ok()?;
    p.set_extension("");
    p.components()
        .filter_map(|c| match c {
            Component::Normal(os) => os.to_str().map(|s| Some(s.into())),
            _ => None,
        })
        .collect()
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

//1->N parent child relation
#[derive(Default, Debug, Clone)]
struct TreeMap {
    children: HashMap<Symbol, Vec<Symbol>>,
    parent: HashMap<Symbol, Symbol>,
}
impl TreeMap {
    fn insert(&mut self, parent: Symbol, child: Symbol) {
        insert_multi(&mut self.children, parent, child);
        self.parent.insert(child, parent);
    }
}
//Ast container each symbol kind lives in its own vector
#[derive(Clone, Debug, Default)]
struct Ast {
    keywords: Vec<Keyword>,
    namespace: Option<Path>,
    includes: Vec<LanguageLevelDecl>,
    import: Vec<Import>,
    features: Vec<Feature>,
    constraints: Vec<ConstraintDecl>,
    attributes: Vec<Attribute>,
    references: Vec<Reference>,
    groups: Vec<Group>,
    dirs: Vec<Dir>,
    structure: TreeMap,
    //The index is stored as a typed radix tree
    index: HashMap<(Symbol, Ustr, SymbolKind), Symbol>,
}
impl Ast {
    pub fn import_prefix(&self, sym: Symbol) -> &[Ustr] {
        match sym {
            Symbol::Import(i) => {
                let im = &self.import[i];
                if let Some(alias) = im.alias.as_ref() {
                    std::slice::from_ref(&alias.name)
                } else {
                    &im.path.names
                }
            }
            _ => unimplemented!(),
        }
    }
    //call f for each child under sym and prefix
    fn lookup<F: FnMut(Symbol)>(&self, sym: Symbol, prefix: Ustr, mut f: F) {
        match sym {
            Symbol::Root => {
                if let Some(&dst) = self.index.get(&(sym, prefix, SymbolKind::Import)) {
                    f(dst);
                }
                if let Some(&dst) = self.index.get(&(sym, prefix, SymbolKind::Dir)) {
                    f(dst);
                }
                if let Some(&dst) = self.index.get(&(sym, prefix, SymbolKind::Feature)) {
                    f(dst);
                }
            }
            Symbol::Feature(..) => {
                if let Some(&dst) = self.index.get(&(sym, prefix, SymbolKind::Attribute)) {
                    f(dst);
                }
            }
            Symbol::Attribute(..) => {
                if let Some(&dst) = self.index.get(&(sym, prefix, SymbolKind::Attribute)) {
                    f(dst);
                }
            }
            Symbol::Dir(..) => {
                if let Some(&dst) = self.index.get(&(sym, prefix, SymbolKind::Import)) {
                    f(dst);
                }
                if let Some(&dst) = self.index.get(&(sym, prefix, SymbolKind::Dir)) {
                    f(dst);
                }
            }
            _ => {}
        }
    }
    fn name(&self, sym: Symbol) -> Option<Ustr> {
        match sym {
            Symbol::Feature(i) => Some(self.features[i].name.name),
            Symbol::Attribute(i) => Some(self.attributes[i].name.name),
            Symbol::Import(i) => {
                if let Some(alias) = self.import[i].alias.as_ref() {
                    Some(alias.name)
                } else {
                    self.import[i].path.names.last().cloned()
                }
            }
            Symbol::Dir(i) => Some(self.dirs[i].name),
            _ => None,
        }
    }
    fn lsp_range(&self, sym: Symbol, source: &Rope) -> Option<tower_lsp::lsp_types::Range> {
        self.span(sym).and_then(|s| lsp_range(s, source))
    }
    //source range for a symbol if there is any
    fn span(&self, sym: Symbol) -> Option<Span> {
        match sym {
            Symbol::Feature(i) => Some(self.features[i].name.span.clone()),
            Symbol::Attribute(i) => Some(self.attributes[i].name.span.clone()),
            Symbol::Import(i) => {
                let import = &self.import[i];
                if let Some(alias) = import.alias.as_ref() {
                    Some(import.path.range().start..alias.span.end)
                } else {
                    Some(import.path.range())
                }
            }
            Symbol::Reference(i) => Some(self.references[i].path.range()),
            Symbol::Group(i) => Some(self.groups[i].span.clone()),
            Symbol::Constraint(i) => Some(self.constraints[i].span.clone()),
            Symbol::LangLvl(i) => Some(self.includes[i].span.clone()),
            Symbol::Keyword(i) => Some(self.keywords[i].span.clone()),
            _ => None,
        }
    }
    fn children(&self, sym: Symbol) -> impl Iterator<Item = Symbol> + DoubleEndedIterator + '_ {
        self.structure
            .children
            .get(&sym)
            .into_iter()
            .flat_map(|v| v.iter().cloned())
    }
    //utility iterators over different elements of interest
    fn all_imports(&self) -> impl Iterator<Item = Symbol> + DoubleEndedIterator {
        (0..self.import.len()).map(Symbol::Import)
    }
    fn all_features(&self) -> impl Iterator<Item = Symbol> {
        (0..self.features.len()).map(Symbol::Feature)
    }
    fn get_feature(&self, index: usize) -> Option<&Feature> {
        self.features.get(index)
    }
    fn containe_feature(&self, name: Ustr) -> bool {
        for feature in self.features.clone() {
            if feature.name.name == name {
                return true;
            }
        }

        false
    }
    fn get_attribute(&self, index: usize) -> Option<&Attribute> {
        self.attributes.get(index)
    }
    fn all_attributes(&self) -> impl Iterator<Item = Symbol> {
        (0..self.attributes.len()).map(Symbol::Attribute)
    }
    fn containe_attribute(&self, name: Ustr) -> bool {
        for attribute in self.attributes.clone() {
            if attribute.name.name == name {
                return true;
            }
        }

        false
    }
    fn all_references(&self) -> impl Iterator<Item = Symbol> {
        (0..self.references.len()).map(Symbol::Reference)
    }
    fn all_constraints(&self) -> impl Iterator<Item = Symbol> {
        (0..self.constraints.len()).map(Symbol::Constraint)
    }
    fn all_lang_lvls(&self) -> impl Iterator<Item = Symbol> {
        (0..self.includes.len()).map(Symbol::LangLvl)
    }
    //Search a symbol by byte offset in O(N)
    fn find(&self, offset: usize) -> Option<Symbol> {
        self.all_imports()
            .chain(self.all_features())
            .chain(self.all_attributes())
            .chain(self.all_references())
            .find(|s| self.span(*s).unwrap().contains(&offset))
    }
    fn find_all_of(&self, current: Symbol, name: Ustr) -> Vec<Symbol> {
        let mut relatives: Vec<Symbol> = vec![];
        if let Symbol::Feature(x) = current {
            if let Some(feature) = self.get_feature(x) {
                if feature.name.name == name {
                    relatives.push(Symbol::Feature(x));
                    return relatives;
                }
            }
        }
        // Go through Children
        match self.structure.children.get(&current) {
            Some(list) => {
                for sym in list {
                    relatives.append(self.find_all_of(sym.to_owned(), name).as_mut())
                }
            }
            None => {
                // info!("Relative Symbol {:?} has no children", from);
            }
        }

        return relatives;
    }
}
//Combines the AST with metadata, this is also a public interface to the AST.
#[derive(Clone, Debug)]
pub struct AstDocument {
    ast: Ast,
    pub source: Rope,
    pub tree: Tree,
    pub timestamp: Instant,
    pub errors: Vec<ErrorInfo>,
    pub path: Vec<Ustr>,
    pub uri: Url,
    pub id: FileID,
}
impl AstDocument {
    pub fn parent(&self, sym: Symbol, merge_root_features: bool) -> Option<Symbol> {
        if merge_root_features && matches!(sym, Symbol::Feature(..)) {
            Some(Symbol::Root)
        } else {
            self.ast.structure.parent.get(&sym).cloned()
        }
    }
    //parent feature of an attribute
    pub fn scope(&self, mut sym: Symbol) -> Symbol {
        while let Some(p) = self.parent(sym, true) {
            match sym {
                Symbol::Feature(..) => return sym,
                Symbol::Root => return sym,
                _ => {}
            }
            sym = p;
        }
        Symbol::Root
    }
    pub fn name(&self, sym: Symbol) -> Option<Ustr> {
        self.ast.name(sym)
    }
    //iterators over diffrent symbole types in the tree
    pub fn all_lang_lvls(&self) -> impl Iterator<Item = Symbol> {
        self.ast.all_lang_lvls()
    }
    pub fn all_imports(&self) -> impl Iterator<Item = Symbol> + DoubleEndedIterator {
        self.ast.all_imports()
    }
    pub fn all_features(&self) -> impl Iterator<Item = Symbol> {
        self.ast.all_features()
    }
    pub fn get_feature(&self, index: usize) -> Option<&Feature> {
        self.ast.get_feature(index)
    }
    pub fn containe_feature(&self, name: Ustr) -> bool {
        self.ast.containe_feature(name)
    }
    pub fn get_attribute(&self, index: usize) -> Option<&Attribute> {
        self.ast.get_attribute(index)
    }
    pub fn all_attributes(&self) -> impl Iterator<Item = Symbol> {
        self.ast.all_attributes()
    }
    pub fn containe_attribute(&self, name: Ustr) -> bool {
        self.ast.containe_attribute(name)
    }
    pub fn all_references(&self) -> impl Iterator<Item = Symbol> {
        self.ast.all_references()
    }
    pub fn all_constraints(&self) -> impl Iterator<Item = Symbol> {
        self.ast.all_constraints()
    }
    pub fn lang_lvl(&self, sym: Symbol) -> Option<&LanguageLevel> {
        if let Symbol::LangLvl(i) = sym {
            Some(&self.ast.includes[i].lang_lvl)
        } else {
            None
        }
    }
    pub fn group_mode(&self, sym: Symbol) -> Option<GroupMode> {
        match sym {
            Symbol::Group(id) => Some(self.ast.groups[id].mode.clone()),
            _ => None,
        }
    }
    pub fn constraint(&self, sym: Symbol) -> Option<&ConstraintDecl> {
        match sym {
            Symbol::Constraint(id) => Some(&self.ast.constraints[id]),
            _ => None,
        }
    }
    pub fn constraints(&self) -> &[ConstraintDecl] {
        &self.ast.constraints
    }

    pub fn imports(&self) -> &[Import] {
        &self.ast.import
    }

    pub fn value(&self, sym: Symbol) -> Option<&Value> {
        match sym {
            Symbol::Attribute(id) => Some(&self.ast.attributes[id].value.value),
            _ => None,
        }
    }
    pub fn direct_children(
        &self,
        sym: Symbol,
    ) -> impl Iterator<Item = Symbol> + DoubleEndedIterator + '_ {
        self.ast
            .structure
            .children
            .get(&sym)
            .into_iter()
            .flat_map(|i| i.iter())
            .cloned()
    }
    pub fn get_reference(&self, index: usize) -> Option<&Reference> {
        self.ast.references.get(index)
    }
    pub fn lsp_range(&self, sym: Symbol) -> Option<tower_lsp::lsp_types::Range> {
        self.ast.lsp_range(sym, &self.source)
    }

    pub fn span(&self, sym: Symbol) -> Option<Span> {
        self.ast.span(sym)
    }
    pub fn namespace(&self) -> Option<&Path> {
        self.ast.namespace.as_ref()
    }
    pub fn path(&self, sym: Symbol) -> &[Ustr] {
        match sym {
            Symbol::Import(i) => &self.ast.import[i].path.names,
            Symbol::Reference(i) => &self.ast.references[i].path.names,
            _ => unimplemented!(),
        }
    }
    pub fn import_prefix(&self, sym: Symbol) -> &[Ustr] {
        self.ast.import_prefix(sym)
    }
    pub fn depth(&self, sym: Symbol) -> u32 {
        match sym {
            Symbol::Feature(..) => 1,
            Symbol::Import(i) => self.ast.import[i].path.names.len() as u32,
            Symbol::Dir(i) => self.ast.dirs[i].depth,
            Symbol::Attribute(i) => self.ast.attributes[i].depth,
            _ => 0,
        }
    }
    //Find all symboles under root with prefix path.
    //Search branches can be aborted with a filter
    pub fn lookup<'a, F: Fn(Symbol) -> bool + 'a>(
        &'a self,
        root: Symbol,
        path: &'a [Ustr],
        filter: F,
    ) -> impl Iterator<Item = Symbol> + 'a {
        let mut stack = vec![(root, path)];
        std::iter::from_fn(move || loop {
            let (cur, base) = stack.pop()?;
            if base.is_empty() {
                return Some(cur);
            }
            self.ast.lookup(cur, base[0], |dst| {
                if filter(dst) {
                    stack.push((dst, &base[1..]));
                }
            })
        })
    }
    //Find imports for any prefix of path
    pub fn lookup_import<'a>(
        &'a self,
        path: &'a [Ustr],
    ) -> impl Iterator<Item = (Symbol, &'a [Ustr])> {
        let mut stack = vec![(Symbol::Root, path)];
        std::iter::from_fn(move || loop {
            let (cur, base) = stack.pop()?;

            if base.is_empty() {
                if matches!(cur, Symbol::Import(..)) {
                    return Some((cur, base));
                }
            }
            self.ast.lookup(cur, base[0], |dst| {
                if matches!(dst, Symbol::Dir(..) | Symbol::Import(..)) {
                    stack.push((dst, &base[1..]));
                }
            });
            if matches!(cur, Symbol::Import(..)) {
                return Some((cur, base));
            }
        })
    }
    //Also track the binding for path, each segment of path has some symbole bound to it
    pub fn lookup_with_binding<'a, F: Fn(Symbol) -> bool + 'a>(
        &'a self,
        root: Symbol,
        path: &'a [Ustr],
        filter: F,
    ) -> impl Iterator<Item = Vec<Symbol>> + 'a {
        let mut stack = vec![(root, path, vec![])];
        std::iter::from_fn(move || loop {
            let (cur, base, bind) = stack.pop()?;
            if base.is_empty() {
                return Some(bind);
            }
            self.ast.lookup(cur, base[0], |dst| {
                if filter(dst) {
                    stack.push((dst, &base[1..], [bind.as_slice(), &[dst]].concat()));
                }
            })
        })
    }
    // returns all Symbols with same name, used for cardinality resolving
    pub fn get_all_entities(&self, path: &[Ustr]) -> Vec<Symbol> {
        let ustr_path = Ustr::from(path.iter().map(|s| s.to_string()).join(".").as_str());
        let mut res = vec![];
        for i in 0..self.ast.features.len() {
            if ustr_path == self.get_feature(i).unwrap().name.name {
                res.push(Symbol::Feature(i));
            }
        }
        let mut path: Vec<Ustr> = path.iter().cloned().collect();
        if let Some(name) = path.pop() {
            let features = self.get_all_entities(&path);
            for i in features {
                if let Some(sym) = self.ast.index.get(&(i, name, SymbolKind::Attribute)) {
                    res.push(*sym);
                }
            }
        }
        res
    }
    //prefix of sym from root
    pub fn prefix(&self, mut sym: Symbol) -> Vec<Ustr> {
        if matches!(sym, Symbol::Import(..)) {
            return self.ast.import_prefix(sym).into();
        }
        let mut out = Vec::new();
        loop {
            if let Some(name) = self.ast.name(sym) {
                out.push(name);
            }
            if let Some(p) = self.ast.structure.parent.get(&sym) {
                if matches!(p, Symbol::Feature(..)) {
                    break;
                }
                sym = *p;
            } else {
                break;
            }
        }
        out
    }
    pub fn type_of(&self, sym: Symbol) -> Option<Type> {
        match sym {
            Symbol::Root => Some(Type::Namespace),
            Symbol::Feature(i) => Some(self.ast.features[i].ty),
            Symbol::Attribute(i) => match &self.ast.attributes[i].value.value {
                Value::Void => Some(Type::Void),
                Value::Vector => Some(Type::Vector),
                Value::Bool(..) => Some(Type::Bool),
                Value::Attributes => Some(Type::Attributes),
                Value::String(..) => Some(Type::String),
                Value::Number(..) => Some(Type::Real),
            },
            Symbol::Import(..) => Some(Type::Namespace),
            Symbol::Dir(..) => Some(Type::Namespace),
            _ => None,
        }
    }
    pub fn find(&self, offset: usize) -> Option<Symbol> {
        self.ast.find(offset)
    }
    //All children under root, when merge_root_features sub features are ignored
    pub fn visit_named_children<F: FnMut(Symbol, &[Ustr]) -> bool>(
        &self,
        root: Symbol,
        merge_root_features: bool,
        mut f: F,
    ) {
        self.visit_named_children_depth(root, merge_root_features, |sym, prefix, _| f(sym, prefix))
    }
    //Iterate all named symbole under root and track their prefix from root
    pub fn visit_named_children_depth<F: FnMut(Symbol, &[Ustr], usize) -> bool>(
        &self,
        root: Symbol,
        merge_root_features: bool,
        mut f: F,
    ) {
        let mut stack: Vec<(Symbol, usize)> = vec![(root, 0)];
        let mut prefix = vec![];
        while let Some((cur, depth)) = stack.pop() {
            prefix.truncate(depth.saturating_sub(1));
            let mut explore = true;
            if let Some(name) = self.name(cur) {
                if cur != root {
                    prefix.push(name);
                    explore = f(cur, &prefix, depth);
                }
            }
            if explore {
                for i in self.ast.children(cur).rev() {
                    if merge_root_features
                        && !matches!(i, Symbol::Attribute(..))
                        && !matches!(root, Symbol::Root)
                    {
                        continue;
                    }
                    match i {
                        Symbol::Feature(..) => {
                            stack.push((i, 1));
                        }
                        Symbol::Attribute(..) | Symbol::Dir(..) | Symbol::Import(..) => {
                            stack.push((i, depth + 1));
                        }
                        _ => {
                            stack.push((i, depth));
                        }
                    }
                }
            }
        }
    }
    pub fn visit_children<F: FnMut(Symbol) -> bool>(
        &self,
        root: Symbol,
        merge_root_features: bool,
        mut f: F,
    ) {
        self.visit_children_depth(root, merge_root_features, |sym, _| f(sym));
    }
    pub fn find_all_of(&self, name: Ustr) -> Vec<Symbol> {
        self.ast.find_all_of(Symbol::Root, name)
    }
    //Iterate all named symbole under root
    pub fn visit_children_depth<F: FnMut(Symbol, u32) -> bool>(
        &self,
        root: Symbol,
        merge_root_features: bool,
        mut f: F,
    ) {
        let mut stack = vec![(root, 0)];
        while let Some((cur, depth)) = stack.pop() {
            let mut explore = true;
            if cur != root {
                explore = f(cur, depth);
            }
            if explore {
                for i in self.ast.children(cur).rev() {
                    if merge_root_features
                        && matches!(i, Symbol::Feature(..))
                        && !matches!(root, Symbol::Root)
                    {
                        continue;
                    }
                    if matches!(
                        i,
                        Symbol::Feature(..) | Symbol::Dir(..) | Symbol::Attribute(..)
                    ) {
                        stack.push((i, depth + 1));
                    } else {
                        stack.push((i, depth));
                    }
                }
            }
        }
    }
    //Iterate all attributes under root, and track theire associated feature
    pub fn visit_attributes<'a, F: FnMut(Symbol, Symbol, &[Ustr])>(&self, root: Symbol, mut f: F) {
        assert!(matches!(root, Symbol::Feature(..) | Symbol::Root));
        let mut owner = root;
        let mut under_feature = 0;
        self.visit_named_children(root, false, |i, prefix| match i {
            Symbol::Feature(..) => {
                owner = i;
                under_feature = 1;
                true
            }
            Symbol::Attribute(..) => {
                f(owner, i, &prefix[under_feature..]);
                true
            }
            _ => false,
        });
    }
    pub fn new(source: Rope, tree: Tree, uri: Url, timestamp: Instant) -> Self {
        transform::visit_root(source, tree, uri, timestamp)
    }
}
