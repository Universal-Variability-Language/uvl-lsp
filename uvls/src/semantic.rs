use crate::ast::*;
use crate::cache::*;
use crate::check::ErrorsAcc;
use crate::config::ConfigDocument;
use crate::config::ConfigValue;
use crate::resolve;
use hashbrown::{HashMap, HashSet};
use log::info;
use std::fmt::Debug;
use std::sync::Arc;
use tokio::time::Instant;
use tokio_util::sync::CancellationToken;
use tower_lsp::lsp_types::*;
use ustr::Ustr;

pub type Snapshot = Arc<RootGraph>;
#[derive(Hash, PartialEq, Eq, Clone, Copy)]
pub struct FileID(Ustr);
impl FileID {
    pub fn new(i: &str) -> Self {
        assert!(i != "");
        Self(i.into())
    }
    pub fn max() -> FileID {
        Self("".into())
    }
    pub fn ptr(&self) -> *const u8 {
        self.0.as_ptr()
    }
    pub fn url(&self) -> Option<Url> {
        Url::parse(self.0.as_str()).ok()
    }
    pub fn is_virtual(&self) -> bool {
        self.0.as_str().ends_with(".VIRTUAL_CONFIG")
    }

    pub fn is_config(&self) -> bool {
        self.0.as_str().ends_with(".json") | self.is_virtual()
    }
}
impl Debug for FileID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0.as_str().split("/").last().unwrap_or("NONE"))
    }
}
pub type AstFiles = HashMap<FileID, Arc<AstDocument>>;
pub type ConfigFiles = HashMap<FileID, Arc<ConfigDocument>>;
pub type DirectConfig = HashMap<FileID, HashMap<Vec<Ustr>, ConfigValue>>;
#[derive(Hash, PartialEq, Eq, Debug, Clone, Copy)]
pub struct RootSymbol {
    pub file: FileID,
    pub sym: Symbol,
}
impl std::fmt::Display for RootSymbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}:{:?}",
            self.file.0.as_str().split("/").last().unwrap(),
            self.sym
        )
    }
}
//A fully linked version of all files, computed asynchronously
#[derive(Debug, Clone, Default)]
pub struct RootGraph {
    cache: Cache,
    revision: u64,
    cancel: CancellationToken,
}
impl RootGraph {
    pub fn containes(&self, uri: &Url) -> bool {
        self.containes_id(FileID::new(uri.as_str()))
    }
    pub fn timestamp(&self, uri: &Url) -> Option<Instant> {
        self.config_by_uri(uri)
            .map(|i| i.timestamp)
            .or(self.file_by_uri(uri).map(|i| i.timestamp))
    }
    pub fn containes_id(&self, id: FileID) -> bool {
        self.cache.files.contains_key(&id) || self.cache.configs.contains_key(&id)
    }
    pub fn try_file(&self, id: FileID) -> Option<&AstDocument> {
        self.cache.files.get(&id).map(|f| &**f)
    }
    pub fn type_of(&self, sym: RootSymbol) -> Option<Type> {
        if matches!(sym.sym, Symbol::Reference(..)) {
            let module = self.cache.file2module[&sym.file];
            self.cache.modules[module]
                .ref_map
                .get(&sym)
                .and_then(|sym| self.type_of(*sym))
        } else {
            self.file(sym.file).type_of(sym.sym)
        }
    }
    pub fn span(&self, sym: RootSymbol) -> Option<Span> {
        self.file(sym.file).span(sym.sym)
    }

    pub fn lsp_range(&self, sym: RootSymbol) -> Option<Range> {
        self.file(sym.file).lsp_range(sym.sym)
    }
    pub fn config_by_uri(&self, name: &Url) -> Option<&ConfigDocument> {
        self.cache
            .configs
            .get(&FileID::new(name.as_str()))
            .map(|i| &**i)
    }
    pub fn file_by_uri(&self, name: &Url) -> Option<&AstDocument> {
        self.cache
            .files
            .get(&FileID::new(name.as_str()))
            .map(|i| &**i)
    }
    pub fn file(&self, id: FileID) -> &AstDocument {
        &self.cache.files[&id]
    }
    pub fn file_id(&self, name: &Url) -> Option<FileID> {
        let id = FileID::new(name.as_str());
        if self.cache.configs.contains_key(&id) || self.cache.files.contains_key(&id) {
            Some(id)
        } else {
            None
        }
    }
    pub fn cancellation_token(&self) -> CancellationToken {
        self.cancel.child_token()
    }
    pub fn cancel(&self) {
        self.cancel.cancel();
    }

    //find all symbols from origin under path
    pub fn resolve<'a>(
        &'a self,
        origin: FileID,
        path: &'a [Ustr],
    ) -> impl Iterator<Item = RootSymbol> + 'a {
        resolve::resolve(&self.cache.files, &self.cache.fs, origin, path)
    }
    pub fn resolve_sym<'a>(&'a self, sym: RootSymbol) -> Option<RootSymbol> {
        if matches!(sym.sym, Symbol::Reference(..)) {
            let module = self.cache.file2module[&sym.file];
            self.cache.modules[module].ref_map.get(&sym).cloned()
        } else {
            Some(sym)
        }
    }
    pub fn revision(&self) -> u64 {
        self.revision
    }
    //find all symbols from origin under path, also keep track
    //of which sections of the search path are bound to which symboles
    pub fn resolve_with_binding<'a>(
        &'a self,
        origin: FileID,
        path: &'a [Ustr],
    ) -> impl Iterator<Item = Vec<(RootSymbol, usize)>> + 'a {
        resolve::resolve_with_bind(&self.cache.files, &self.cache.fs, origin, path)
    }
    //find all attributes from origin under context, usefull for aggregates
    pub fn resolve_attributes<'a, F: FnMut(RootSymbol, &[Ustr])>(
        &'a self,
        origin: FileID,
        context: &'a [Ustr],
        f: F,
    ) {
        resolve::resolve_attributes(&self.cache.files, &self.cache.fs, origin, context, f)
    }
    //find all attributes from origin under context, usefull for aggregates, also keep track
    //of the owner feature and file
    pub fn resolve_attributes_with_feature<
        'a,
        F: FnMut(RootSymbol, RootSymbol, &[Ustr], &AstDocument),
    >(
        &'a self,
        origin: FileID,
        context: &'a [Ustr],
        f: F,
    ) {
        resolve::resolve_attributes_with_feature(
            &self.cache.files,
            &self.cache.fs,
            origin,
            context,
            f,
        )
    }
    pub fn iter_files(&self) -> impl Iterator<Item = (FileID, &'_ AstDocument)> + '_ {
        self.cache.files.iter().map(|(i, v)| (*i, &**v))
    }
    pub fn fs(&self) -> &FileSystem {
        &self.cache.fs
    }
    pub fn dump(&self) {
        info!("{:#?}", &self.cache.files);
    }
    pub fn cache(&self) -> &Cache {
        &self.cache
    }
    pub fn new(
        files: &HashMap<FileID, Arc<AstDocument>>,
        configs: &HashMap<FileID, Arc<ConfigDocument>>,
        revision: u64,
        old: &Cache,
        err: &mut ErrorsAcc,
        check_state: &mut HashMap<FileID, Instant>,
    ) -> Self {
        let mut dirty = HashSet::new();
        for file in files.values() {
            if check_state
                .get(&file.id)
                .map(|old| old != &file.timestamp)
                .unwrap_or(true)
            {
                dirty.insert(file.id);
                check_state.insert(file.id, file.timestamp);
                err.errors.insert(file.id, file.errors.clone());
            }
        }
        for conf in configs.values() {
            if check_state
                .get(&conf.id)
                .map(|old| old != &conf.timestamp)
                .unwrap_or(true)
            {
                dirty.insert(conf.id);
                check_state.insert(conf.id, conf.timestamp);
                err.errors.insert(conf.id, conf.syntax_errors.clone());
            }
        }
        {
            let mut file_paths = HashSet::new();
            for file in files.values() {
                if !file_paths.insert(file.path.as_slice()) {
                    //info!("{:?}", file.namespace());
                    if let Some(ns) = file.namespace() {
                        if err.errors.contains_key(&file.id) {
                            err.span(ns.range(), file.id, 100, "namespace already defined");
                        }
                    }
                }
            }
        }
        //info!("dirty {:?}",dirty);
        Self {
            cancel: CancellationToken::new(),
            cache: Cache::new(old, files, configs, &dirty, revision, err),
            revision,
        }
    }
}