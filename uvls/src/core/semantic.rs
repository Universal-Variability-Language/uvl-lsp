use crate::core::*;

use hashbrown::{HashMap, HashSet};
use log::info;
use percent_encoding::percent_decode_str;
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
        Self((percent_decode_str(i).decode_utf8().unwrap().into_owned()[..]).into())
    }
    pub fn from_uri(uri: &Url) -> FileID {
        Self::new(uri.as_str())
    }
    pub fn max() -> FileID {
        Self("".into())
    }
    pub fn url(&self) -> Url {
        Url::parse(self.0.as_str()).unwrap()
    }
    pub fn is_virtual(&self) -> bool {
        self.0.as_str().ends_with(".VIRTUAL_CONFIG")
    }
    pub fn is_config(&self) -> bool {
        self.0.as_str().ends_with(".json") | self.is_virtual()
    }
    pub fn filepath(&self) -> std::path::PathBuf {
        self.url().to_file_path().unwrap()
    }
    pub fn as_str(&self) -> &str {
        &self.0
    }
}
impl Debug for FileID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0.as_str().split("/").last().unwrap_or("NONE"))
    }
}
pub type AstFiles = HashMap<FileID, Arc<AstDocument>>;
pub type ConfigFiles = HashMap<FileID, Arc<ConfigDocument>>;
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
    pub files: AstFiles,
    pub configs: ConfigFiles,
}
impl RootGraph {
    pub fn contains(&self, uri: &Url) -> bool {
        self.contains_id(FileID::new(uri.as_str()))
    }
    pub fn timestamp(&self, uri: &Url) -> Option<Instant> {
        self.config_by_uri(uri)
            .map(|i| i.timestamp)
            .or(self.file_by_uri(uri).map(|i| i.timestamp))
    }
    pub fn contains_id(&self, id: FileID) -> bool {
        self.files.contains_key(&id) || self.configs.contains_key(&id)
    }
    pub fn type_of(&self, sym: RootSymbol) -> Option<Type> {
        if matches!(sym.sym, Symbol::Reference(..)) {
            let file = &self.cache.ast[&sym.file];
            file.resolved
                .get(&sym.sym)
                .and_then(|sym| self.type_of(*sym))
        } else {
            self.file(sym.file).type_of(sym.sym)
        }
    }
    pub fn config_by_uri(&self, name: &Url) -> Option<&ConfigDocument> {
        self.configs.get(&FileID::new(name.as_str())).map(|i| &**i)
    }
    pub fn file_by_uri(&self, name: &Url) -> Option<&AstDocument> {
        self.cache
            .ast
            .get(&FileID::new(name.as_str()))
            .map(|i| &*i.content)
    }
    pub fn file(&self, id: FileID) -> &AstDocument {
        &self.cache.ast[&id].content
    }
    pub fn file_id(&self, name: &Url) -> Option<FileID> {
        let id = FileID::new(name.as_str());
        if self.cache.ast.contains_key(&id) || self.configs.contains_key(&id) {
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
        resolve::resolve(&self.files, &self.cache.fs, origin, path)
    }
    pub fn revision(&self) -> u64 {
        self.revision
    }
    //find all symbols from origin under path, also keep track
    //of which sections of the search path are bound to which symbols
    pub fn resolve_with_binding<'a>(
        &'a self,
        origin: FileID,
        path: &'a [Ustr],
    ) -> impl Iterator<Item = Vec<(RootSymbol, usize)>> + 'a {
        resolve::resolve_with_bind(&self.files, &self.cache.fs, origin, path)
    }
    //find all attributes from origin under context, useful for aggregates
    pub fn resolve_attributes<'a, F: FnMut(RootSymbol, &[Ustr])>(
        &'a self,
        origin: FileID,
        context: &'a [Ustr],
        f: F,
    ) {
        resolve::resolve_attributes(&self.files, &self.cache.fs, origin, context, f)
    }
    pub fn fs(&self) -> &FileSystem {
        &self.cache.fs
    }
    pub fn dump(&self) {
        info!("{:#?}", self);
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
                    if let Some(ns) = file.namespace() {
                        if err.errors.contains_key(&file.id) {
                            err.span(ns.range(), file.id, 100, "namespace already defined");
                        }
                    }
                }
            }
        }
        Self {
            cancel: CancellationToken::new(),
            cache: Cache::new(old, files, configs, &dirty, revision, err),
            revision,
            files: files.clone(),
            configs: configs.clone(),
        }
    }
}
