use crate::core::*;
use config::*;
use hashbrown::HashMap;
use indexmap::IndexSet;
use log::info;
use resolve;
use tokio::time::Instant;
use ustr::Ustr;

use std::sync::Arc;
#[derive(Hash, PartialEq, Eq, Debug, Clone, Copy)]
pub struct InstanceID(pub usize);
impl InstanceID {
    pub fn sym(&self, sym: Symbol) -> ModuleSymbol {
        ModuleSymbol {
            instance: *self,
            sym,
        }
    }
}
//A ast symbole within a module context
#[derive(Hash, PartialEq, Eq, Debug, Clone, Copy)]
pub struct ModuleSymbol {
    pub instance: InstanceID,
    pub sym: Symbol,
}

impl resolve::AstContainer for HashMap<FileID, Arc<LinkedAstDocument>> {
    fn get(&self, file: FileID) -> &AstDocument {
        &*self[&file].content
    }
}
//Depth first iteration
fn iterate_instances<'a>(
    root: FileID,
    files: &'a HashMap<FileID, Arc<LinkedAstDocument>>,
) -> impl Iterator<Item = (ModuleSymbol, InstanceID, FileID, u32)> + 'a {
    let mut counter = 0;
    let mut stack = vec![(
        ModuleSymbol {
            instance: InstanceID(0),
            sym: Symbol::Root,
        },
        root,
        0,
    )];
    std::iter::from_fn(move || {
        stack.pop().map(|(origin, file, depth)| {
            let file = &files[&file];
            for (im, tgt) in file
                .content
                .all_imports()
                .rev()
                .map(|i| (i, file.resolved[&i].file))
            {
                stack.push((
                    ModuleSymbol {
                        instance: InstanceID(counter),
                        sym: im,
                    },
                    tgt,
                    depth + 1,
                ));
            }
            counter += 1;
            return (origin, InstanceID(counter - 1), file.content.id, depth);
        })
    })
}

//An actual instance of a root file with all subfiles
//A module is basically a depth first iteration of all features and recusive sub file contents
//Each import statement creates a new instance of some ast file. So features and attributes can
//exist multiple times in diffrent instances. This struct allows for easy instance iteration and
//resolution. Since references in diffrent instances have diffrent resolutions, we currently
//reresolve references to non local symbols, TODO this can be avoided using a static instance
//encoding scheme?.
#[derive(Debug)]
pub struct Module {
    instance_files: Vec<FileID>,
    instances: IndexSet<(InstanceID, Symbol)>,
    pub timestamp: Instant,
    pub files: HashMap<FileID, Arc<LinkedAstDocument>>,
    pub ok: bool,
}
impl Module {
    pub fn get_instance(&self, instance: InstanceID, sym: Symbol) -> InstanceID {
        InstanceID(self.instances.get_index_of(&(instance, sym)).unwrap())
    }
    pub fn new(
        root: FileID,
        fs: &FileSystem,
        files: &HashMap<FileID, Arc<LinkedAstDocument>>,
    ) -> Module {
        let mut members = fs.recursive_imports(root);
        members.push(root);
        let ok = members.iter().all(|i| files[i].ok);
        if ok {
            let mut instances = IndexSet::new();
            let mut instance_files = Vec::new();
            for (origin, _, file, _) in iterate_instances(root, files) {
                instances.insert((origin.instance, origin.sym));
                instance_files.push(file);
            }
            Module {
                files: files
                    .iter()
                    .filter(|(k, _)| members.contains(k))
                    .map(|(k, v)| (*k, v.clone()))
                    .collect(),
                instance_files,
                instances,
                timestamp: Instant::now(),
                ok,
            }
        } else {
            Module {
                files: files
                    .iter()
                    .filter(|(k, _)| members.contains(k))
                    .map(|(k, v)| (*k, v.clone()))
                    .collect(),
                instance_files: [root].into(),
                instances: IndexSet::new(),
                timestamp: Instant::now(),
                ok,
            }
        }
    }
    //Resolves references inside this module
    pub fn resolve_value(&self, src_sym: ModuleSymbol) -> ModuleSymbol {
        assert!(self.ok);
        match src_sym.sym {
            Symbol::Feature(_) | Symbol::Attribute(_) => src_sym,
            Symbol::Reference(_) => {
                let src_file = &self.files[&self.instance_files[src_sym.instance.0]];
                let tgt = src_file.resolved[&src_sym.sym];
                //Fast path
                if tgt.file == src_file.content.id {
                    return ModuleSymbol {
                        instance: src_sym.instance,
                        sym: tgt.sym,
                    };
                }
                let tgt_file = &self.files[&tgt.file];
                let path = src_file.content.path(src_sym.sym);
                let instance_path = &path[0..path.len() - tgt_file.content.depth(tgt.sym) as usize];
                let mut stack = vec![(instance_path, src_sym.instance)];

                while let Some((prefix, instance)) = stack.pop() {
                    let file = self.file(instance);
                    if prefix.len() == 0 && file.id == tgt.file {
                        return ModuleSymbol {
                            sym: tgt.sym,
                            instance,
                        };
                    }
                    for (sym, tail) in file.lookup_import(prefix) {
                        stack.push((tail, self.get_instance(instance, sym)));
                    }
                }

                info!("path {instance_path:?}");
                info!("mod  {self:?}");
                panic!("unresolved module value");
            }
            _ => panic!("{src_sym:?} not a value"),
        }
    }
    //Bind a recursive configuration doc to a linear set of symbols
    pub fn resolve_config<E: FnMut(Span, String)>(
        &self,
        doc: &Vec<ConfigEntry>,
        mut err: E,
    ) -> (
        HashMap<ModuleSymbol, ConfigValue>,
        HashMap<ModuleSymbol, Span>,
    ) {
        assert!(self.ok);
        let mut out = HashMap::new();
        let mut out_span = HashMap::new();
        let mut stack = vec![(InstanceID(0), doc.as_slice())];
        while let Some((instance, config)) = stack.pop() {
            let file = self.file(instance);
            for c in config.iter() {
                match c {
                    ConfigEntry::Value(path, val) => {
                        if let Some(sym) = file
                            .lookup(Symbol::Root, &path.names, |sym| {
                                matches!(sym, Symbol::Feature(..) | Symbol::Attribute(..))
                            })
                            .next()
                        {
                            if file.type_of(sym).unwrap() == val.ty() {
                                out.insert(ModuleSymbol { instance, sym }, val.clone());
                                out_span.insert(ModuleSymbol { instance, sym }, path.range());
                            } else {
                                err(
                                    path.range(),
                                    format!(
                                        "expected {} got {}",
                                        file.type_of(sym).unwrap(),
                                        val.ty()
                                    ),
                                );
                            }
                        } else {
                            err(path.range(), format!("unresolved value",));
                        }
                    }
                    ConfigEntry::Import(path, val) => {
                        if let Some(sym) = file
                            .lookup(Symbol::Root, &path.names, |sym| {
                                matches!(sym, Symbol::Import(..) | Symbol::Dir(..))
                            })
                            .find(|sym| matches!(sym, Symbol::Import(..)))
                        {
                            stack.push((self.get_instance(instance, sym), &val));
                        } else {
                            err(path.range(), format!("unresolved import",));
                        }
                    }
                }
            }
        }
        (out, out_span)
    }

    pub fn file(&self, instance: InstanceID) -> &AstDocument {
        &self.files[&self.instance_files[instance.0]].content
    }
    pub fn type_of(&self, sym: ModuleSymbol) -> Type {
        assert!(self.ok);
        let sym = self.resolve_value(sym);
        self.files[&self.instance_files[sym.instance.0]]
            .content
            .type_of(sym.sym)
            .unwrap()
    }
    //Visit all instances in the module
    pub fn instances<'a>(&'a self) -> impl Iterator<Item = (InstanceID, &'a AstDocument)> {
        assert!(self.ok);
        self.instance_files
            .iter()
            .enumerate()
            .map(|(i, k)| (InstanceID(i), &*self.files[k].content))
    }
    pub fn instances_depth<'a>(
        &'a self,
    ) -> impl Iterator<Item = (ModuleSymbol, InstanceID, &'a AstDocument, u32)> {
        assert!(self.ok);
        iterate_instances(self.instance_files[0], &self.files)
            .map(|(origin, i, file, depth)| (origin, i, &*self.files[&file].content, depth))
    }
}
//Configuration with a module and resolved configuration symboles
#[derive(Debug, Clone)]
pub struct ConfigModule {
    pub module: Arc<Module>,
    pub values: HashMap<ModuleSymbol, ConfigValue>,
    pub source_map: HashMap<ModuleSymbol, Span>,
}
impl ConfigModule {
    fn serialize_rec(&self, path: &[Ustr], i: InstanceID) -> ConfigEntry {
        let file = self.file(i);
        let mut entries = Vec::new();
        for im in file.all_imports() {
            let entry = self.serialize_rec(file.import_prefix(im), self.get_instance(i, im));
            if !entry.is_empty() {
                entries.push(entry);
            }
        }
        file.visit_named_children(Symbol::Root, false, |sym, prefix| match sym {
            Symbol::Feature(_) | Symbol::Attribute(_) => {
                if let Some(config) = self.values.get(&i.sym(sym)) {
                    entries.push(ConfigEntry::Value(
                        Path {
                            names: prefix.to_vec(),
                            spans: Vec::new(),
                        },
                        config.clone(),
                    ))
                }
                true
            }
            _ => false,
        });
        ConfigEntry::Import(
            Path {
                names: path.to_vec(),
                spans: Vec::new(),
            },
            entries,
        )
    }
    //Turns a the set of linear configuration values of this module into theire recusive from
    //used in json
    pub fn serialize(&self) -> Vec<ConfigEntry> {
        let ConfigEntry::Import(_,v) = self.serialize_rec(&[],InstanceID(0)) else {unreachable!()};
        v
    }
}
impl std::ops::Deref for ConfigModule {
    type Target = Module;
    fn deref(&self) -> &Self::Target {
        &self.module
    }
}
