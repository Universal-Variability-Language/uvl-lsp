use crate::core::*;
use crate::ide::completion::*;
use hashbrown::HashMap;
use log::info;
use ropey::Rope;
use tower_lsp::lsp_types::*;
use tree_sitter::Node;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TextObjectKind {
    Attribute,
    Feature,
    FeatureReference,
    Reference(Type),
    ImportPath,
    ImportAlias,
    Aggregate(Option<Path>),
}

#[derive(Clone, Debug)]
pub struct TextObject {
    path: Path,
    kind: TextObjectKind,
    selected_segment: usize,
}
pub fn attribute_prefix(node: Node, source: &Rope) -> Option<Path> {
    match node.kind() {
        "attribute_value" => {
            let name = parse_name(node.child_by_field_name("name")?, source)?;
            Some(attribute_prefix(node.parent()?, source)?.append(&name))
        }
        "blk" => {
            let header = node.child_by_field_name("header")?;
            match header.kind() {
                "name" => parse_path(header, source),
                "typed_feature" => parse_path(header.child_by_field_name("name")?, source),
                _ => None,
            }
        }
        "attributes" => attribute_prefix(node.parent()?, source),
        _ => None,
    }
}
pub fn whole_expr(node: Node) -> Node {
    match node.parent().map(|i| i.kind()) {
        Some("blk") => node,
        Some(_) => whole_expr(node.parent().unwrap()),
        _ => node,
    }
}

pub fn find_text_object_impl(
    node: Node,
    source: &Rope,
    pos: &Position,
    offset: usize,
    file: FileID,
    root: &Snapshot,
) -> Option<TextObject> {
    match find_section(node) {
        Section::Imports => {
            let (path, p_node) = longest_path(node, source)?;
            match p_node.kind() {
                "name" => Some(TextObject {
                    kind: TextObjectKind::ImportAlias,
                    selected_segment: path.segment(offset),
                    path,
                }),
                "path" => Some(TextObject {
                    kind: TextObjectKind::ImportPath,
                    selected_segment: path.segment(offset),
                    path,
                }),
                _ => None,
            }
        }
        Section::Features => {
            let (path, p_node) = longest_path(node, source)?;
            match p_node.kind() {
                "name" => Some(TextObject {
                    kind: TextObjectKind::Feature,
                    selected_segment: 0,
                    path,
                }),
                "path" => Some(TextObject {
                    kind: TextObjectKind::FeatureReference,
                    selected_segment: path.segment(offset),
                    path,
                }),
                _ => None,
            }
        }
        Section::Attribute => match node.kind() {
            "name" => {
                let path = attribute_prefix(node.parent().unwrap(), source)?;
                Some(TextObject {
                    kind: TextObjectKind::Attribute,
                    selected_segment: path.len() - 1,
                    path,
                })
            }
            _ => None,
        },
        Section::Constraints => {
            let (path, p_node) = longest_path(node, source)?;

            match estimate_expr(p_node, pos, source) {
                CompletionEnv::Numeric | CompletionEnv::Constraint => {
                    let mut ty_map = HashMap::new();
                    resolve::estimate_types(
                        whole_expr(p_node),
                        Type::Bool.into(),
                        source,
                        &mut ty_map,
                        file,
                        root,
                    );

                    Some(TextObject {
                        kind: TextObjectKind::Reference(
                            ty_map
                                .get(&p_node.id())
                                .iter()
                                .next()
                                .map(|t| **t)
                                .unwrap_or(Type::Bool),
                        ),
                        selected_segment: path.segment(offset),
                        path,
                    })
                }

                CompletionEnv::Aggregate { context } => Some(TextObject {
                    kind: TextObjectKind::Aggregate(context),
                    selected_segment: path.segment(offset),
                    path,
                }),
                _ => None,
            }
        }
        _ => None,
    }
}
pub fn find_text_object(
    draft: &Draft,
    pos: &Position,
    file: FileID,
    root: &Snapshot,
) -> Option<TextObject> {
    match draft {
        Draft::JSON { .. } => {
            //TODO
            None
        }
        Draft::UVL { source, tree, .. } => {
            let start = char_offset(pos, source);
            let end = start + 1;
            find_text_object_impl(
                tree.root_node().named_descendant_for_byte_range(
                    source.try_char_to_byte(start).ok()?,
                    source.try_char_to_byte(end).ok()?,
                )?,
                source,
                pos,
                source.try_char_to_byte(start).ok()?,
                file,
                root,
            )
        }
    }
}

fn find_definitions(
    root: &Snapshot,
    draft: &Draft,
    pos: &Position,
    uri: &Url,
) -> Option<Vec<RootSymbol>> {
    let file_id = root.file_id(uri)?;
    let obj = find_text_object(draft, pos, file_id, root)?;
    info!("{:?}", obj);

    let _file = root.file(file_id);
    match obj.kind {
        TextObjectKind::ImportAlias => {
            for i in root.resolve(file_id, &obj.path.names) {
                info!("{:?}", i);
                if matches!(i.sym, Symbol::Root) {
                    return Some(vec![i]);
                }
            }
            None
        }
        TextObjectKind::ImportPath => root.fs().resolve(file_id, &obj.path.names).map(|f| {
            vec![RootSymbol {
                file: f,
                sym: Symbol::Root,
            }]
        }),
        TextObjectKind::FeatureReference => {
            for bind in root.resolve_with_binding(file_id, &obj.path.names) {
                let last = bind.last().unwrap().0;
                info!("{:?}", bind);
                if matches!(last.sym, Symbol::Feature(..)) {
                    return Some(vec![bind
                        .iter()
                        .find_map(|(sym, index)| {
                            if obj.selected_segment < *index {
                                Some(*sym)
                            } else {
                                None
                            }
                        })
                        .unwrap_or(last)]);
                }
            }
            None
        }

        TextObjectKind::Reference(ty) => {
            for bind in root.resolve_with_binding(file_id, &obj.path.names) {
                let last = bind.last().unwrap().0;
                let dst_file = root.file(last.file);
                info!("{:?}", bind);

                if dst_file
                    .type_of(last.sym)
                    .map(|dty| ty == dty)
                    .unwrap_or(false)
                {
                    return Some(vec![bind
                        .iter()
                        .find_map(|(sym, index)| {
                            if obj.selected_segment < *index {
                                Some(*sym)
                            } else {
                                None
                            }
                        })
                        .unwrap_or(last)]);
                }
            }
            for bind in root.resolve_with_binding(file_id, &obj.path.names) {
                let last = bind.last().unwrap().0;
                let dst_file = root.file(last.file);
                info!("{:?}", bind);
                if dst_file
                    .type_of(last.sym)
                    .map(|dty| matches!(dty, Type::String | Type::Real | Type::Bool))
                    .unwrap_or(false)
                {
                    return Some(vec![bind
                        .iter()
                        .find_map(|(sym, index)| {
                            if obj.selected_segment < *index {
                                Some(*sym)
                            } else {
                                None
                            }
                        })
                        .unwrap_or(last)]);
                }
            }
            None
        }
        TextObjectKind::Aggregate(ctx) => {
            let mut out = Vec::new();
            root.resolve_attributes(
                file_id,
                ctx.as_ref().map(|ctx| ctx.names.as_slice()).unwrap_or(&[]),
                |sym, prefix| {
                    let common = prefix
                        .iter()
                        .zip(obj.path.names.iter())
                        .take_while(|(i, k)| i == k)
                        .count();
                    if common == obj.path.len() {
                        out.push(sym);
                    }
                },
            );
            Some(out)
        }
        TextObjectKind::Feature => {
            for i in root.resolve(file_id, &obj.path.names) {
                if matches!(i.sym, Symbol::Feature(_)) {
                    return Some(vec![i]);
                }
            }
            None
        }
        TextObjectKind::Attribute => {
            for i in root.resolve(file_id, &obj.path.names) {
                if matches!(i.sym, Symbol::Attribute(_)) {
                    return Some(vec![i]);
                }
            }
            None
        }
    }
}
pub fn goto_definition(
    root: &Snapshot,
    draft: &Draft,
    pos: &Position,
    uri: &Url,
) -> Option<GotoDefinitionResponse> {
    let refs = find_definitions(root, draft, pos, uri)?;
    Some(GotoDefinitionResponse::Array(
        refs.iter()
            .filter_map(|sym| {
                let file = root.file(sym.file);
                match sym.sym {
                    Symbol::Root => Some(Location {
                        uri: file.uri.clone(),
                        range: Range::default(),
                    }),
                    _ => {
                        let range = file.lsp_range(sym.sym)?;
                        Some(Location {
                            uri: file.uri.clone(),
                            range,
                        })
                    }
                }
            })
            .collect(),
    ))
}

fn reverse_resolve(
    root: &Snapshot,
    dst_id: FileID,
    tgt: Symbol,
) -> Vec<(RootSymbol, Option<Range>)> {
    let dst_file = root.file(dst_id);

    root.fs()
        .recursive_imported(dst_id)
        .iter()
        .flat_map(|&src_id| {
            let src_file = root.file(src_id);

            src_file
                .all_references()
                .filter(move |r| {
                    root.resolve(src_id, src_file.path(*r)).any(|sym| {
                        sym == RootSymbol {
                            file: dst_id,
                            sym: tgt,
                        } || matches!(tgt, Symbol::Feature(_))
                            && matches!(sym, RootSymbol {file, sym: Symbol::Attribute(n)}
                                if file == dst_id && dst_file.scope(Symbol::Attribute(n)) == tgt)
                    })
                })
                .map(move |sym| -> (RootSymbol, Option<Range>) {
                    fn get_range(
                        root: &Snapshot,
                        sym: Symbol,
                        src_file: &AstDocument,
                        dst_id: FileID,
                        tgt: Symbol,
                    ) -> Option<Range> {
                        let reference = if let Symbol::Reference(n) = sym {
                            src_file.get_reference(n)?
                        } else {
                            return None;
                        };
                        for i in 0..reference.path.names.len() {
                            if root
                                .resolve(src_file.id, &reference.path.names[0..=i])
                                .any(|sym| {
                                    sym == RootSymbol {
                                        file: dst_id,
                                        sym: tgt,
                                    }
                                })
                            {
                                return lsp_range(
                                    reference.path.spans.get(i).unwrap().clone(),
                                    &src_file.source,
                                );
                            }
                        }
                        None
                    }
                    (
                        RootSymbol { file: src_id, sym },
                        get_range(root, sym, src_file, dst_id, tgt),
                    )
                })
        })
        .collect()
}

fn find_references_symboles(
    root: &Snapshot,
    draft: &Draft,
    pos: &Position,
    uri: &Url,
) -> Option<Vec<(RootSymbol, Option<Range>)>> {
    let file_id = root.file_id(uri)?;
    let file = root.file(file_id);
    let obj = find_text_object(draft, pos, file_id, root)?;
    match obj.kind {
        TextObjectKind::Feature => file
            .lookup(Symbol::Root, &obj.path.names, |sym| {
                matches!(sym, Symbol::Feature(..))
            })
            .next()
            .map(|f| reverse_resolve(root, file_id, f)),

        TextObjectKind::Attribute => file
            .lookup(Symbol::Root, &obj.path.names, |sym| {
                matches!(sym, Symbol::Feature(..) | Symbol::Attribute(..))
            })
            .next()
            .map(|a| reverse_resolve(root, file_id, a)),

        TextObjectKind::FeatureReference
        | TextObjectKind::Reference(..)
        | TextObjectKind::Aggregate(..) => find_definitions(root, draft, pos, uri).map(|defs| {
            defs.iter()
                .flat_map(|def| reverse_resolve(root, def.file, def.sym))
                .collect()
        }),
        _ => None,
    }
}

pub fn find_references(
    root: &Snapshot,
    draft: &Draft,
    pos: &Position,
    uri: &Url,
) -> Option<Vec<Location>> {
    let refs = find_references_symboles(root, draft, pos, uri)?;
    Some(
        refs.iter()
            .filter_map(|(sym, range)| {
                let file = root.file(sym.file);
                match sym.sym {
                    Symbol::Root => Some(Location {
                        uri: file.uri.clone(),
                        range: Range::default(),
                    }),
                    _ => Some(Location {
                        uri: file.uri.clone(),
                        range: range.unwrap_or(file.lsp_range(sym.sym).unwrap_or_default()),
                    }),
                }
            })
            .collect(),
    )
}

pub fn rename(
    root: &Snapshot,
    draft: &Draft,
    uri: &Url,
    pos: &Position,
    new_text: String,
) -> Option<WorkspaceEdit> {
    let mut changes = std::collections::HashMap::<Url, Vec<TextEdit>>::new();

    // Add definition changes
    let binding = find_definitions(root, draft, pos, uri)?;
    let RootSymbol { file, sym } = binding.iter().next()?;
    changes.insert(
        file.url(),
        vec![TextEdit {
            range: root.file(*file).lsp_range(*sym)?,
            new_text: new_text.clone(),
        }],
    );

    // Add reference changes
    find_references(root, draft, pos, uri)?
        .iter()
        .for_each(|location| {
            let edit = TextEdit {
                range: location.range,
                new_text: new_text.clone(),
            };
            if let Some(edits) = changes.get_mut(&location.uri) {
                edits.push(edit);
            } else {
                changes.insert(location.uri.clone(), vec![edit]);
            }
        });

    Some(WorkspaceEdit {
        changes: Some(changes),
        document_changes: None,
        change_annotations: None,
    })
}
