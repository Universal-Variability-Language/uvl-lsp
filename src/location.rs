use crate::ast::*;
use crate::completion::find_section;
use crate::completion::Section;
use crate::parse::*;
use crate::semantic::*;
use crate::util::*;
use log::info;
use ropey::Rope;
use tower_lsp::lsp_types::*;
use tree_sitter::{Node, Tree};

pub enum TextObjectKind {
    FeatureName,
    AttributeName,
    ImportPath,
    ImportAlias,
    FeaturePath,
    FeaturePathOutOfTree,
    AttributePath,
    Aggregate(Path),
    LanguageLevelPath,
    NamespaceName,
    Group,
    Cardinality,
}
pub struct TextObject<'a> {
    path: Path,
    prefix: usize,
    kind: TextObjectKind,
    node: Node<'a>,
}

impl<'a> TextObject<'a> {
    fn new_path(
        node: Node<'a>,
        start: usize,
        source: &Rope,
        kind: TextObjectKind,
    ) -> TextObject<'a> {
        let path = parse_path(node, source)
            .or_else(|| parse_lang_lvl_path(node, source))
            .unwrap();
        let prefix = path
            .spans
            .iter()
            .take_while(|s| s.start < start)
            .count()
            .saturating_sub(1);
        TextObject {
            node,
            path,
            prefix,
            kind,
        }
    }
}
fn estimate_expr(node: Node, start: usize, source: &Rope) -> TextObjectKind {
    if node.is_error() && node.start_position().row == node.end_position().row {
        let err_raw: String = source.byte_slice(node.byte_range()).into();
        if err_raw.contains("=>")
            || err_raw.contains("<=>")
            || err_raw.contains("&")
            || err_raw.contains("|")
        {
            return TextObjectKind::FeaturePath;
        }
        if err_raw.contains("+")
            || err_raw.contains("-")
            || err_raw.contains("*")
            || err_raw.contains("/")
            || err_raw.contains(">")
            || err_raw.contains("<")
            || err_raw.contains("==")
        {
            return TextObjectKind::AttributePath;
        }
    }
    match node.kind() {
        "aggregate" => {
            let mut cursor = node.walk();
            cursor.goto_first_child();
            let mut args = Vec::new();
            let mut args_range = Vec::new();
            loop {
                if cursor.field_name().map(|i| i == "arg").unwrap_or(false) {
                    args.push(parse_path(cursor.node(), source));
                    args_range.push(cursor.node());
                }
                info!("{:?}", cursor.node().kind());
                if !cursor.goto_next_sibling() {
                    break;
                }
            }
            let arg_offset = args_range
                .iter()
                .take_while(|p| p.start_byte() < start)
                .count()
                .saturating_sub(1);
            info!("args {:?} offset {}", &args, arg_offset);
            if arg_offset == 0 && args.len() > 1 {
                TextObjectKind::FeaturePath
            } else if args.len() == 1 && arg_offset == 0 {
                TextObjectKind::Aggregate(Path::default())
            } else if arg_offset >= 1 {
                TextObjectKind::Aggregate(args[0].clone().unwrap_or(Path::default()))
            } else {
                TextObjectKind::Aggregate(Path::default())
            }
        }
        "binary_expr" => {
            let op: String = source
                .byte_slice(node.child_by_field_name("op").unwrap().byte_range())
                .into();
            match op.as_str() {
                "=>" | "&" | "|" | "<=>" => return TextObjectKind::FeaturePath,
                _ => TextObjectKind::FeaturePath,
            }
        }
        "nested_expr" | "path" => estimate_expr(node.parent().unwrap(), start, source),
        _ => TextObjectKind::FeaturePath,
    }
}

fn find_textobject<'a>(pos: &Position, tree: &'a Tree, source: &Rope) -> Option<TextObject<'a>> {
    let pos_char = source.line_to_char(pos.line as usize)
        + source
            .line(pos.line as usize)
            .utf16_cu_to_char(pos.character as usize);
    let start = source.char_to_byte(pos_char);
    let end = source.char_to_byte(pos_char + 1);
    let node = tree
        .root_node()
        .named_descendant_for_byte_range(start, end)?;
    let object = match node.kind() {
        "name" | "minor_lvl" | "major_lvl" => match node.parent().unwrap().kind() {
            "path" | "lang_lvl" => node.parent().unwrap(),
            _ => node,
        },
        _ => node,
    };
    let section = find_section(object);
    match (object.kind(), section) {
        ("path", Section::Imports) => Some(TextObject::new_path(
            object,
            start,
            source,
            TextObjectKind::ImportPath,
        )),
        ("name", Section::Imports) => {
            if object.parent().unwrap().kind() == "ref" {
                Some(TextObject::new_path(
                    object,
                    start,
                    source,
                    TextObjectKind::ImportAlias,
                ))
            } else {
                Some(TextObject::new_path(
                    object,
                    start,
                    source,
                    TextObjectKind::ImportPath,
                ))
            }
        }
        ("path" | "name", Section::Include) => Some(TextObject::new_path(
            object,
            start,
            source,
            TextObjectKind::LanguageLevelPath,
        )),
        ("path", _) if object.parent().unwrap().kind() == "namespace" => Some(
            TextObject::new_path(object, start, source, TextObjectKind::NamespaceName),
        ),
        ("name", Section::Features) if object.parent().unwrap().kind() == "blk" => Some(
            TextObject::new_path(object, start, source, TextObjectKind::FeatureName),
        ),
        ("path", Section::Features) if object.parent().unwrap().kind() == "ref" => Some(
            TextObject::new_path(object, start, source, TextObjectKind::FeaturePathOutOfTree),
        ),
        ("path", Section::Constraints) => Some(TextObject::new_path(
            object,
            start,
            source,
            estimate_expr(object, start, source),
        )),
        (_, _) => None,
    }
}

pub fn find_definitions(root: &RootGraph, pos: &Position, uri: &Url) -> Option<Vec<RootSymbol>> {
    let file = root.files.get(&uri.as_str().into())?;
    let offset = byte_offset(pos, &file.source);
    info!("offset {}", offset);
    let sym = file.find(offset)?;
    info!("sym {:?}", sym);
    match sym {
        Symbol::Feature(..) | Symbol::Attribute(..) => Some(vec![RootSymbol {
            sym,
            file: file.name,
        }]),
        Symbol::Import(..) => {
            for i in root.resolve(file.name, file.import_prefix(sym)) {
                if matches!(i.sym, Symbol::Root) {
                    return Some(vec![i]);
                }
            }
            None
        }
        Symbol::Reference(id) => {
            let r = &file.references()[id as usize];
            let segment = r.path.segment(offset);
            for bind in root.resolve_with_binding(file.name, &r.path.names) {
                let tgt = bind.last().unwrap();
                let dst_file = &root.files[&bind.last().unwrap().file];
                if dst_file
                    .type_of(tgt.sym)
                    .map(|ty| ty == r.ty)
                    .unwrap_or(false)
                {
                    return Some(vec![bind[segment].clone()]);
                }
            }
            None
        }
        _ => None,
    }
}
pub fn goto_definition(
    root: &RootGraph,
    pos: &Position,
    uri: &Url,
) -> Option<GotoDefinitionResponse> {
    let refs = find_definitions(&root, &pos, uri)?;
    Some(GotoDefinitionResponse::Array(
        refs.iter()
            .filter_map(|sym| {
                let file = &root.files[&sym.file];
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
pub fn find_references(root: &RootGraph, pos: &Position, uri: &Url) -> Option<Vec<RootSymbol>> {
    let file = root.files.get(&uri.as_str().into())?;
    let offset = byte_offset(pos, &file.source);
    info!("offset {}", offset);
    let _sym = file.find(offset)?;
    None
}
