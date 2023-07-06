use ropey::Rope;
use ustr::Ustr;

use crate::core::*;
use enumflags2::BitFlags;
use parse::parse_path;

use hashbrown::HashMap;
use log::info;
use tree_sitter::Node;

//Path resolving on file level
//imports between files allow for multiple possible meanings hence depth first serach is required
//This also containes functions for attribute aggregates and path-symbol binding and type checking
pub fn common_prefix(a: &[Ustr], b: &[Ustr]) -> usize {
    a.iter().zip(b.iter()).take_while(|(i, k)| i == k).count()
}
pub trait AstContainer {
    fn get(&self, file: FileID) -> &AstDocument;
}
impl AstContainer for AstFiles {
    fn get(&self, file: FileID) -> &AstDocument {
        &*self[&file]
    }
}

//Find all symboles from origin under path
pub fn resolve<'a>(
    files: &'a impl AstContainer,
    fs: &'a FileSystem,
    origin: FileID,
    path: &'a [Ustr],
) -> impl Iterator<Item = RootSymbol> + 'a {
    let mut stack = vec![(origin, path)];
    std::iter::from_fn(move || {
        stack.pop().map(|(file, tail)| {
            let f = files.get(file);
            for (sym, tgt) in fs.imports(file) {
                let common_prefix = common_prefix(f.import_prefix(sym), tail);
                if common_prefix == f.import_prefix(sym).len() {
                    stack.push((tgt, &tail[common_prefix..]));
                }
            }

            f.lookup(Symbol::Root, tail, |_| true)
                .map(move |sym| RootSymbol { file, sym })
        })
    })
    .flatten()
}

//Find all symboles from origin under path while keeping track of what sections path are bound to what symbol
pub fn resolve_with_bind<'a>(
    files: &'a impl AstContainer,
    fs: &'a FileSystem,
    origin: FileID,
    path: &'a [Ustr],
) -> impl Iterator<Item = Vec<(RootSymbol, usize)>> + 'a {
    let mut stack = vec![(origin, path, vec![])];
    std::iter::from_fn(move || {
        stack.pop().map(|(file, tail, binding)| {
            let src_file = files.get(file);
            for (sym, tgt) in fs.imports(file) {
                let common_prefix = common_prefix(src_file.import_prefix(sym), tail);
                if common_prefix == src_file.import_prefix(sym).len() {
                    stack.push((
                        tgt,
                        &tail[common_prefix..],
                        [
                            binding.as_slice(),
                            &[(RootSymbol { sym, file }, common_prefix)],
                        ]
                        .concat(),
                    ));
                }
            }
            src_file
                .lookup_with_binding(Symbol::Root, tail, |_| true)
                .map(move |sub_binding| {
                    let mut offset = 0;
                    binding
                        .iter()
                        .cloned()
                        .chain(
                            sub_binding
                                .iter()
                                .map(|i| (RootSymbol { file, sym: *i }, 1)),
                        )
                        .map(move |(sym, len)| {
                            offset += len;
                            (sym, offset)
                        })
                        .collect()
                })
        })
    })
    .flatten()
}

pub fn resolve_attributes<'a, F: FnMut(RootSymbol, &[Ustr])>(
    files: &'a impl AstContainer,
    fs: &'a FileSystem,
    origin: FileID,
    context: &'a [Ustr],
    mut f: F,
) {
    resolve_attributes_with_feature(files, fs, origin, context, |_, attrib, prefix, _| {
        f(attrib, prefix)
    });
}
//Find all attributes in orgin under context, allso gives the prefix for each attribut
pub fn resolve_attributes_with_feature<
    'a,
    F: FnMut(RootSymbol, RootSymbol, &[Ustr], &AstDocument),
>(
    files: &'a impl AstContainer,
    fs: &'a FileSystem,
    origin: FileID,
    context: &'a [Ustr],
    mut f: F,
) {
    for root in resolve(files, fs, origin, context) {
        let file = files.get(root.file);
        let mut owner = Some(root);
        let mut under_feature = 0;
        file.visit_named_children(root.sym, false, |i, prefix| match i {
            Symbol::Feature(..) => {
                owner = Some(RootSymbol {
                    file: root.file,
                    sym: i,
                });
                under_feature = 1;
                true
            }
            Symbol::Attribute(..) => {
                f(
                    owner.unwrap(),
                    RootSymbol {
                        sym: i,
                        file: root.file,
                    },
                    &prefix[under_feature..],
                    file,
                );
                true
            }
            _ => false,
        });
    }
}

struct TypeResolveContext<'a> {
    fs: &'a FileSystem,
    files: &'a AstFiles,
}
impl<'a> TypeResolveContext<'a> {
    pub fn file(&self, id: FileID) -> &AstDocument {
        &self.files[&id]
    }
    pub fn resolve<'d>(
        &'d self,
        origin: FileID,
        path: &'d [Ustr],
    ) -> impl Iterator<Item = RootSymbol> + 'd {
        resolve(self.files, &self.fs, origin, path)
    }
    pub fn resolve_sym<'d>(&'d self, sym: RootSymbol) -> impl Iterator<Item = RootSymbol> + 'd {
        self.resolve(sym.file, self.file(sym.file).path(sym.sym))
    }
    pub fn type_of(&self, sym: RootSymbol) -> Option<Type> {
        self.file(sym.file).type_of(sym.sym)
    }
}
#[derive(Debug)]
pub enum ResolveState {
    Unresolved,
    WrongType { expected: Type, found: Type },
    Resolved(RootSymbol),
}

//Best effort tupe resolving
pub fn resolve_file(file: FileID, fs: &FileSystem, err: &mut ErrorsAcc) -> RefMap {
    let mut ref_map = HashMap::new();
    let ctx = TypeResolveContext {
        files: err.files,
        fs,
    };
    let file_data = ctx.file(file);
    for i in file_data.constraints() {
        resolve_constraint(&ctx, file, i, err, &mut ref_map);
    }
    for i in file_data.all_imports() {
        if let Some(rs) = ctx
            .resolve(file, file_data.import_prefix(i))
            .find(|i| matches!(i.sym, Symbol::Root))
        {
            ref_map.insert(i, rs);
        }
    }
    for r in file_data.all_references() {
        if file_data.parent(r, false).is_some() {
            let mut ok = false;
            let mut found_some = false;

            for i in ctx.resolve(file, file_data.path(r)) {
                info!("found {i}");
                if matches!(i.sym, Symbol::Feature(..)) {
                    ref_map.insert(r, i);
                    ok = true;
                    break;
                } else {
                    found_some = true;
                }
            }
            if !ok {
                if found_some {
                    err.sym(r, file, 30, "expected a feature");
                } else {
                    err.sym(r, file, 30, "unresolved reference");
                }
            }
        }
    }
    ref_map
}
type RefMap = HashMap<Symbol, RootSymbol>;
fn select_type(flags: BitFlags<Type>) -> Type {
    flags.iter().next().unwrap()
}

//Since there can be multiple possible interpretations,
//two pases are used for equations.
//First pass: Gather a set of all possible types for each equation side.
//Second pass: Pick a common type and resolve each expression with the choosen type
//We could simply forbid alias import and feature names but thats boring.
fn resolve_constraint(
    ctx: &TypeResolveContext,
    file: FileID,
    constraint: &ConstraintDecl,
    err: &mut ErrorsAcc,
    ref_map: &mut RefMap,
) {
    match &constraint.content {
        Constraint::Ref(sym) => {
            let rs = RootSymbol { sym: *sym, file };
            let mut state = ResolveState::Unresolved;

            for i in ctx.resolve_sym(rs) {
                let ty = ctx.type_of(i).unwrap();
                if ty == Type::Bool {
                    state = ResolveState::Resolved(i);
                    break;
                } else {
                    state = ResolveState::WrongType {
                        expected: Type::Bool,
                        found: ty,
                    }
                }
            }
            match state {
                ResolveState::Unresolved => {
                    err.sym(*sym, file, 30, "unresolved reference");
                }
                ResolveState::WrongType { expected, found } => {
                    err.sym(
                        *sym,
                        file,
                        30,
                        format!("expected {:?} found {:?}", expected, found),
                    );
                }
                ResolveState::Resolved(tgt) => {
                    ref_map.insert(*sym, tgt);
                }
            }
        }
        Constraint::Logic { lhs, rhs, .. } => {
            stacker::maybe_grow(32 * 1024, 1024 * 1024, || {
                resolve_constraint(ctx, file, lhs, err, ref_map)
            });
            resolve_constraint(ctx, file, rhs, err, ref_map)
        }
        Constraint::Not(lhs) => {
            stacker::maybe_grow(32 * 1024, 1024 * 1024, || {
                resolve_constraint(ctx, file, lhs, err, ref_map)
            });
        }
        Constraint::Equation { op: _, lhs, rhs } => {
            let lhs_ty = gather_expr_options(ctx, file, lhs, err, ref_map);
            if lhs_ty.is_empty() {
                return;
            }

            let rhs_ty = gather_expr_options(ctx, file, rhs, err, ref_map);
            if rhs_ty.is_empty() {
                return;
            }

            if (rhs_ty & lhs_ty).is_empty() {
                err.span(
                    constraint.span.clone(),
                    file,
                    30,
                    format!(
                        "type missmatch {:?} and {:?}",
                        select_type(lhs_ty),
                        select_type(rhs_ty)
                    ),
                );
                return;
            }
            let req = Type::String | Type::Real;
            let ty = req & lhs_ty & rhs_ty;
            if !((Type::String | Type::String) & ty).is_empty()
                && !{
                    // if TYPE-level.string-constraints is not included in any way
                    let ast_document = ctx.files.get(&file).unwrap();
                    ast_document.all_lang_lvls()
                        .map(|x| ast_document.lang_lvl(x).unwrap())
                             .any(|s|
                                matches!(s, LanguageLevel::Type(x) if x.contains(&LanguageLevelType::Any))
                             || matches!(s, LanguageLevel::Type(x) if x.contains(&LanguageLevelType::StringConstraints)))
                        || {let s: Vec<Symbol> = ast_document.all_lang_lvls().collect(); s.is_empty()}
                }
            {
                err.span(
                    constraint.span.clone(),
                    file,
                    30,
                    format!("Need to include TYPE-level.string-constraints"),
                );
            }
            if ty.is_empty() {
                err.span(
                    constraint.span.clone(),
                    file,
                    30,
                    format!(
                        "unsupported operand type {:?}",
                        select_type(lhs_ty & rhs_ty),
                    ),
                );
            } else {
                commit_expr(ctx, file, lhs, select_type(ty), err, ref_map);
                commit_expr(ctx, file, rhs, select_type(ty), err, ref_map);
            }
        }

        _ => {}
    }
}
//Find possible types
fn gather_expr_options(
    ctx: &TypeResolveContext,
    file: FileID,
    expr: &ExprDecl,
    err: &mut ErrorsAcc,
    ref_map: &mut RefMap,
) -> BitFlags<Type> {
    match &expr.content {
        Expr::String(..) => Type::String.into(),
        Expr::Number(..) => Type::Real.into(),
        Expr::Aggregate { context, .. } => {
            if let Some(context) = context.clone() {
                let rs = RootSymbol { sym: context, file };
                if let Some(tgt) = ctx
                    .resolve_sym(rs)
                    .find(|i| matches!(i.sym, Symbol::Feature(_) | Symbol::Root))
                {
                    ref_map.insert(context, tgt);
                } else {
                    err.sym(
                        context,
                        file,
                        10,
                        "unresolved context expected file root or feature",
                    );
                }
            }
            Type::Real.into()
        }
        Expr::Integer { op: _, n } => {
            let n_ty = stacker::maybe_grow(32 * 1024, 1024 * 1024, || {
                gather_expr_options(ctx, file, n, err, ref_map)
            });
            if (n_ty & Type::Real).is_empty() {
                err.span(
                    expr.span.clone(),
                    file,
                    30,
                    format!("type missmatch expected Real/Number",),
                );
                Default::default()
            } else {
                Type::Real.into()
            }
        }
        Expr::Binary { rhs, lhs, op } => {
            let lhs_ty = stacker::maybe_grow(32 * 1024, 1024 * 1024, || {
                gather_expr_options(ctx, file, lhs, err, ref_map)
            });
            let rhs_ty = gather_expr_options(ctx, file, rhs, err, ref_map);
            if lhs_ty.is_empty() {
                return lhs_ty;
            }
            if rhs_ty.is_empty() {
                return rhs_ty;
            }
            if (rhs_ty & lhs_ty).is_empty() {
                err.span(
                    expr.span.clone(),
                    file,
                    30,
                    format!(
                        "type missmatch {:?} and {:?}",
                        select_type(lhs_ty),
                        select_type(rhs_ty)
                    ),
                );
                rhs_ty & lhs_ty
            } else {
                let req = match op {
                    NumericOP::Add => Type::String | Type::Real,
                    _ => Type::Real.into(),
                };
                if (rhs_ty & lhs_ty & req).is_empty() {
                    err.span(
                        expr.span.clone(),
                        file,
                        30,
                        format!("unsupported operator type {}", select_type(rhs_ty & lhs_ty),),
                    );
                }
                rhs_ty & lhs_ty & req
            }
        }
        Expr::Len(lhs) => {
            let lhs_ty = stacker::maybe_grow(32 * 1024, 1024 * 1024, || {
                gather_expr_options(ctx, file, lhs, err, ref_map)
            });
            if (lhs_ty & Type::String).is_empty() {
                err.span(
                    expr.span.clone(),
                    file,
                    30,
                    format!("type missmatch expected String",),
                );
                Default::default()
            } else {
                Type::Real.into()
            }
        }
        Expr::Ref(sym) => {
            let rs = RootSymbol { sym: *sym, file };
            let ty = ctx
                .resolve_sym(rs)
                .map(|i| ctx.type_of(i).unwrap())
                .fold(BitFlags::default(), |acc, i: Type| acc | i);
            if ty.is_empty() {
                err.sym(*sym, file, 30, "unresolved reference");
            }
            ty
        }
    }
}
//Fix types
fn commit_expr(
    ctx: &TypeResolveContext,
    file: FileID,
    expr: &ExprDecl,
    ty: Type,
    err: &mut ErrorsAcc,
    ref_map: &mut RefMap,
) {
    match &expr.content {
        Expr::Binary { rhs, lhs, .. } => {
            stacker::maybe_grow(32 * 1024, 1024 * 1024, || {
                commit_expr(ctx, file, lhs, ty, err, ref_map);
            });
            commit_expr(ctx, file, rhs, ty, err, ref_map);
        }
        Expr::Len(lhs) => {
            stacker::maybe_grow(32 * 1024, 1024 * 1024, || {
                commit_expr(ctx, file, lhs, Type::String, err, ref_map);
            });
        }
        Expr::Integer { op: _, n } => {
            stacker::maybe_grow(32 * 1024, 1024 * 1024, || {
                commit_expr(ctx, file, n, Type::Real, err, ref_map);
            });
        }
        Expr::Ref(sym) => {
            let rs = RootSymbol { sym: *sym, file };
            let tgt = ctx
                .resolve_sym(rs)
                .find(|i| ctx.type_of(*i).unwrap() == ty)
                .unwrap();
            ref_map.insert(*sym, tgt);
        }
        _ => {}
    }
}

//Best effort type resolve for a single tree-sitter expression
pub fn estimate_types(
    node: Node,
    possible: BitFlags<Type>,
    source: &Rope,
    ty_map: &mut HashMap<usize, Type>,
    file: FileID,
    root: &RootGraph,
) -> BitFlags<Type> {
    info!("{:?}, {:?}", node, possible);
    match node.kind() {
        "constraint" | "nested_expr" => estimate_types(
            node.named_child(0).unwrap(),
            possible,
            source,
            ty_map,
            file,
            root,
        ),
        "unary_expr" => estimate_types(
            node.child_by_field_name("lhs").unwrap(),
            Type::Bool.into(),
            source,
            ty_map,
            file,
            root,
        ),
        "bool" => Type::Bool.into(),
        "number" => Type::Real.into(),
        "string" => Type::String.into(),
        "path" | "name" => {
            let path = parse_path(node, source).unwrap();
            if let Some(sym) = root
                .resolve(file, &path.names)
                .find(|i| !(possible & root.type_of(*i).unwrap()).is_empty())
            {
                let ty = root.type_of(sym).unwrap();
                ty_map.insert(node.id(), ty);
            }
            root.resolve(file, &path.names)
                .map(|i| root.type_of(i).unwrap())
                .fold(Default::default(), |acc, i| acc | i)
        }
        "binary_expr" => {
            let op: std::borrow::Cow<'_, _> = source
                .slice(node.child_by_field_name("op").unwrap().byte_range())
                .into();
            let req = match &*op {
                "+" | "-" | "/" | "*" | ">" | "<" => Type::Real.into(),
                "&" | "|" | "<=>" | "=>" => Type::Bool.into(),
                _ => Type::String | Type::Real | Type::Bool,
            };
            let mut lhs = estimate_types(
                node.child_by_field_name("lhs").unwrap(),
                req,
                source,
                ty_map,
                file,
                root,
            );
            let mut rhs = estimate_types(
                node.child_by_field_name("rhs").unwrap(),
                req,
                source,
                ty_map,
                file,
                root,
            );
            if (lhs & rhs).is_empty() {
                return req;
            }
            if lhs & rhs != lhs {
                lhs = estimate_types(
                    node.child_by_field_name("lhs").unwrap(),
                    lhs & rhs,
                    source,
                    ty_map,
                    file,
                    root,
                );
            }
            if lhs & rhs != rhs {
                rhs = estimate_types(
                    node.child_by_field_name("rhs").unwrap(),
                    lhs & rhs,
                    source,
                    ty_map,
                    file,
                    root,
                );
            }
            if (lhs & rhs).is_empty() {
                return req;
            }
            lhs & rhs
        }
        "ERROR" => {
            let mut cursor = node.walk();
            cursor.goto_first_child();
            loop {
                if node.is_named() {
                    estimate_types(
                        node.child_by_field_name("arg").unwrap(),
                        possible,
                        source,
                        ty_map,
                        file,
                        root,
                    );
                }
                if !cursor.goto_next_sibling() {
                    break;
                }
            }
            possible
        }
        "function" => {
            let op: std::borrow::Cow<'_, _> = source
                .slice(node.child_by_field_name("op").unwrap().byte_range())
                .into();
            match &*op {
                "len" => estimate_types(
                    node.child_by_field_name("arg").unwrap(),
                    Type::String.into(),
                    source,
                    ty_map,
                    file,
                    root,
                ),
                "floor" | "ceil" => estimate_types(
                    node.child_by_field_name("arg").unwrap(),
                    Type::Real.into(),
                    source,
                    ty_map,
                    file,
                    root,
                ),
                _ => Type::Real.into(),
            }
        }
        _ => Type::String | Type::Real | Type::Bool,
    }
}
