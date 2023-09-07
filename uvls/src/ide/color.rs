use crate::core::*;
use crate::ide::completion::find_section;
use log::info;
use ropey::Rope;
use std::collections::HashSet;
use tokio::time::Instant;
use tower_lsp::lsp_types::*;
use tree_sitter::{Node, QueryCursor, Tree};
use ustr::Ustr;
//Syntax highlight happens in here
//we mainly use tree-sitter queries to extract token and serialize them
//according to the lsp spec
//TODO make use of incremental parsing and updates
//this is fast enough for medium sized files but sinks at huge files

#[derive(Clone, Debug, PartialEq, Eq)]
struct AbsToken {
    range: Range,
    kind: u32,
}
struct FileState {
    state: Vec<SemanticToken>,
}
pub fn token_types() -> Vec<SemanticTokenType> {
    vec![
        SemanticTokenType::KEYWORD,
        SemanticTokenType::OPERATOR,
        SemanticTokenType::NAMESPACE,
        SemanticTokenType::ENUM_MEMBER,
        SemanticTokenType::CLASS,
        SemanticTokenType::COMMENT,
        SemanticTokenType::ENUM,
        SemanticTokenType::INTERFACE,
        SemanticTokenType::FUNCTION,
        SemanticTokenType::MACRO,
        SemanticTokenType::PARAMETER,
        SemanticTokenType::NUMBER,
        SemanticTokenType::STRING,
    ]
}
pub fn modifiers() -> Vec<SemanticTokenModifier> {
    vec![
        SemanticTokenModifier::DEPRECATED,
        SemanticTokenModifier::READONLY,
        SemanticTokenModifier::MODIFICATION,
        SemanticTokenModifier::ASYNC,
        SemanticTokenModifier::STATIC,
        SemanticTokenModifier::ABSTRACT,
        SemanticTokenModifier::ASYNC,
    ]
}
fn token_index(name: &str) -> u32 {
    match name {
        "keyword" => 0,
        "operator" => 1,
        "namespace" => 2,
        "enumMember" => 3,
        "class" => 4,
        "comment" => 5,
        "enum" => 6,
        "interface" => 7,
        "function" => 8,
        "macro" => 9,
        "parameter" => 10,
        "number" => 11,
        "string" => 12,
        _ => 0,
    }
}
fn modifier_bitset(name: &str) -> u32 {
    match name {
        "deprecated" => 0b1,
        "readonly" => 0b10,
        _ => 0,
    }
}

pub enum ColorUpdate {
    File(Tree),
    Root(RootGraph),
}
fn fast_lsp_range(
    node: Node,
    source: &Rope,
    utf16_lines: &HashSet<usize>,
) -> tower_lsp::lsp_types::Range {
    if utf16_lines.contains(&node.start_position().row)
        || utf16_lines.contains(&node.end_position().row)
    {
        node_range(node, source)
    } else {
        tower_lsp::lsp_types::Range {
            start: Position {
                line: node.start_position().row as u32,
                character: node.start_position().column as u32,
            },
            end: Position {
                line: node.end_position().row as u32,
                character: node.end_position().column as u32,
            },
        }
    }
}

impl FileState {
    //calculate the diffrence of two states using a crude single change or all diff algorithm
    fn diff(&self, new: &FileState) -> SemanticTokensFullDeltaResult {
        //TODO use a proper diffing algorithm
        let prefix = self
            .state
            .iter()
            .zip(new.state.iter())
            .take_while(|(i, j)| i == j)
            .count();
        let diff = self.state.len().abs_diff(new.state.len());
        if self.state.len() < new.state.len() {
            if self.state[prefix..]
                .iter()
                .zip(new.state[prefix + diff..].iter())
                .all(|(i, k)| i == k)
            {
                return SemanticTokensFullDeltaResult::TokensDelta(SemanticTokensDelta {
                    result_id: None,
                    edits: vec![SemanticTokensEdit {
                        start: prefix as u32,
                        delete_count: 0,
                        data: Some(new.state[prefix..prefix + diff].to_vec()),
                    }],
                });
            }
        } else if self.state.len() > new.state.len()
            && self.state[prefix + diff..]
                .iter()
                .zip(new.state[prefix..].iter())
                .all(|(i, k)| i == k)
        {
            return SemanticTokensFullDeltaResult::TokensDelta(SemanticTokensDelta {
                result_id: None,
                edits: vec![SemanticTokensEdit {
                    start: prefix as u32,
                    delete_count: diff as u32,
                    data: None,
                }],
            });
        }
        SemanticTokensFullDeltaResult::TokensDelta(SemanticTokensDelta {
            result_id: None,
            edits: vec![SemanticTokensEdit {
                start: prefix as u32,
                delete_count: (self.state.len() - prefix) as u32,
                data: Some(new.state[prefix..].to_vec()),
            }],
        })
    }
    fn color_section(
        origin: Node,
        root: &Snapshot,
        source: &Rope,
        file: &AstDocument,
        utf16_line: &HashSet<usize>,
        token: &mut Vec<AbsToken>,
    ) {
        let _section = find_section(origin);
        let mut cursor = QueryCursor::new();

        let captures = TS.queries.highlight.capture_names();
        for i in cursor.matches(&TS.queries.highlight, origin, node_source(source)) {
            for c in i.captures {
                let path = Self::create_path(c.node, source);
                if c.node.kind() == "path"
                    && path != None
                    && Self::handle_path(root, file, path.unwrap().clone())
                {
                    //document slice gets two colors
                    let kind = captures[7].as_str();
                    let range = node_range(c.node.child(c.node.child_count() - 1).unwrap(), source);
                    token.push(AbsToken {
                        range,
                        kind: token_index(kind),
                    });
                    let feat_kind = captures[c.index as usize].as_str();
                    let mut feat_range = fast_lsp_range(c.node, source, utf16_line);
                    feat_range.end = Position {
                        line: range.start.line,
                        character: range.start.character - 1,
                    };
                    token.push(AbsToken {
                        range: feat_range,
                        kind: token_index(feat_kind),
                    });
                } else {
                    let kind = captures[c.index as usize].as_str();
                    let range = fast_lsp_range(c.node, source, utf16_line);
                    token.push(AbsToken {
                        range,
                        kind: token_index(kind),
                    });
                }
            }
        }
    }
    /**
     * if node is a path create a Path
     */
    fn create_path(node: Node, source: &Rope) -> Option<Path> {
        if node.kind() != "path" {
            return None;
        }
        let mut path = Path::default();
        for i in 0..node.child_count() {
            if let Some(child) = node.child(i) {
                if child.kind() == "name" {
                    if let Some(name) = source.byte_slice(child.byte_range()).as_str() {
                        path.names.push(Ustr::from(name));
                        path.spans.push(child.byte_range());
                    } else {
                        return None;
                    }
                }
            } else {
                return None;
            }
        }
        Some(path)
    }
    /**
     * if it is a attribute path return true
     * otherwise false
     */
    fn handle_path(root: &Snapshot, file: &AstDocument, mut path: Path) -> bool {
        if path.len() == 0 {
            return false;
        } else if path.len() == 1 {
            if file.containe_attribute(path.names.get(0).unwrap().clone()) {
                return true;
            }
        } else if path.len() == 2 {
            // check if path prefix is a feature if not it couldn't be a attribute path
            if file.containe_feature(path.names.remove(0).clone()) {
                let _ = path.spans.remove(0);
                return Self::handle_path(root, file, path);
            }
            return false;
        } else {
            //check if path start with an import or and import alias
            for import in file.imports() {
                //check import alias
                if let Some(alias) = import.clone().alias {
                    if path.names.get(0).unwrap().clone() == alias.name {
                        let _ = path.spans.remove(0);
                        let _ = path.names.remove(0);
                        if let Some(url) =
                            create_new_uvl(file.uri.to_string(), import.path.relative_path())
                        {
                            if let Some(child_ast) = root.file_by_uri(&url) {
                                return Self::handle_path(root, child_ast, path);
                            }
                        }
                        return false;
                    }
                } else {
                    //check normal import
                    let mut same = true;
                    for i in 0..import.path.len() {
                        if let Some(name) = path.names.get(i) {
                            if name != import.path.names.get(i).unwrap() {
                                same = false;
                            }
                        } else {
                            same = false;
                        }
                    }
                    if same {
                        for _ in 0..import.path.len() {
                            let _ = path.spans.remove(0);
                            let _ = path.names.remove(0);
                        }
                        if let Some(url) =
                            create_new_uvl(file.uri.to_string(), import.path.relative_path())
                        {
                            info!("{}", url);
                            if let Some(child_ast) = root.file_by_uri(&url) {
                                return Self::handle_path(root, child_ast, path);
                            }
                        }
                        return false;
                    }
                }
            }
        }
        return false;
    }
    fn new(origin: &Url, tree: Tree, source: &ropey::Rope, root: &Snapshot) -> Self {
        let mut token = vec![];

        let time = Instant::now();
        //Keep track of bad utf16 lines, only perform byte->utf8->utf16 transformation when needed
        //61ms->34ms performance improvment for pure ascii!
        //TODO make a better uniform byte->utf16 provider as ropey is to slow
        //or just use more threads
        let mut utf16_line = HashSet::new();
        for (i, line) in source.lines().enumerate() {
            for c in line.chars() {
                if c.len_utf8() != c.len_utf16() {
                    utf16_line.insert(i);
                }
            }
        }
        let mut sections = tree.walk();
        let file = root.file_by_uri(origin).unwrap();
        //iterate captures and create colors token, we currently allow diffrent color for diffrent
        //sections (currently unsed)
        sections.goto_first_child();
        loop {
            Self::color_section(sections.node(), root, source, file, &utf16_line, &mut token);
            if !sections.goto_next_sibling() {
                break;
            }
        }
        token.sort_by_key(|a| (a.range.start.line, a.range.start.character));
        token.dedup();
        let mut filtered = Vec::new();
        let mut last: Option<AbsToken> = None;
        //translate to relative lsp tokens
        for i in token.iter() {
            if let Some(last) = last.as_ref() {
                if last.range.end.line > i.range.start.line {
                    continue;
                }
                if last.range.end.line == i.range.start.line
                    && last.range.end.character > i.range.start.character
                {
                    continue;
                }
            }
            if i.range.start.line == i.range.end.line {
                let next_col = i.range.start.character;
                let next_line = i.range.start.line;
                let len = i.range.end.character - i.range.start.character;
                if let Some(last) = last.as_ref() {
                    let last_line = last.range.end.line;
                    let last_col = last.range.start.character;
                    filtered.push(SemanticToken {
                        delta_line: next_line - last_line,
                        delta_start: if next_line == last_line {
                            next_col - last_col
                        } else {
                            next_col
                        },
                        length: len,
                        token_type: i.kind,
                        token_modifiers_bitset: 0,
                    })
                } else {
                    filtered.push(SemanticToken {
                        delta_line: next_line,
                        delta_start: next_col,
                        length: len,
                        token_type: i.kind,
                        token_modifiers_bitset: 0,
                    })
                }
            } else {
                let next_col = i.range.start.character;
                let next_line = i.range.start.line;
                if let Some(last) = last.as_ref() {
                    let last_line = last.range.end.line;
                    let last_col = last.range.start.character;
                    filtered.push(SemanticToken {
                        delta_line: next_line - last_line,
                        delta_start: if next_line == last_line {
                            next_col - last_col
                        } else {
                            next_col
                        },
                        length: source.line(i.range.start.line as usize).len_utf16_cu() as u32
                            - next_col,
                        token_type: i.kind,
                        token_modifiers_bitset: 0,
                    })
                } else {
                    filtered.push(SemanticToken {
                        delta_line: next_line,
                        delta_start: next_col,
                        length: source.line(i.range.start.line as usize).len_utf16_cu() as u32
                            - next_col,
                        token_type: i.kind,
                        token_modifiers_bitset: 0,
                    })
                }
                if i.range.end.line - i.range.start.line > 1 {
                    for l in i.range.start.line + 1..i.range.end.line {
                        filtered.push(SemanticToken {
                            delta_line: 1,
                            delta_start: 0,
                            length: source.line(l as usize).len_utf16_cu() as u32,
                            token_type: i.kind,
                            token_modifiers_bitset: 0,
                        })
                    }
                }
                filtered.push(SemanticToken {
                    delta_line: 1,
                    delta_start: 0,
                    length: i.range.end.character,
                    token_type: i.kind,
                    token_modifiers_bitset: 0,
                })
            }
            last = Some(i.clone());
        }

        info!("Semantic highlight took {:?}", time.elapsed());

        FileState { state: filtered }
    }
}
pub struct State {
    files: dashmap::DashMap<Url, FileState>,
}
impl State {
    pub fn new() -> Self {
        State {
            files: Default::default(),
        }
    }
    pub fn remove(&self, uri: &Url) {
        self.files.remove(uri);
    }
    pub fn get(&self, root: Snapshot, uri: Url, tree: Tree, source: ropey::Rope) -> SemanticTokens {
        let state = FileState::new(&uri, tree, &source, &root);
        let out = state.state.clone();
        self.files.insert(uri, state);

        SemanticTokens {
            result_id: None,
            data: out,
        }
    }
    pub fn delta(
        &self,
        root: Snapshot,
        uri: Url,
        tree: Tree,
        source: ropey::Rope,
    ) -> SemanticTokensFullDeltaResult {
        if let Some(old) = self.files.get(&uri) {
            let state = FileState::new(&uri, tree, &source, &root);
            let diff = old.diff(&state);
            self.files.insert(uri.clone(), state);
            diff
        } else {
            info!("Start color");
            let state = FileState::new(&uri, tree, &source, &root);
            let out = state.state.clone();
            self.files.insert(uri.clone(), state);

            info!("End color");
            SemanticTokensFullDeltaResult::Tokens(SemanticTokens {
                result_id: None,
                data: out,
            })
        }
    }
}
