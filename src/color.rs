use log::info;
use std::collections::HashMap;
use std::sync::Arc;
use tokio::time::Instant;
use tower_lsp::lsp_types::*;

use crate::semantic::{Span, TS, RootGraph};
use tree_sitter::{QueryCursor, Tree};

#[derive(Clone, Debug, PartialEq, Eq)]
struct AbsToken {
    line: u32,
    col: u32,
    len: u32,
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
        "function"=>8,
        "macro"=>9,
        _ => 0,
    }
}
pub enum ColorUpdate{
    File(Tree),
    Root(RootGraph),

}

impl FileState {
    fn diff(&self, new: &FileState) -> SemanticTokensFullDeltaResult {
        //todo use a proper diffing algorithm
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
        } else if self.state.len() > new.state.len() {
            if self.state[prefix + diff..]
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
    fn new(tree: Tree, source: &ropey::Rope) -> Self {
        let time = Instant::now();
        let mut cursor = QueryCursor::new();
        let mut token = vec![AbsToken {
            len: 0,
            line: 0,
            col: 0,
            kind: 0,
        }];
        for i in cursor.matches(
            &TS.queries.highlight,
            tree.root_node(),
            crate::util::node_source(source),
        ) {
            for c in i.captures {
                let line = c.node.start_position().row as u32;
                let line_end = c.node.end_position().row as u32;
                let start = c.node.start_position().column as u32;
                let end = c.node.end_position().column as u32;
                if line != line_end && c.node.end_position().column > 0 {
                    continue;
                }
                let len = if line_end == line + 1 {
                    source.line(line as usize).len_utf16_cu() as u32 - start
                } else if line_end == line {
                    end - start
                } else {
                    continue;
                };
                let kind = TS.queries.highlight.capture_names()[c.index as usize].as_str();
                token.push(AbsToken {
                    line,
                    len,
                    col: start,
                    kind: token_index(kind),
                });
            }
        }
        token.sort_by_key(|a| (a.line, a.col, a.len));
        token.dedup();
        info!("Semantic highlight took {:?}",time.elapsed());
        FileState {
            state: token
                .windows(2)
                .map(|i| SemanticToken {
                    delta_line: i[1].line - i[0].line,
                    delta_start: if i[0].line != i[1].line {
                        i[1].col
                    } else {
                        i[1].col - i[0].col
                    },
                    length: i[1].len,
                    token_type: i[1].kind,
                    token_modifiers_bitset: 0,
                })
                .collect(),
        }
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
    pub fn get(&self, uri: Url, tree: Tree, source: ropey::Rope) -> SemanticTokens {
        let state = FileState::new(tree, &source);
        let out = state.state.clone();
        self.files.insert(uri.clone(), state);
        SemanticTokens {
            result_id: None,
            data: out,
        }
    }
    pub fn delta(
        &self,
        uri: Url,
        tree: Tree,
        source: ropey::Rope,
    ) -> SemanticTokensFullDeltaResult {

        if let Some(old) = self.files.get(&uri) {
            let state = FileState::new(tree, &source);
            let diff = old.diff(&state);
            self.files.insert(uri.clone(), state);
            diff

        } else {
            let state = FileState::new(tree, &source);
            let out = state.state.clone();
            self.files.insert(uri.clone(), state);
            SemanticTokensFullDeltaResult::Tokens(
            SemanticTokens {
                result_id: None,
                data: out,
            })
        }
    }
}
