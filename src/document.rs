use crate::{ast, check};
use crate::{parse, semantic};
use hashbrown::HashMap;
use log::info;
use std::sync::atomic::Ordering;
use std::sync::Arc;
use std::time::SystemTime;
use tokio::sync::watch;
use tokio::time::Instant;
use tokio::{select, spawn};
use tower_lsp::lsp_types::*;
use tree_sitter::{InputEdit, Tree};
use ustr::Ustr;

use ropey::Rope;
//update the document text using text deltas form the editor
pub fn update_text(
    source: &mut Rope,
    tree: &mut Tree,
    changes: DidChangeTextDocumentParams,
) -> bool {
    let mut whole_file = false;
    for e in changes.content_changes.iter() {
        if let Some(range) = e.range {
            info!("apply change");
            let start_line = range.start.line as usize;
            let end_line = range.end.line as usize;

            let start_col = range.start.character as usize;
            let end_col = range.end.character as usize;

            let start_col8 = source.line(start_line).utf16_cu_to_char(start_col);
            let end_col8 = if end_line < source.len_lines() {
                source.line(end_line).utf16_cu_to_char(end_col)
            } else {
                0
            };

            let start_char = source.line_to_char(start_line) + start_col8;
            let end_char = if end_line < source.len_lines() {
                source.line_to_char(end_line) + end_col8
            } else {
                source.len_chars()
            };

            let start_byte = source.char_to_byte(start_char);
            let end_byte = source.char_to_byte(end_char);
            let start_col_byte = start_byte - source.line_to_byte(start_line);
            let end_col_byte = end_byte - source.line_to_byte(end_line);
            source.remove(start_char..end_char);
            source.insert(start_char, &e.text);
            let new_end_line = source.byte_to_line(start_byte + e.text.len());
            let new_end_col_byte = (start_byte + e.text.len()) - source.line_to_byte(new_end_line);
            tree.edit(&InputEdit {
                start_byte,
                old_end_byte: end_byte,
                new_end_byte: start_byte + e.text.len(),
                start_position: tree_sitter::Point {
                    row: start_line,
                    column: start_col_byte,
                },
                old_end_position: tree_sitter::Point {
                    row: end_line,
                    column: end_col_byte,
                },
                new_end_position: tree_sitter::Point {
                    row: new_end_line,
                    column: new_end_col_byte,
                },
            });

            info!("done change");
        } else {
            whole_file = true;
            *source = Rope::from_str(&e.text);
        }
    }
    whole_file
}
//each parsed document can be in three states, wich allows for faster proccessing when the parse
//tree is not needed
#[derive(Clone)]
pub enum Draft {
    Unavailable {
        revision: Instant,
    },
    Source {
        source: Rope,
        revision: Instant,
    },
    Tree {
        source: Rope,
        tree: Tree,
        revision: Instant,
    },
}
impl Draft {
    fn sync(&self) -> DraftSync {
        match self {
            Draft::Tree { .. } => DraftSync::Tree,
            Draft::Source { .. } => DraftSync::Source,
            Draft::Unavailable { .. } => DraftSync::Unavailable,
        }
    }
    pub fn revision(&self) -> Instant {
        match self {
            Self::Unavailable { revision }
            | Self::Tree { revision, .. }
            | Self::Source { revision, .. } => *revision,
        }
    }
}
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum DraftSync {
    Unavailable,
    Source,
    Tree,
    Final,
}

//A document can be owned by the operating system or opened in the editor
#[derive(Clone, PartialEq, Eq, Copy)]
pub enum DocumentState {
    OwnedByOs(SystemTime),
    OwnedByEditor,
}
impl DocumentState {
    pub fn can_update(&self, other: &DocumentState) -> bool {
        match (self, other) {
            (DocumentState::OwnedByOs(t1), DocumentState::OwnedByOs(t2)) => t2 > t1,
            (DocumentState::OwnedByEditor, DocumentState::OwnedByEditor) => true,
            (DocumentState::OwnedByOs(_), DocumentState::OwnedByEditor) => true,
            (DocumentState::OwnedByEditor, DocumentState::OwnedByOs(_)) => false,
        }
    }
}
//The states are proccessed asynchronously
#[derive(Clone)]
pub struct AsyncDraft {
    content: watch::Receiver<Draft>,
    pub state: DocumentState,
}

impl AsyncDraft {
    //Wait until a state is reached, or timeout
    pub async fn sync(&mut self, sync: DraftSync, deadline: tokio::time::Instant) -> Option<Draft> {
        select! {
            () = tokio::time::sleep_until(deadline) =>
                Some(self.content.borrow().clone()),
            d = Self::wait_for(&mut self.content,sync) => d
        }
    }

    pub async fn wait(&mut self, sync: DraftSync) -> Option<Draft> {
        Self::wait_for(&mut self.content, sync).await
    }
    pub async fn wait_for(draft: &mut watch::Receiver<Draft>, sync: DraftSync) -> Option<Draft> {
        loop {
            if draft.borrow_and_update().sync() >= sync {
                break;
            }
            draft.changed().await.ok()?;
        }
        Some(draft.borrow().clone())
    }
    async fn open_raw(
        tx: watch::Sender<Draft>,
        revision: Instant,
        text: String,
        state: DocumentState,
        uri: Url,
        semantic: Arc<semantic::Context>,
    ) {
        let _ = if state != DocumentState::OwnedByEditor {
            Some(semantic.load_files_sema.acquire().await.unwrap())
        } else {
            None
        };
        let t = Instant::now();
        let source = Rope::from_str(&text);
        let _ = tx.send(Draft::Source {
            revision,
            source: source.clone(),
        });
        parse_document(semantic, revision, uri, tx, source, None).await;
        info!("opened in {:?}", t.elapsed());
    }
    pub fn open(
        text: String,
        state: DocumentState,
        uri: Url,
        semantic: Arc<semantic::Context>,
    ) -> Self {
        let revision = Instant::now();
        let (tx, rx) = watch::channel(Draft::Unavailable { revision });
        semantic.revison_counter.fetch_add(1, Ordering::SeqCst);
        spawn(Self::open_raw(tx, revision, text, state, uri, semantic));

        Self { state, content: rx }
    }
    pub fn update(
        &mut self,
        params: DidChangeTextDocumentParams,
        semantic: Arc<semantic::Context>,
    ) {
        let revision = Instant::now();
        let (tx, rx) = watch::channel(Draft::Unavailable { revision });
        let mut old_rx = std::mem::replace(&mut self.content, rx);
        let uri = params.text_document.uri.clone();
        semantic.revison_counter.fetch_add(1, Ordering::SeqCst);
        spawn(async move {
            let t = Instant::now();

            let old = Self::wait_for(&mut old_rx, DraftSync::Tree).await; //Wait for the old document
            info!("waiting {:?} for reparse", t.elapsed());
            let (mut source, mut old_tree) = match old.unwrap() {
                Draft::Tree { source, tree, .. } => (source, tree),
                _ => {
                    panic!("internal error");
                }
            };
            let parse_whole = update_text(&mut source, &mut old_tree, params);
            let _ = tx.send(Draft::Source {
                revision,
                source: source.clone(),
            });
            parse_document(
                semantic,
                revision,
                uri,
                tx,
                source,
                if parse_whole { None } else { Some(old_tree) },
            )
            .await;
            info!("Updated  in {:?}", t.elapsed());
        });
    }
}
#[derive(Default)]
pub struct DocumentStore {
    pub ast: im::HashMap<Ustr, ast::Document>,
    revision: HashMap<Ustr, Instant>,
}
impl DocumentStore {
    fn update(&mut self, doc: ast::Document) {
        if self
            .revision
            .get(&doc.name)
            .map(|old| old > &doc.timestamp)
            .unwrap_or(false)
        {
            return;
        }
        self.ast.insert(doc.name, doc);
    }
    pub fn delete(&mut self, name: &Url, timestamp: Instant) {
        let name: Ustr = name.as_str().into();
        if self
            .revision
            .get(&name)
            .map(|old| old > &timestamp)
            .unwrap_or(false)
        {
            return;
        }
        self.ast.remove(&name);
    }
}

async fn parse_document(
    semantic: Arc<semantic::Context>,
    revision: Instant,
    uri: Url,
    draft: watch::Sender<Draft>,
    source: Rope,
    old_tree: Option<Tree>,
) {
    let tree = parse::parse(&source, old_tree.as_ref());
    let _ = draft.send(Draft::Tree {
        revision,
        tree: tree.clone(),
        source: source.clone(),
    });
    let mut doc = ast::visit_root(source.clone(), tree.clone(), uri.clone(), revision);
    doc.errors.append(&mut check::check_sanity(&tree, &source));
    doc.errors.append(&mut check::check_errors(&tree, &source));
    semantic.documents.lock().update(doc);
    semantic
        .revison_counter_parsed
        .fetch_add(1, Ordering::SeqCst);
}
