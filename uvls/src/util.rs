use std::{
    fmt::Display,
    sync::atomic::{AtomicU64, Ordering},
};

use crate::query::Queries;
use futures::Future;
use lazy_static::lazy_static;
use ropey::Rope;
use std::error;
use tokio::select;
use tokio_util::sync::CancellationToken;
use tower_lsp::lsp_types::{Position, Range, Url};
use tree_sitter::{Language, Node};

pub struct ParseConstants {
    pub queries: Queries,
    pub uvl: Language,
    pub json: Language,
}

impl ParseConstants {
    pub fn new() -> ParseConstants {
        let lang = tree_sitter_uvl::language();
        let queries = Queries::new(&lang);
        ParseConstants {
            queries,
            uvl: lang,
            json: tree_sitter_json::language(),
        }
    }
}

lazy_static! {
    pub static ref TS: ParseConstants = ParseConstants::new();
}

pub fn node_source(source: &Rope) -> impl tree_sitter::TextProvider<'_> {
    |node: tree_sitter::Node| {
        source
            .byte_slice(node.byte_range())
            .chunks()
            .map(|i: &str| i.as_bytes())
    }
}
pub fn node_range(node: Node, rope: &Rope) -> Range {
    lsp_range(node.byte_range(), rope).unwrap()
}
//Treesitter is using bytes as offsets while lsp uses utf16 codepoints for some insane reason
//So we have to convert
pub fn lsp_position(byte: usize, source: &Rope) -> Option<Position> {
    if byte == source.len_bytes() {
        Some(Position {
            line: (source.len_lines() - 1) as u32,
            character: source.line(source.len_lines() - 1).len_utf16_cu() as u32,
        })
    } else if byte > source.len_bytes() {
        None
    } else {
        let line = source.byte_to_line(byte);
        let col = source.byte_to_char(byte) - source.line_to_char(line);
        let col16 = source.line(line).char_to_utf16_cu(col);
        Some(Position {
            line: line as u32,
            character: col16 as u32,
        })
    }
}
pub fn lsp_range(span: std::ops::Range<usize>, source: &Rope) -> Option<Range> {
    lsp_position(span.start, source)
        .and_then(|start| lsp_position(span.end, source).map(|end| Range { start, end }))
}
pub fn char_offset(pos: &Position, source: &Rope) -> usize {
    if let Some(line) = source.get_line(pos.line as usize) {
        if let Ok(end) = line.try_utf16_cu_to_char(pos.character as usize) {
            source.line_to_char(pos.line as usize) + end
        } else {
            source.line_to_char(pos.line as usize) + line.len_chars()
        }
    } else {
        source.len_chars()
    }
}
pub fn byte_offset(pos: &Position, source: &Rope) -> usize {
    source.char_to_byte(char_offset(pos, source))
}

pub fn containing_blk(mut node: Node) -> Option<Node> {
    node = node.parent()?;
    while node.kind() != "blk" {
        node = node.parent()?
    }
    Some(node)
}
pub fn header_kind(node: Node) -> &str {
    node.child_by_field_name("header").unwrap().kind()
}

pub type Result<T> = std::result::Result<T, Box<dyn error::Error + Send + Sync>>;
fn shutdown_error() -> tower_lsp::jsonrpc::Error {
    tower_lsp::jsonrpc::Error {
        code: tower_lsp::jsonrpc::ErrorCode::InternalError,
        message: "".into(),
        data: None,
    }
}

#[derive(Debug)]
struct CancelledError {}
impl Display for CancelledError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "cancelled")
    }
}
impl error::Error for CancelledError {}

pub async fn maybe_cancel<'a, F: Future + 'a>(
    token: &CancellationToken,
    f: F,
) -> Result<F::Output> {
    let token = token.clone();
    select! {
        _ = token.cancelled() => Err(CancelledError{})?,
        out = f => Ok(out)
    }
}

pub async fn retry<'a, T, R, F>(f: F) -> Result<T>
where
    F: Fn() -> R,
    R: Future<Output = Result<T>> + 'a,
{
    loop {
        match f().await {
            Ok(v) => return Ok(v),
            Err(e) => {
                if e.downcast_ref::<CancelledError>().is_none() {
                    return Err(e);
                }
            }
        }
        tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    }
}
pub struct AtomicSemaphorePermit<'a> {
    owner: &'a AtomicSemaphore,
}
pub struct AtomicSemaphore {
    counter: AtomicU64,
}
impl AtomicSemaphore {
    pub fn new() -> Self {
        AtomicSemaphore {
            counter: AtomicU64::new(0),
        }
    }
    pub fn take(&self) -> AtomicSemaphorePermit<'_> {
        self.counter.fetch_add(1, Ordering::SeqCst);
        AtomicSemaphorePermit { owner: self }
    }
    pub fn zero(&self) -> bool {
        self.counter.load(Ordering::SeqCst) == 0
    }
}
impl<'a> Drop for AtomicSemaphorePermit<'a> {
    fn drop(&mut self) {
        self.owner.counter.fetch_sub(1, Ordering::SeqCst);
    }
}
pub fn is_config(uri: &Url) -> bool {
    uri.to_file_path()
        .map(|fp| {
            fp.extension()
                .map(|ext| ext.to_str().unwrap() == "json")
                .unwrap_or(false)
        })
        .unwrap_or(false)
}

pub fn is_uvl(uri: &Url) -> bool {
    uri.to_file_path()
        .map(|fp| {
            fp.extension()
                .map(|ext| ext.to_str().unwrap() == "uvl")
                .unwrap_or(false)
        })
        .unwrap_or(false)
}