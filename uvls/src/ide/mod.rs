/// Handles all sorts of Code actions.
///
/// Each function handles a different kind of error. They can also be combined for more flexibility
pub mod actions;
/// Handle color highlighting for IDEs
///
/// Syntax highlight happens in here
/// we mainly use tree-sitter queries to extract token and serialize them
/// according to the lsp spec
/// TODO make use of incremental parsing and updates
/// this is fast enough for medium sized files but sinks at huge files
pub mod color;
/// Handle Completion and code suggestions for IDEs
///
/// All things completion related happen in here, the process is roughly as follows:
/// 1. Find the current context using the latest draft and editor position
/// 2. Find good completions in this context
///
/// The completion context includes:
///  - Meta information on the cursor position eg. Are we currently in a path or an empty line etc.
///  - The semantic context eg. do we need a constraint or a number
///  - A optional path prefix and suffix. The suffix is used as a weight for completions using the jaro
///    winkler distance, the prefix is a filter restricting possible completions.
///
///  To weigh completions we use a simple weight function with hand picked weights for parameters
///  like length or type correctness
///
pub mod completion;
/// Inlay hints are used to display the configuration in the source code view.
///
/// Inlays are managed as a global token state,
/// there can only be 1 inlay source to keep things simple,
/// inlays are computed asynchronously. Both configurations
/// and webview can provide them as a SMT-Model
pub mod inlays;
/// handles text jumps, like go to definition etc
pub mod location;
