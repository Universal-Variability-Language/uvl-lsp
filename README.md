# UVLS - Universal Variability Language Server
[UVL](https://github.com/Universal-Variability-Language) language server based on [tree-sitter](https://github.com/tree-sitter/tree-sitter).

## Getting started
### Build
- Requirements
    - Rust 1.65+
    - Git
```
git clone https://codeberg.org/caradhras/uvls.git
cd  uvls
cargo build --release
```

### VSCode
```
ext install caradhras.uvls-code
```
Make sure the server binary is in path or specify the location under `uvls.path`
### NeoVim

## Features
- Completions
- Syntax highlighting
- Error messages
## Why tree-sitter
We use tree-sitter as an initial parser to create a lose syntax tree of uvl code-fragments.
Because the tree-sitter grammar is more relaxed than the original UVL-grammar and has great error recovery,
we can capture many incorrect expression and provide decent error messages in most cases.
Tree-sitter queries allow for easy symbol extraction and are used to transform the tree-sitter tree into a more compact graph.
This graph is then used for further analysis.


