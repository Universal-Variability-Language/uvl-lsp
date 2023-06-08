# UVLS - Universal Variability Language Server

UVLS is a language server for [UVL](https://github.com/Universal-Variability-Language)(Universal Variability Language).
The server is still in active development but should provide a solid editing experience.


## Features
Currently supports
- completions
- semantic syntax highlighting
- decent error messages and robust parsing using [tree-sitter](https://tree-sitter.github.io/tree-sitter/)
- Z3 based configuration 
- Inlays
- goto definitions
- configuration editor
## Configuration Editor
![alt text](https://raw.githubusercontent.com/Universal-Variability-Language/uvl-lsp/master/img/show_editor.gif)
## Requirements
On most common platforms installing this extension should just work, without any dependencies.
When the automatic install fails you will need to build the server you're self.
Build instructions can be found [here](https://codeberg.org/caradhras/uvls).
To use a custom build server specify its location via `uvls.path` or add it to `PATH`  
To use the Visualization of Feature Models please install the [Graphviz Interactive Preview Extension](https://marketplace.visualstudio.com/items?itemName=tintinweb.graphviz-interactive-preview) (tintinweb.graphviz-interactive-preview).
You may use any other Graphviz Preview Extension, but this is highly compatible with the UVLS.
## Extension Settings

* `uvls.path`: Path to the server executable eg. `uvls`t
* `uvls.auto_update`: Choose to check for updates automatically


