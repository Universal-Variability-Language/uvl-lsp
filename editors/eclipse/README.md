# UVLS (Universal Variability Language Server) in JetBrain IDEs
UVLS is a language server for [UVL](https://github.com/Universal-Variability-Language) (Universal Variability Language).

The server is still in active development but should provide a solid editing experience.

## Installation

- Add [this LSP Client](https://github.com/eclipse/lsp4e) to your Eclipse Installation.  
  The process is described [here](https://download.eclipse.org/lsp4e/releases/latest/).  
  `Help` -> `Install new software` -> Enter the provided url (`https://download.eclipse.org/lsp4e/releases/latest/`) -> Select all checkboxes and click on `Next`
- Register `.uvl` as a Content Type:  
  `Window` -> `Preferences` -> `General` -> `Content Type` -> Click `Add Root`, Enter `uvl`, Add the File association `*.uvl`, add `Text Editor` to the Associated Editors
- Download and unpack an UVLS executable [here](https://github.com/Universal-Variability-Language/uvl-lsp/releases).
- Configure the LSP for `uvl` files:
  - `Run` -> `External Tools` at the very bottom -> `External Tools Configuration` -> Right click `New Configuration` -> Enter a name like UVL-LSP, Click `Browse File System`, Select the unpacked UVL executable
  - `Window` -> `Preferences` -> `Language Servers` -> At the bottom right click `Add` -> Select `UVL` on the left and your configured LSP Program on the right, Click `Ok` -> `Apply & Close` 
- Open an `.uvl` file and the LSP should work




## Notes
This will not support Syntax Highlighting, since Eclipse does not provide a simple solution to add keywords but needs 3rd party plugins to define a Syntax which will provide the possibility to color certain keywords. We could use [this instruction](https://www.vogella.com/tutorials/EclipseEditors/article.html) to create a custom Text Editor for Eclipse.
