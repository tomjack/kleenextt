# Editor support

`kleenextt --server` is a language server on stdio: it checks each open
file as it changes, publishing errors and the output of `#` commands as
diagnostics, and Lean's `$/lean/fileProgress` for the part not yet
checked. Imports are read from disk and kept while unchanged. A change
takes effect at the next command boundary, so a slow definition finishes
first.

Go to definition is resolved on the syntax: a local name goes to its
binder, a global one to the latest earlier `def`, `data` or constructor
in the file as it currently reads, else to one in an import as of the
last completed check, and an `import` to its file. There is no hover.

## Emacs

[emacs/kleenextt-mode.el](./emacs/kleenextt-mode.el) builds on
[lean4-mode](https://github.com/leanprover-community/lean4-mode) for its
syntax table, `\to`-style Unicode input method and progress fringe, so
lean4-mode must be on the `load-path`:

```elisp
(add-to-list 'load-path "~/Documents/lean4-mode")
(add-to-list 'load-path "~/Documents/kleenextt/editors/emacs")
(require 'kleenextt-mode)
```

Opening a `.ktt` file starts the server through lsp-mode or eglot,
whichever is installed, using the enclosing project's
`.lake/build/bin/kleenextt` if built and otherwise
`kleenextt-executable`. `C-c C-l` runs `kleenextt check` on the file
under `compile`.

## VS Code

The repository is itself the extension: `package.json` at the root points
at [vscode/extension.js](./vscode/extension.js), which has no
dependencies and no build step. It depends on the
[Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4),
whose setup guide installs elan, and adds `kleenextt` to that extension's
`lean4.input.languages` so its Unicode input works in `.ktt` files.

The first time a `.ktt` file is opened, the extension runs `lake build`
in its own directory with elan's lake, which also downloads the pinned
Lean toolchain, then starts `.lake/build/bin/kleenextt --server`. A
workspace's own build, or the `kleenextt.executablePath` setting, takes
precedence. `kleenextt: Rebuild Server` rebuilds after pulling.

To use a checkout as the extension, link it into the extensions
directory and reload:

```sh
ln -s ~/Documents/kleenextt ~/.vscode/extensions/kleenextt
```
