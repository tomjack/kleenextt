# kleenextt

An experimental implementation of "Kleene CCHM": the cubical type theory of
Cohen, Coquand, Huber and Mörtberg (arXiv:1611.02108) with the interval the
free Kleene algebra rather than the free De Morgan algebra, per the remark
in §2. Design notes in NOTES.md, literature in REFERENCES.md.

`lake build` (or `make`) produces the self-contained executable
`.lake/build/bin/kleenextt`, which needs nothing from the toolchain at run
time:

    kleenextt check FILE...   check `.ktt` files, running their `#…` commands
    kleenextt nf FILE EXPR    normalize a name or expression in FILE's context

A `.ktt` file is `import`s, then `def`/`data` definitions and `#…`
commands. `import X` loads `X.ktt` from the same directory, transitively,
definitions only; a file's `#…` commands run only when it is checked
itself. `#conv`, `#differ` and `#fail` are errors when they fail, and any
error makes the exit status 1. `#time` reports timings and the counters of
`Core/Stats.lean`; `#trace`, `#head`, `#stable` and `#overlaps` are
diagnostics. `lake test` (or `make test`) checks the quick examples;
`make bench` checks the slow ones, `examples/BrunerieBench` and `Pi4S3`,
one process each, reporting wall time, CPU time and peak memory.

`Core/` is the type theory (interval, syntax, evaluation, unification,
elaboration, the `defun` closure deriver), with no dependency on Lean's own
library. `Syntax/` registers the `kexpr`/`kcmd`/… categories as builtin
parsers, so they live in the binary rather than in `.olean` files; the
compiler sees them too, since Lake loads the precompiled modules as plugins.
`Frontend.lean` turns the syntax into `Raw` terms, runs commands against a
`KState`, and loads files with their imports. `examples/` holds object-level
programs, `ElabZoo` and `Prelude` first.
