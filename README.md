# kleenextt

An experimental implementation of "Kleene CCHM": the cubical type theory of
Cohen, Coquand, Huber and Mörtberg (arXiv:1611.02108) with the interval the
free Kleene algebra rather than the free De Morgan algebra, per the remark
in §2. Design notes in NOTES.md, literature in REFERENCES.md.

`lake build` checks everything in the default target; `#kconv`, `#kdiffer`
and `#kfail` fail the build when they fail. The library is precompiled, so
the evaluator runs natively; `lean` by hand needs the `--load-dynlib` flags
`lake build` passes. `#ktime` reports timings and the counters of
`Core/Stats.lean`; `#ktrace`, `#khead`, `#kstable` and `#koverlaps` are
diagnostics. Outside the default build: `Examples/Bench*`, `Hope`, `Pi4S3`.

`Core/` is the type theory (interval, syntax, evaluation, unification,
elaboration, the `defun` closure deriver); `Frontend.lean` embeds it in
Lean as the `kexpr` syntax category and the `kdef`/`kdata`/`#k…` commands;
`Examples/` holds object-level programs, `ElabZoo` and `Prelude` first.
