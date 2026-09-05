# kleenextt

An experimental implementation of "Kleene CCHM": the cubical type theory of
Cohen, Coquand, Huber and Mörtberg [CCHM], with the interval the free Kleene
algebra rather than the free De Morgan algebra, as suggested in the remark
in §2 of the paper. Design notes and measurements are in NOTES.md, the
literature in REFERENCES.md.

[CCHM]: "Cubical Type Theory: a constructive interpretation of the
univalence axiom", 2016. arXiv:1611.02108

## Building and testing

`lake build` checks everything in the default target; `#kconv`, `#kdiffer`
and `#kfail` fail the build when they fail. The library is precompiled, so
the evaluator runs natively, ten times faster than in the interpreter;
running `lean` by hand needs the `--load-dynlib` flags `lake build` passes.

`#ktime e` normalises `e` and reports timings, the counters of
`Core/Stats.lean` and the start of the normal form; `#ktrace` (and
`KDEF_TRACE=1` for every `kdef`) also samples the counters and resident
size every two seconds. `#khead`, `#kstable` and `#koverlaps` are
diagnostics for a value's head, its stability under substitution, and the
system invariant of an `hcomp`.

Outside the default build: `Examples/Bench*.lean` (the ladder to the
Brunerie number), `Hope` and `BenchHope` (cctt's file towards π₄(S³)), and
`Pi4S3`.

## Layout

- `Core/Interval.lean`: interval expressions, faces, and the decision
  procedure for the free Kleene and De Morgan intervals; `Core/Tests.lean`
  pins the expected (in)equations.
- `Core/Syntax.lean`, `Core/Eval.lean`, `Core/Unify.lean`,
  `Core/Check.lean`: terms, the semantic domain and computation rules,
  pattern unification, bidirectional elaboration (after elaboration-zoo 04).
- `Core/Defun.lean`: the `defun` command deriving closures from their use
  sites; `Core/DefunTest.lean` exercises it.
- `Frontend.lean`: Lean as the surface language, a `kexpr` syntax category
  and the `kdef`/`kdata`/`#k…` commands.
- `Examples/`: object-level programs; `ElabZoo` and `Prelude` first.
