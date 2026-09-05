# kleenextt

An experimental implementation of "Kleene CCHM": the cubical type theory of
Cohen, Coquand, Huber and Mörtberg [CCHM], with the interval the free Kleene
algebra rather than the free De Morgan algebra, as suggested in the remark
in §2 of the paper. Design notes and measurements are in NOTES.md, the
literature in REFERENCES.md.

[CCHM]: "Cubical Type Theory: a constructive interpretation of the
univalence axiom", 2016. arXiv:1611.02108

## Building and testing

`lake build` checks everything in the default target. The object-level
tests are the `#kconv`, `#kdiffer` and `#kfail` commands, which fail the
build when they fail. The library is precompiled (`precompileModules`), so
the evaluator runs natively rather than in Lean's interpreter, which is ten
times slower; running `lean` on a file by hand needs the `--load-dynlib`
flags that `lake build` passes.

`#ktime e` normalises `e` and reports the time of evaluation and quotation,
the counters of `Core/Stats.lean` and the start of the normal form.
`#ktrace` also prints the counters and resident size every two seconds
(`KDEF_TRACE=1` does the same for every `kdef`). `#khead`, `#kstable` and
`#koverlaps` inspect a value's head, its stability under substitution, and
the system invariant of an `hcomp`.

Outside the default build: `lake build Kleenextt.Examples.Bench` (and
`BenchDeep`, `BenchBrunerie`) is the ladder towards the Brunerie number;
`Hope` and `BenchHope` continue cctt's file towards π₄(S³); `Pi4S3` proves
π₄(S³) nontrivial.

## Layout

- `Core/Interval.lean`: interval expressions, faces, and the decision
  procedure for the free Kleene and De Morgan intervals, by evaluation into
  the finite algebra generating the variety. `Core/Tests.lean` pins the
  expected (in)equations at compile time.
- `Core/Syntax.lean`: surface (`Raw`) and core (`Tm`) terms.
- `Core/Eval.lean`: the semantic domain and the computation rules.
- `Core/Unify.lean`, `Core/Check.lean`: pattern unification and
  bidirectional elaboration with implicit arguments, after
  elaboration-zoo 04.
- `Core/Defun.lean`: the `defun` command deriving closures from their use
  sites; `Core/DefunTest.lean` exercises it on a toy domain.
- `Core/Stats.lean`: evaluation counters.
- `Frontend.lean`: Lean as the surface language. A `kexpr` syntax category
  of existing Lean tokens and the commands `kdef`, `kdata`, `#knf`,
  `#ktype`, `#kconv`, `#kdiffer`, `#kfail`, which run the elaborator at
  Lean elaboration time and keep checked definitions in an environment
  extension. Systems are written `[ (i = 0) ↦ u, (i = 1) ↦ v ]`, binding
  forms `hcomp A (λ j => […]) u`, `transp (λ i => A) r u`,
  `comp (λ i => A) (λ i => […]) u`; faces are `(i = 0)`/`(i = 1)` on
  variables, conjoined by juxtaposition.
- `Examples/`: object-level programs. `ElabZoo` (MLTT and implicits),
  `Prelude` (paths, `ua`, `lineToEquiv`), `Cubical` (tests), `Brunerie`,
  `HLevel` (`hlevel`), `S1Mod2`, `Tubes`, `LocalGlobal`, `S2Mod2`, `J2S2`
  (the cheat-free `bit`), `Pi4S3`.
