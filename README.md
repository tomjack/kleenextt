# kleenextt

This is an experimental implementation of a "Kleene CCHM" cubical type
theory: the cubical type theory of Cohen, Coquand, Huber, and Mörtberg
[CCHM], with the interval taken to be the free Kleene algebra rather
than the free De Morgan algebra, as suggested in the remark in §2 of
the paper.

[CCHM]: "Cubical Type Theory: a constructive interpretation of the
univalence axiom", 2016. arXiv:1611.02108

## Implementation

`lake build` checks everything; the object-level tests are `#kconv`,
`#kdiffer` and `#kfail` commands that fail the build when they fail.
The library is precompiled (`precompileModules`), so the evaluator runs
natively rather than in Lean's interpreter, which is ten times slower;
running `lean` on a file by hand needs the `--load-dynlib` flags that
`lake build` passes.

**Measuring**: `#ktime e` normalises `e`, reporting the time of evaluation
and of quotation, the counters of `Stats.lean` (compositions, transports,
substitutions, line instantiations, …) and the start of the normal form.
`Bench.lean`, `BenchDeep.lean` and `BenchBrunerie.lean` are the ladder
towards the Brunerie number, outside the default build:
`lake build Kleenextt.Bench`. `Hope.lean` continues cctt's file towards
π₄(S³) (the Hopf construction computes; `generator` takes 9 s), and
`BenchHope.lean` holds the numbers that still run out of memory.

**Interval theory** (tier 2 of NOTES.md): `Interval.lean` decides the
equational theory of the free Kleene (and free De Morgan) interval by
evaluation into the finite algebra generating the variety; `Tests.lean` pins
the expected (in)equations at compile time. The kernel uses the Kleene
theory for conversion of interval expressions. System faces are
conjunctions of `(i = 0)`/`(i = 1)` on variables, as in cubicaltt; a
cofibration is represented by its face normal form (cubicaltt's
`invFormula`), which is the same for the Kleene and De Morgan intervals.
ABCFHL validity (`IExpr.isValid`) is available but not enforced (see
NOTES.md).

**Elaborator** (tiers 1/3): a port of elaboration-zoo's 04-implicit-args —
core terms with de Bruijn indices, NbE with first-order closures and levels
in values, metavariables solved by pattern unification, bidirectional
check/infer with Agda-style insertion of implicit arguments and lambdas
(positional and named), type-in-type. `Syntax.lean`, `Eval.lean`,
`Unify.lean`, `Check.lean`. Metavariables and builtins live in a `Globals`
record passed explicitly (a section variable) rather than in a global ref;
each top-level definition is zonked and must leave no unsolved metas. This
is the §2.6 insertion of Kovács' ICFP 2020 paper only; first-class
polymorphism (postponed insertion, zoo stage 06) is not implemented.

**Cubical layer**: CCHM-style, with `transp` and `hcomp` as the primitives
(the CHM / Cubical Agda decomposition) and `comp`, `hfill`, `ghcomp`
derived. Type formers: Pi (also over `I`), Sigma, `PathP`, `Glue`, the
universe, and user-declared parameterless inductive types and HITs
(`kdata`, with `case` as the dependent eliminator, computing on `hcomp` by
the CHM rule). `transp` for `Glue` follows Cubical Agda / Huber, with
`ghcomp` in the `∀i.φ` correction so no empty systems arise. `hcomp` in the
universe is a type former of its own (cubicaltt's `VCompU`): its elements
are `glueU`, the implicit equivalence is transport backwards along the side
line, and `lemEq` supplies the fiber contraction, so no equivalence proof
is ever built. Equivalences are contractible-fiber (`Equiv`, `isEquiv`,
`fiber`, `isContr` are primitives unfolding to closed templates).

Values use de Bruijn levels for both ordinary and interval variables.
Semantic interval binders (`line`) hold their body at a fresh variable as a
memoised thunk, and their support, computed from the captures of the
derived closure they are built from (below); instantiation substitutes
into the body, and substitution into a line is deferred. Substitution
elsewhere skips values outside their support and is otherwise deferred as
a `sub` node, as in cctt: `whnf` exposes a head by pushing the pending
substitution one layer, re-running the computation rules on a neutral head
and deferring the children, so that only what is inspected is ever
rebuilt; a substitution of a `sub` composes. Top-level definitions are
lazily evaluated constants outside the environment. The components a
rule builds for the faces of a `Glue` or a universe composition, and the
components of pairs and constructors under `transp` and `hcomp`, are
deferred computations (`lazy`, with the support of their captures), since
a total face discards all but one of them. Every semantic operation takes
the current context size as its fresh-level supply. Known gaps: no interval metavariables, so an
interval-binding lambda must be checked against a known type; the `Glue`
eta rule is in unification but not in the computation rules. The
Brunerie number of `Brunerie.lean` normalises in about 0.6 s.

**Derived closures** (`Defun.lean`, exercised on a toy domain in
`DefunTest.lean`): a `defun … in … end defun` block holds the domain and
its rules, with closures written at the use site as `closure% fun L i =>
body`. The block is elaborated twice: once against an `unsafe`
function-valued closure type to record what each site captures, then for
real, with the closure type an inductive with one constructor per site,
`apply` re-elaborating each site's lambda in its arm, and a function per
`deriving` clause mapping or folding a class method over the fields.
`Eval.lean` builds every line this way, deriving `Line.vars`, the support
of a line from its captures (see NOTES.md, "Derived closure
defunctionalization").

**Lean as the surface language**: no string parser. `Frontend.lean` declares
a `kexpr` syntax category (existing Lean tokens only) and commands — `kdef`,
`kdata`, `#knf`, `#ktype`, `#kconv`, `#kdiffer`, `#kfail` — that run our
elaborator at elaboration time, keeping checked definitions in an
environment extension. The cubical primitives are ordinary identifiers
recognised at the head of an application; systems are written
`[ (i = 0) ↦ u, (i = 1) ↦ v ]`, and binding forms as `hcomp A (λ j => […]) u`,
`transp (λ i => A) r u`, `comp (λ i => A) (λ i => […]) u`; faces are
`(i = 0)`/`(i = 1)` on variables, conjoined by juxtaposition. Object-level
programs live in ordinary Lean files: `Examples.lean` (MLTT and implicits),
`Prelude.lean` (paths, `ua`, `uaβ`, `lineToEquiv`), `Cubical.lean` (tests,
including transport around the circle through univalence).
