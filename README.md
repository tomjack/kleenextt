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
universe, and two hardcoded inductives — strict `Bool` and the HIT `S1`
(`base`, `loop`, eliminator computing on `hcomp`). `transp` for `Glue`
follows Cubical Agda / Huber, with `ghcomp` in the `∀i.φ` correction so no
empty systems arise; `hcomp` in the universe reduces to a `Glue` type along
`lineToEquiv`, an object-level definition in `Prelude.lean` registered with
`#kbuiltin`. Equivalences are contractible-fiber (`Equiv`, `isEquiv`,
`fiber`, `isContr` are primitives unfolding to closed templates).

Values use de Bruijn levels for both ordinary and interval variables;
semantic interval binders record their level, and interval substitution is
eager and re-runs the computation rules on neutral forms, as in cubicaltt.
Every semantic operation takes the current context size as its fresh-level
supply. Known gaps: no interval metavariables, so an interval-binding lambda
must be checked against a known type; the `Glue` eta rule is in unification
but not in the computation rules.

**Lean as the surface language**: no string parser. `Frontend.lean` declares
a `kexpr` syntax category (existing Lean tokens only) and commands — `kdef`,
`#kbuiltin`, `#knf`, `#ktype`, `#kconv`, `#kdiffer`, `#kfail` — that run our
elaborator at elaboration time, keeping checked definitions in an
environment extension. The cubical primitives are ordinary identifiers
recognised at the head of an application; systems are written
`[ (i = 0) ↦ u, (i = 1) ↦ v ]`, and binding forms as `hcomp A (λ j => […]) u`,
`transp (λ i => A) r u`, `comp (λ i => A) (λ i => […]) u`; faces are
`(i = 0)`/`(i = 1)` on variables, conjoined by juxtaposition. Object-level
programs live in ordinary Lean files: `Examples.lean` (MLTT and implicits),
`Prelude.lean` (paths, `ua`, `uaβ`, `lineToEquiv`), `Cubical.lean` (tests,
including transport around the circle through univalence).
