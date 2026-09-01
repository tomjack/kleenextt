# kleenextt

This is an experimental implementation of a "Kleene CCHM" cubical type
theory: the cubical type theory of Cohen, Coquand, Huber, and Mörtberg
[CCHM], with the interval taken to be the free Kleene algebra rather
than the free De Morgan algebra, as suggested in the remark in §2 of
the paper.

[CCHM]: "Cubical Type Theory: a constructive interpretation of the
univalence axiom", 2016. arXiv:1611.02108

## Implementation

Two layers, `lake build` checks both.

**MLTT kernel** (tiers 1/3 of NOTES.md): a port of elaboration-zoo's
02-typecheck-closures-debruijn — core terms with de Bruijn indices, NbE with
first-order closures and levels in values, beta-eta conversion, bidirectional
check/infer, type-in-type. `Syntax.lean`, `Eval.lean`, `Check.lean`.

**Lean as the surface language**: no string parser. `Frontend.lean` declares a
`kexpr` syntax category (existing Lean tokens only) and commands — `kdef`,
`#knf`, `#ktype`, `#kconv`, `#kfail` — that run our checker at elaboration
time, keeping checked definitions in an environment extension. Object-level
programs live in ordinary Lean files (`Examples.lean`) and object-level type
errors are ordinary positioned Lean errors. A standalone parser stays easy to
add if distribution without Lean ever matters.

**Interval theory** (tier 2): `Interval.lean` decides the equational theory of
the free Kleene (and free De Morgan) interval by evaluation into the finite
algebra generating the variety; `Tests.lean` pins the expected (in)equations
at compile time. Not yet connected to the kernel — cofibrations should be
driven by what `coe`/`hcom` need.
