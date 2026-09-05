# Kleene CCHM — working notes

Goal: a simple but usable implementation of CCHM cubical type theory with a
Kleene algebra on the interval (a De Morgan algebra satisfying
`r ∧ ¬r ≤ s ∨ ¬s`) in place of the free De Morgan algebra of Cubical Agda
and cubicaltt. Cubical Agda has the surface language but long-standing
canonicity bugs; cubicaltt is small enough to trust (`pi4s3_nobug`, among
the `pi4s3*` branches of mortberg/cubicaltt, behaves best) but has no
implicit arguments. The target is cctt with the Kleene interval: a small
CCHM-style kernel plus an elaborator with implicit arguments in the
smalltt/elaboration-zoo style.

## Known gaps

- No interval metavariables, so an interval-binding lambda must be checked
  against a known type.
- The `Glue` eta rule is in unification but not in the computation rules.
- Implicit insertion is §2.6 of Kovács' ICFP 2020 paper only; first-class
  polymorphism (postponed insertion, elaboration-zoo stage 06) is not
  implemented.

## Open: the validity constraint

`ghcomp` is Mörtberg's `hcomp [φ ↦ u, ¬φ ↦ u₀] u₀`, with `¬φ` computed on
the face normal form; Angiuli's structural definition (cctt's `ghcomdn`)
needs no negation and could replace it (REFERENCES.md, "Empty systems").
Enforcing ABCFHL validity on user `hcomp`s would rule out empty systems but
reject `hcomp [ (i=0) ↦ u ] u₀`, which would have to be a `ghcomp`. Current
choice, as in Cubical Agda: enforce nothing and use `ghcomp` internally
where a `∀i.φ` face can vanish (`transp` for `Glue`); `IExpr.isValid` exists
but is not wired in. Revisit when there is enough code to measure the effect
on normal forms.

## Open: declarative rules → implementation

Tiers, easiest first: syntax and binding from a datatype declaration; the
interval theory and cofibration logic, decidable and the part that differs
from stock CCHM, so keeping it declarative and swappable is the strongest
argument for Lean; typing rules from a logic-programming reading of the
bidirectional rules; the computation rules for `coe`/`hcom` at each type
former, which stay hand-written.

## Open: parallel closed evaluation

The evaluator is pure, fresh levels are local to each line and `Globals` is
read-only, so `Task.spawn` fork-join is possible and deterministic; the
stats ref behind `tick` would need to be per-task or off. Independent work:
the sides of a system (`hcompData`'s `sameCon`, `hcompFields`), the two
components of a pair under `transp`/`hcomp` at Σ, and the children of
`readback`, which drives most of `nf` since evaluation is lazy. Speculative
tasks in place of `Thunk.mk` in `mkLine`, `mkLazy` and `sub` are rejected:
millions of them, and they compute what laziness skips. Costs: atomic
reference counting on everything reachable from a spawned closure, a worker
spinning on a thunk another worker is computing (a blocking memo cell may
be needed), and peak memory, already the wall for `brunerieW` and `hope`.
Cheapest experiment: parallelise `sameCon` and the `readback` children
only, ticks off, the `Bench` ladder on one core against all.

## Derived closures

cctt defunctionalizes every closure so that substitution can act on it, and
writes each non-term closure three times (constructor, `apply` arm,
substitution arm); Template Haskell's stage restriction stops it deriving
them. Here term closures are cubicaltt-style (`Closure.mk env t`, the Pi
rules dispatched in `vApp` on `.transp`/`.hcomp` values), and the derived
closures of `Core/Defun.lean` serve the semantic interval binders: a
`Val.line` holds its body as a memoised thunk at a fresh variable, which
cannot be inspected, so its support has to come from the captures. Measured
on the open transport of the `w22` cube through `global`
(`split (λ k => w22 i j k)` normalised under `i j`):

| lines | time |
|---|---|
| memoised body, substitution deferred, support unknown | 19.7 s |
| derived closure only, body recomputed per instantiation | > 300 s |
| closure and memoised body, substitution eager on the captures | > 300 s |
| memoised body, substitution deferred, support from the captures | 8.8 s |

- Re-running the site at every instantiation, as cubicaltt does, holds
  memory flat at 1.8 GB where the memoised body grows about 300 bytes per
  `hcomp`, but costs 5x to 50x (`brunerie` 0.5 s to 22 s, `generator`
  3.8 s to 174 s).
- Eager substitution into the captures copies the shared computation graph
  as a tree. Substitution into a line stays deferred to instantiation; the
  derived `Line.act` is unused.
- `Line.vars` is a bitmask of levels over the captures, updated through the
  substitution's images; it never exceeds 19 bits here, so it is unboxed.
- Components peeked at a fresh level (`Glue`, universe compositions) cannot
  be re-instantiated from the type line, which reduces at the endpoints, and
  a closure capturing the level would need it renamed under substitution;
  `mkBind` makes them lines directly, the level cleared from the support.
- Captured local functions have no support, so helpers live in the mutual
  block. `Val` needs a nullary constructor for `Nonempty Line`.

Rejected: Kripke closures `Sub → Val → Val` (unsafe `Val`, no inspection,
so no support skipping); uniform closures, a code pointer plus tagged
captured fields (unsafe `Val`, a tag check per capture); explicit capture
lists (same output, one pass, no inference); transporting pass-1 `Expr`s
instead of re-elaborating (rewrites every auxiliary declaration Lean
produces, which change across releases). Open: what the closure is worth
for printing lines.

## Evaluation: what the measurements decided

Substitution is deferred everywhere (cctt's `sub`/`force`), and the
components a rule builds for every face of a `Glue` or universe composition
are `lazy`, since a total face keeps one and computing them strictly is
exponential in the nesting. Measured natively:

| probe | eager | deferred substitution | lazy components |
|---|---|---|---|
| `split` of the `w22` cube, open under `i j` | 0.85 s, 201k `hcomp` | 0.20 s, 17k | 0.16 s, 8.7k |
| one transport further, the `S1` loop, open under `i` | 297 s, 57M | 3.7 s, 47k | 0.5 s, 21k |
| `brunerie` | > 15 min | > 15 min | 0.6 s, 27k |

cctt's rule of never inspecting the sides of a strict inductive `hcomp`
with no fibrant variables made no difference once these were in.

Compound values carry their support in a `cached` node: walking the strict
skeleton at every substitution was the profile of `generator` (9.0 s to
3.8 s). What remains is flat: line instantiation, pushing substitutions,
face normal forms.

Restriction is cctt's, a cofibration `κ` in scope rather than an operation
on values (Eval.lean's module doc). Two details decide the cost: a captured
cofibration is not part of a closure's support, or every line built in a
face scope would look as if it mentioned the face; and what a face scope
captures is pre-restricted once (`face`), so one copy serves every
inspection under the face. Restriction as an operation let the `Glue` and
universe rules build a face's fibre from a type not restricted to the face,
producing off-face garbage that leaked through a later restriction;
`splitApp`, `unglueU'` and `transp'` panic on the symptoms. The change took
`brunerieW` from 13 minutes and 21 GB (74M `hcomp`s, universe compositions
rebuilt at every substitution pushed through a `case`) to 32 s and 2.7 GB
(1.07M), and let `hope`, which ran out of 34 GB, finish. For scale, cctt's
normal-form version of the same square takes 6.4 s and 13.5M `hcom`s
against 0.09 s and 87k for its Brunerie number.

Glued evaluation: `notEqSym k i` as a type, an `hcomp` in the universe over
`ua` and `J`, took 15 s to convert unfolded, and checking the square over it
converts it many times; `Examples/S1Mod2.lean` now checks in under a
second. Conversion compares system components under their face: the same
component reaches the checker restricted on one side and not the other.

## `hlevel`

The construction is kangrongji's `extend` (`kangrongji/cubical`, branch
`extend-all`, commit `b46c4be`, `HLevels/ExtendConstruction.agda`); the
mechanics are in `extend'`. What the branch does not do, and what makes
`extend` painful in Cubical Agda, is read the boundary off the goal: here
the checker records at each path binder the endpoints as faces the body
must respect, applies later binders to them, and hands the system to
`hlevel`. Truncations are constructors of the HITs, so a recursor's
truncation case is one `hlevel`.

## Results

`Examples/J2S2.lean`: the cheat-free `bit` of tomjack/cubical
`Stuff/Pi3JS2` is `true` in 5.5 s and 143k `hcomp`s, where Agda's `canon`
macro reports "not ok!", and the controls hold. What made every elaboration
in the chain take seconds: glued evaluation, the unifier's shortcuts for the
same object and the same closure, and `lineApp` keeping a definition glued
so that boundary values are quoted by name.

`Examples/Pi4S3.lean`: `π₄(S³)` is nontrivial, cctt's `hope` with its two
cheats removed; the invariant on the generator is `true` in 250 s and 11 GB
(3.9M `hcomp`s against `hope`'s 5.8M).
