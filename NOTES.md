# Kleene CCHM — working notes

Goal: a simple but usable implementation of CCHM cubical type theory with a
Kleene algebra on the interval (a De Morgan algebra satisfying
`r ∧ ¬r ≤ s ∨ ¬s`) in place of the free De Morgan algebra of Cubical Agda
and cubicaltt.

"Usable" is set by the prior art. Cubical Agda has the surface language but
layers the cubical machinery onto a large elaborator, with long-standing
undiagnosed canonicity bugs. cubicaltt is small enough to trust (among the
π₄(S³) branches `pi4s3*` of mortberg/cubicaltt, `pi4s3_nobug` has the best
canonicity behaviour) but has no implicit arguments. The target is "cctt
with the Kleene interval": a small CCHM-style kernel plus an elaborator with
implicit arguments in the smalltt/elaboration-zoo style.

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
Two ways to keep empty systems out of closed terms:

- Enforce ABCFHL validity on every user `hcomp`: reject systems whose
  cofibration is not a classical tautology. No empty systems, but
  `hcomp [ (i=0) ↦ u ] u₀` must then be written as a `ghcomp`.
- Enforce nothing, and use `ghcomp` internally wherever a `∀i.φ` face can
  vanish (`transp` for `Glue`). This is what Cubical Agda does.

Current choice: the second, with `IExpr.isValid` available but not wired
into `hcomp`. Revisit once there is enough code to measure the effect on
normal forms.

## Open: declarative rules → implementation

Tiers, easiest first:

1. Syntax and binding: substitution, traversals, printing, α-equality from
   a datatype declaration. Well-trodden.
2. The interval theory and cofibration logic: equational and decidable, so
   a decision procedure can be generated from the presentation. This is the
   part that differs from stock CCHM, so keeping it declarative and
   swappable is high value, and the strongest argument for Lean.
3. Typing rules: a logic-programming reading of bidirectional rules can
   generate the checker skeleton.
4. The computation rules for `coe`/`hcom` at each type former: deriving
   these mechanically is research-grade. Hand-written.

## Open: parallel closed evaluation

Closed evaluation runs on one core. The evaluator is pure, fresh levels are
local to each line, and `Globals` is read-only, so nothing prevents more:
`Task.spawn` runs pure closures on a thread pool, `Task.get` from a worker
grows the pool so fork-join cannot starve, and a `Thunk` forced from two
threads is computed once. Results are deterministic. The stats ref behind
`tick` would serialise every tick under contention and needs to be per-task
or off.

Independent work: the sides of a system (`hcompData`'s `sameCon` forces
every side, `hcompFields` then composes per field), the two components of a
pair under `transp` or `hcomp` at Σ, and the children of `readback`, which
drives most of the work in `nf` since evaluation is lazy.

Fork-join at those points, with a depth or size cutoff, keeps laziness and
is easy to switch off. Speculative tasks in place of `Thunk.mk` in `mkLine`,
`mkLazy` and the `sub` head are rejected: the counters put these in the
millions, so spawn overhead dominates, and it computes what laziness skips.

Costs: every object reachable from a spawned closure gets atomic reference
counting, so single-thread throughput drops and several busy cores are
needed to break even; a worker forcing a thunk another worker is computing
spins, so a memo cell that blocks (a promise behind `implemented_by`, as
`tick` is) may be needed; peak memory rises with branches in flight, and
memory is the wall for `brunerieW` and `hope`. Unknown: how much of the side
computations funnels into shared memoised thunks, which bounds the speedup.

Cheapest experiment: parallelise `sameCon` and the `readback` children
only, ticks off, and run the `Bench` ladder pinned to one core against all
cores.

## Derived closures

cctt defunctionalizes every closure in the semantic domain because interval
substitution has to act on closures and HOAS closures cannot be inspected
(cctt README, "Defunctionalization"). Each closure whose body is not a term
is then written three times: constructor, arm of `apply`, arm of the
substitution action. Kovács notes a metaprogramming framework for this
"would be a lot of work (if it's even feasible in Haskell)"; Template
Haskell's stage restriction forces the closure type to be declared before
the evaluator that determines its constructors.

Term closures here are cubicaltt-style, one `Closure.mk env t`, with the Pi
rules for `transp`/`hcomp` dispatched in `vApp` on the `.transp`/`.hcomp`
values themselves. The semantic interval binders are the pressure: a
`Val.line` holds its body as a memoised thunk at a fresh variable, which
cannot be inspected, so without more the support check must treat it as
mentioning every variable. `Core/Defun.lean` derives the closure type from
the use sites in two Lean elaboration passes (its module doc has the
mechanism); `Core/Eval.lean` builds every line this way and derives
`Line.vars`, the support of a line from its captures. Everything is Lean
compile-time work; the binary runs ordinary cctt-style code.

Measured on the open transport of the `w22` cube through `global`
(`split (λ k => w22 i j k)` normalised under `i j`):

| lines | time |
|---|---|
| memoised body, substitution deferred, support unknown | 19.7 s |
| derived closure only, body recomputed per instantiation | > 300 s |
| closure and memoised body, substitution eager on the captures | > 300 s |
| memoised body, substitution deferred, support from the captures | 8.8 s |

- The memoised body at a fresh variable is essential. A closure re-running
  its site at every instantiation, as cubicaltt's do, holds memory flat at
  1.8 GB where the memoised design grows about 300 bytes per `hcomp`, but
  costs 5x to 50x in work (`brunerie` 0.5 s to 22 s, `generator` 3.8 s to
  174 s).
- Eager substitution into the captures is not usable either: the captures
  reach the whole shared computation graph, and a field-wise action copies
  it as a tree. Substitution into a line stays deferred to instantiation,
  so the derived `Line.act` is not used.
- What the closure contributes is the support: `Line.vars`, a bitmask of
  levels folded over the captures, cached in the line and updated through
  the substitution's images. It never exceeds 19 bits here, so it is
  unboxed.
- Components of a `Glue` or universe composition peeked at a fresh level
  cannot be re-instantiated from the type line, since the type reduces at
  the endpoints, and a closure capturing the level would need it renamed
  under substitution. `mkBind` makes them lines directly: the body at the
  bound level, with the level cleared from the support.
- Local helper functions captured by lines have function types, which have
  no support; they live in the mutual block instead.
- `Val` needs a nullary constructor: the derived functions are `partial`,
  and `Nonempty Line` is derived from `Nonempty Val`.

Alternatives considered:

- Kripke closures `Sub → Val → Val`: no metaprogramming, but `Val` is
  `unsafe` and closures cannot be inspected, so no support skipping and no
  printing of closures.
- Uniform closures, a closed code pointer plus an array of tagged captured
  fields, built by a term elaborator: single pass, no generated inductive,
  generic substitution, but `Val` is `unsafe` and each capture costs a tag
  check on apply.
- Explicit captures: each closure a named declaration listing its captured
  parameters, and the macro emits inductive, `apply` and substitution. Same
  output, one pass, no hygiene risk; inferred versus listed captures is the
  only difference.
- Transporting the elaborated `Expr`s from the naive types to the real ones
  instead of re-elaborating: avoids the second pass but has to rewrite every
  auxiliary declaration Lean produced (matchers, the `partial`
  implementation split, `let` encodings), all of which change across Lean
  releases.

Open: what the closure is worth for printing lines.

## Evaluation: what the measurements decided

Substitution is deferred everywhere (cctt's `sub`/`force`): a `sub` node
records the substitution and its support and is pushed one layer when the
head is inspected. The components a rule builds for every face of a `Glue`
or universe composition, where a total face keeps one, are `lazy`;
computing them strictly is exponential in the nesting of universe
compositions. Measured natively:

| probe | eager | deferred substitution | lazy components |
|---|---|---|---|
| `split` of the `w22` cube, open under `i j` | 0.85 s, 201k `hcomp` | 0.20 s, 17k | 0.16 s, 8.7k |
| one transport further, the `S1` loop, open under `i` | 297 s, 57M | 3.7 s, 47k | 0.5 s, 21k |
| `brunerie` | > 15 min | > 15 min | 0.6 s, 27k |

cctt's closed-evaluation rule for strict inductive `hcomp` (never inspect
the sides when there are no fibrant variables) made no difference: no side
is inspected on this computation once substitution and components are lazy.

Compound values carry their support in a transparent `cached` node. Walking
the strict skeleton at every substitution and every line or lazy node built
was the profile of the Hopf generator (`generator`: 9.0 s to 3.8 s). What
remains is flat: line instantiation, pushing substitutions, face normal
forms.

Restriction is cctt's: a cofibration `κ` in scope, not an operation on
values. A head is inspected under `κ` (`frc`, free when the value mentions
none of `κ`'s generators); the work for a face `α` runs under `κ ∧ α`,
captured by the face's closure; systems keep their faces relative to `κ`;
interval decisions apply `κ`. Substitution (`act`) remains for renaming,
instantiating a peeked variable, and constant instantiation. Two details
decide the cost: a captured cofibration is not part of a closure's support,
or every line built in a face scope would look as if it mentioned the face;
and what a face scope captures is pre-restricted once (`face`), so one
restricted copy serves every inspection under the face. Restriction as an
operation let the `Glue` and universe-composition rules build a face's
fibre from a type component not restricted to the face, producing off-face
garbage that leaked through a later restriction; `splitApp`, `unglueU'` and
`transp'` panic on the symptoms (a case or unglue of a canonical form of the
wrong type, a transport stuck at a non-neutral type). The change took
`brunerieW` from 13 minutes and 21 GB (74M `hcomp`s, the universe
compositions rebuilt at every substitution pushed through a `case`) to 32 s
and 2.7 GB (1.07M), and let `hope`, which ran out of 34 GB, finish. cctt is
Cartesian, without connections; its normal-form version of the square takes
6.4 s and 13.5M `hcom`s against 0.09 s and 87k for its Brunerie number, so
the direct square is two orders harder there too.

Evaluation is glued: a definition stays a head with its spine and its
unfolding, compared or quoted by the spine first. `notEqSym k i` as a type,
an `hcomp` in the universe over `ua` and `J`, took 15 s to convert with
itself unfolded, and checking the square over it converts it many times;
`Examples/S1Mod2.lean` checks in under a second. Conversion compares the
components of two systems under their face: a component is only meaningful
there, and the same one reaches the checker restricted on one side and not
on the other.

## `hlevel`

`hlevel n h` fills the cube the enclosing path binders ask for, in a type of
h-level `n`, from `h : isOfHLevel n A` (`isContr`, then
`(x y : A) → isOfHLevel (n-1) (Path A x y)`, with `isProp` at 1). The
construction is kangrongji's `extend` (`kangrongji/cubical`, branch
`extend-all`, commit `b46c4be`, `HLevels/ExtendConstruction.agda`): peel the
last cube variable, fill an `(n-1)`-cube in the path type between its two
faces, whose h-level is `h x₀ x₁`, down to a proposition, and `ext` for a
contractible type. A proposition needs no correcting composition: the
boundary is the whole one, so `h x₀ x₁` has the faces as its endpoints
definitionally, over a family too when `h` at the point is applied to the
endpoints transported there along connections. What the branch does not do,
and what makes `extend` painful in Cubical Agda, is read the boundary off
the goal: here the checker records at each path binder the endpoints as the
faces the body must respect, applies later binders to them, and hands the
system to `hlevel`. The core term keeps the cube variables; evaluation peeks
them at fresh levels, builds the cube and substitutes, so it is stable under
connections. A type varying over the cube transports the h-level along it
(`isOfHLevelPathP'`); a cube of dimension above the level weakens `h` up to
it (`isOfHLevelSuc`).

Truncations are constructors of the HITs: `S1m2` has `trunc`, a 3-cube with
path-typed fields, so a recursor's truncation case is one `hlevel`.

## Results

`Examples/S1Mod2.lean`: `Helix/2` into `hSet` needs the library up to
`isGroupoidHSet` (Π, Σ and retracts by `hlevel`, `Bool` a set by
encode-decode, `Path Type A B` a set as a retract of `Equiv A B` by `ua` and
`J`).

`Examples/J2S2.lean`: the cheat-free `bit` of tomjack/cubical
`Stuff/Pi3JS2`. The family over `J₂S²` has fibre `S1t × S2m2` (truncations
as constructors), `global rotLoopsMod2` over `surf₁` and over `surf₂` the
`2,2`-extension that `rotLoopsMod2Mod2` gives through `LocalGlobal`
(`Examples/Tubes.lean`, `Examples/LocalGlobal.lean`, with `glueU` in the
surface syntax for `thing2`). Transport along it takes the Hopf generator
`η surf₁` of `π₃(J₂S²)` to `π₂∥S²/2∥₂`, `Code` into `hGroupoid` to
`π₁∥S¹/2∥₁`, and `Helix/2` to `Bool`: `true`, in 5.5 s and 143k `hcomp`s,
where Agda's `canon` macro reports "not ok!". The constant cube and `η ∙ η`
give `false`, the flipped generator `true`. Every elaboration in the chain
takes seconds, given glued evaluation, the unifier's shortcuts for the same
object and the same closure, and `lineApp` keeping a definition glued so
that boundary values are quoted by name.

`Examples/Pi4S3.lean`: `π₄(S³)` is nontrivial,
`π4S3Nontrivial : Path (Ω⁴S³) (η loop3) refl → Empty`. The invariant is
`bit` after `Ω⁴S³ → Ω³J₂S²`, transport along `global3` of the surfaces of
`J₂S²` over `loop3`: cctt's `hope` with its two cheats removed, `J₂S²`
carrying its 4-truncation as a constructor so the surfaces over `surf₂` are
one `hlevel`, and the family landing in `h2Groupoid`
(`is3GroupoidH2Groupoid`) with the truncation case a 5-cube by `hlevel`.
The invariant on the generator is `true` in 250 s and 11 GB (3.9M `hcomp`s,
against `hope`'s 5.8M); checking `π4S3Nontrivial` computes it.
