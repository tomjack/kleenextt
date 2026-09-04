# Kleene CCHM — working notes

Goal: a simple but usable implementation of CCHM cubical type theory with a
Kleene algebra structure on the interval (De Morgan algebra satisfying
`r ∧ ¬r ≤ s ∨ ¬s`) in place of the free De Morgan algebra used by Cubical Agda
and cubicaltt.

"Usable" pins down the two lessons from prior art:

- Cubical Agda: usable surface language, but the cubical machinery is layered
  onto a large existing elaborator; long-standing undiagnosed canonicity bugs.
- cubicaltt: small enough to trust (certain branches have better canonicity
  behavior — notably `pi4s3_nobug`, among the π₄(S³) experiment branches
  `pi4s3*` on mortberg/cubicaltt), but no implicit arguments, so unusable in
  practice.

So the target is roughly "cctt with the Kleene interval": a small standalone
kernel in the CCHM style plus a real elaborator with first-class implicit
arguments in the smalltt/elaboration-zoo style.

## Open question: build in the validity constraint?

System faces are conjunctions of `(i = 0)`/`(i = 1)` on variables, and a
cofibration is its face normal form. `ghcomp` is currently Mörtberg's
`hcomp [φ ↦ u, ¬φ ↦ u₀] u₀` with `¬φ` computed on the normal form;
Angiuli's structural definition (cctt's `ghcomdn`) needs no negation at
all and could replace it (see REFERENCES.md, "Empty systems"). Two ways
to keep empty systems out of closed terms:

- Enforce ABCFHL validity on every user `hcomp`: reject systems whose
  cofibration is not a classical tautology. Guarantees no empty systems,
  but rejects e.g. `hcomp [ (i=0) ↦ u ] u₀`, which then has to be
  written as a `ghcomp`.
- Enforce nothing, use `ghcomp` internally wherever a `∀i.φ` face can
  vanish (`transp` for `Glue`), and leave user systems alone. This is
  what Cubical Agda does.

Current choice: the second, with a validity check available but not
wired into `hcomp`. Revisit once there is enough code to measure the
effect on normal forms.

## Open question: declarative rules → implementation

How much of the system can be written down declaratively and compiled to code?

Realistic tiers, easiest first:

1. Syntax + binding: derive substitution/weakening, traversals, pretty
   printing, α-equality from a datatype declaration. Well-trodden.
2. The interval theory: the Kleene algebra operations and the cofibration
   logic are equational/decidable; a decision procedure could be generated
   from the presentation, and this is exactly the part that differs from
   stock CCHM, so keeping it declarative and swappable is high value.
3. Typing rules: a logic-programming-style reading of bidirectional rules can
   generate the checker skeleton. Harder but done before.
4. The computation rules for `coe`/`hcom` at each type former: this is where
   cubical implementations live or die; deriving these mechanically is
   research-grade. Expect to hand-write them in any language.

Tier 2 is the strongest argument for Lean: the novel part of Kleene CCHM is
precisely an algebraic theory, and Lean can both state it and generate the
solver.

## Open question: parallel closed evaluation

Closed evaluation runs on one core. Nothing in the evaluator prevents
using more: it is pure, fresh levels are local to each line so there is
no name supply to contend for, and `Globals` is read-only during closed
evaluation. Lean's runtime supports it: `Task.spawn` runs pure closures
on a thread pool, `Task.get` from a worker grows the pool by one while
it waits so fork-join cannot starve (documented on `Task.get`), and a
`Thunk` forced from two threads is computed once, the other forcer
spinning until the value appears. Results are deterministic. The one
mutable piece, the stats ref behind `tick`, would serialise every tick
under contention and needs to be per-task or off.

Independent work is in the sides of a system (`hcompData`'s `sameCon`
forces every side at a fresh variable, `hcompFields` then composes per
field), the two components of a pair from `transp` or `hcomp` at Σ, and
the children of `readback`, which is what drives most of the work in
`nf` since evaluation is lazy.

Two ways in:

- Fork-join at those points, `Task.spawn` over a list then `Task.get`,
  with a depth or size cutoff. Keeps laziness; easy to switch off.
- Speculative: tasks in place of `Thunk.mk` in `mkLine`, `mkLazy` and
  the `sub` head. The counters put these in the millions, so spawn
  overhead dominates, and it computes and retains what laziness now
  skips. Rejected.

Costs: every object reachable from a spawned closure gets atomic
reference counting, which Lean does a lot of, so single-thread
throughput drops and several busy cores are needed to break even; a
worker that forces a thunk another worker is computing burns a core
spinning, so a memo cell that blocks properly (a promise behind
`implemented_by`, as `tick` is) may be needed; peak memory rises with
branches in flight, and memory is the current wall for `W22` and
`hope`. Unknown: how much of the side computations funnels into shared
memoised thunks, which bounds the speedup.

Cheapest experiment: parallelise `sameCon` and the `readback` children
only, ticks off, and run the `Bench` ladder pinned to one core against
all cores.

## Derived closure defunctionalization

cctt defunctionalizes every closure in the semantic domain, not for speed
but because interval substitution has to act on closures and HOAS closures
can't be inspected (cctt README, "Defunctionalization"). The cost is that
each closure whose body is not a term — `CCoePi`, the `CIsEquiv*` family,
`CCoeLinv` and friends — is written three times: constructor, arm of the
generic `apply`, arm of the substitution action. Kovács notes a
metaprogramming framework for this "would be a lot of work (if it's even
feasible in Haskell)"; the Haskell obstacle is Template Haskell's stage
restriction, which forces the closure type to be declared before the
evaluator that determines its constructors.

The Lean implementation sidesteps the issue in the cubicaltt style for term
closures: one `Closure.mk env t`, with the Pi rules for `transp`/`hcomp`
dispatched in `vApp` on the `.transp`/`.hcomp` values themselves. That is
already a defunctionalization with the `Val` constructors doubling as
closures. The pressure has arrived with the semantic interval binders:
`Val.line` holds its body as a memoised `Thunk` at a fresh variable, and
substitution into it is deferred to instantiation. It cannot be inspected,
so the support check treats it as mentioning every variable, and the
Brunerie-number probes show that this costs (see `README.md`).
A derived defunctionalization of the rule-built lines is the natural fix.

The derivation is a Lean command elaborator, `Defun.lean`,
exercised on a toy domain in `DefunTest.lean` and used by `Eval.lean`.
The evaluator is written naively, with closures as `closure% fun …` at
the use site, inside a `defun … in … end defun` block holding the domain
and its rules. Everything is Lean compile-time work; the Kleenextt binary
runs ordinary cctt-style code.

The circularity: the generated `Closure` inductive needs one constructor
per lambda site, with fields typed by the Lean locals that site captures,
and those types are only known after Lean elaborates the site; but the
site lives inside `eval`, which can't be elaborated against the real `Val`
until `Closure` exists. Resolution, two Lean elaboration passes:

1. Against `unsafe structure Closure where apply : A → B → Val` (unsafe
   because of the negative occurrence), with every declaration made
   `unsafe`, `deriving` clauses stripped, and each site wrapped in a
   marker. The elaborated definitions are traversed to record, per site,
   the captured locals with their names and delaborated types, in context
   order; section variables are excluded by name. Everything declared is
   discarded, info trees included.
2. For real: `Closure` becomes an inductive with one constructor per site,
   each site becomes its constructor applied to the locals, `Closure.apply`
   re-elaborates each site's lambda in the arm for its constructor, and
   each header clause `deriving f (p : P) via K.m := impl` generates
   `Closure.f : P → Closure → Closure` applying the single-method class
   `K` to every field, with `⟨impl⟩ : K Val` as a local instance (or, with
   `: T folding op e`, folds the fields' values into `T`); the instances
   for the other field types (`IExpr`, `Face`, lists, pairs) are ordinary.

`Closure.mk` and `Closure.apply` exist in both passes, so the rules are
written once. Only the elaborator's public surface is used (elaborating
commands, `Meta.transform` over definition values, delaboration), so the
scheme is not exposed to the internal encodings of matchers, `partial`,
or `let`. Hygiene: the recorded names are reused verbatim for the arm
binders, and a site capturing an inaccessible local is reported.

What the port of `Eval.lean` settled, measured on the open transport of
the `w22` cube through `global` (`split (λ k => w22 i j k)` normalised
under `i j`):

| lines | time |
|---|---|
| memoised body, substitution deferred, support unknown (before) | 19.7 s |
| derived closure only, body recomputed per instantiation | > 300 s |
| closure and memoised body, substitution eager on the captures | > 300 s |
| memoised body, substitution deferred, support from the captures | 8.8 s |

- The memoised body at a fresh variable is essential; a closure
  re-running its site at every instantiation, as cubicaltt does, is not
  usable here.
- Eager substitution into the captures is not usable either: the
  captures reach the whole computation graph, which is shared, and a
  field-wise action copies it as a tree. Substitution into a line stays
  deferred to instantiation, so the derived `Line.act` is not used.
- What the derived closure contributes is the support: `Line.vars`,
  a bitmask of levels folded over the captures, cached in the line and
  updated through the substitution's images. This is the exact support
  check the memoised design lacked, and it halves the time.
- The components of a `Glue` or universe composition peeked at a fresh
  level cannot be re-instantiated from the type line, since the type
  reduces at the endpoints, and a closure capturing the level would need
  the level renamed under substitution, which a field-wise action cannot
  do. `mkBind` makes them lines directly: the body at the bound level,
  with the level cleared from the support.
- Local helper functions captured by lines (`at_`, `atI`, `cod`, `rev`,
  `item`) have function types, which have no support; they moved to the
  mutual block.
- `Val` needs a nullary constructor: the derived functions are `partial`,
  and `Nonempty Line` is derived from `Nonempty Val`.

Substitution is now deferred everywhere (cctt's `sub`/`force`): a `sub`
node records the substitution and its support and is pushed one layer
when the head is inspected, so eager copying of the computation graph is
gone and `Line.act` has no role. The rules were also computing every
face's fiber and composite strictly where a total face keeps one, which
is exponential in the nesting of universe compositions; those components
are now `lazy` nodes. Measured natively (the evaluator ran in Lean's
interpreter before, ten times slower):

| probe | eager | deferred substitution | lazy components |
|---|---|---|---|
| `split` of the `w22` cube, open under `i j` | 0.85 s, 201k `hcomp` | 0.20 s, 17k | 0.16 s, 8.7k |
| one transport further, the `S1` loop, open under `i` | 297 s, 57M | 3.7 s, 47k | 0.5 s, 21k |
| `brunerie` | > 15 min | > 15 min | 0.6 s, 27k |

cctt's closed-evaluation rule for strict inductive `hcomp` (never inspect
the sides when there are no fibrant variables) was tried and made no
difference here: no side is inspected on this computation once
substitution and components are lazy.

With those in place the profile of the Hopf-construction generator moved
to the support computation, which walked the strict skeleton of a value
at every substitution and every line or lazy node built, with closure
environments nesting; compound values now carry their support in a
transparent `cached` node (`generator`: 9.0 s to 3.8 s). What remains is
flat: line instantiation, pushing substitutions, face normal forms.

The writhe of the Whitehead square written directly as nested `hcomp`s
with connections in the constructor arguments (`W22`, Tom's `W₂₂'`) is
+2, in 13 minutes and 21 GB: 74M `hcomp`s against 27k for `brunerie`.
It first normalised, with the same work, to a stuck term, `helix`
applied to a `glueU`. The `Glue` and universe-composition rules built
each face's fibre from the type component `E` of that face without
restricting `E` to the face, while restricting the element; off the face
the type is a universe composition where on the face it is `S1`, so the
transport of `base` produced off-face garbage (`unglueU base` at a
system with no total face), which leaked when a later composition
restricted its type to the face, found a data type, and returned the
element unchanged. cubicaltt restricts both. `generator` passed through
the same states and was right by luck; `brunerie` never reached them.
`splitApp`, `unglueU'` and `transp'` now panic on a case or unglue of a
canonical form of the wrong type and on a transport stuck at a
non-neutral type. Found with `#ktrace` (counters and resident size every
two seconds), `#khead` (head and system faces at generic levels),
`#kstable` (generic evaluation then substitution of an endpoint, against
evaluation at the endpoint), `#koverlaps` (sides of an `hcomp` agree on
common faces and with the base) and a tag threaded through `transp'`
naming the construction site.

Memory grows linearly with work, about 300 bytes per `hcomp`: what is
computed stays reachable through the memoised line bodies of the outer
transports' lines. Lines that re-apply their closure at each
instantiation instead, as cctt's do, hold memory flat at 1.8 GB but cost
5x to 50x in work (`brunerie` 0.5 s to 22 s, `generator` 3.8 s to 174 s),
so the memoised body stays. The level bitmask never exceeds 19 here, so
it is unboxed. cctt is Cartesian, without connections; its normal-form
version of the square (`w22thing`) takes 6.4 s and 13.5M `hcom`s against
0.09 s and 87k for its Brunerie number, so the direct square is two
orders harder there too.

Restriction is now cctt's: a cofibration in scope, not an operation on
values. Every rule takes `κ`, a face, next to `L`. A head is inspected
under `κ` (`frc`, which applies `κ` at the head only and is free when the
value mentions none of `κ`'s generators); the work for a face `α` of a
system runs under `κ ∧ α`, captured by the face's closure; systems keep
their faces relative to `κ`, re-read under a larger one; interval
decisions apply `κ`. Substitution (`act`) stays for renaming, for
instantiating a peeked variable, and for constant instantiation. Two
details decided the cost. A captured cofibration is not part of a
closure's support, or every line built in a face scope looks as if it
mentioned the face and is restricted again at each inspection. And what a
face scope captures is pre-restricted once with `face`, so one restricted
copy serves every inspection under the face, with `κ` only the guarantee.
The bug above cannot be written any more. Counts on the ladder drop or
hold (`generator` 204k to 142k `hcomp`s) at the same wall time, and
`brunerieW` goes from 13 minutes and 21 GB to 32 s and 2.7 GB, 74M to
1.07M `hcomp`s: the universe compositions were rebuilt at every
substitution pushed through a `case`, 25.7M times, now 105k. `hope`,
which ran out of 34 GB in 12 minutes, is +1 in 310 s with memory flat at
2.8 GB from the first half minute (5.9M `hcomp`s).

`hlevel n h` fills the cube the enclosing path binders ask for, in a type
of h-level `n`, from `h : isOfHLevel n A` (`isContr`, then `(x y : A) →
isOfHLevel (n-1) (Path A x y)`, with `isProp` at 1). The construction is
kangrongji's `extend` (the `extend-all` branch of `kangrongji/cubical`,
commit `b46c4be`, `HLevels/ExtendConstruction.agda`): peel the last cube
variable, fill an `(n-1)`-cube in the path type between its two faces,
whose h-level is `h x₀ x₁`, down to `extend₁` for a proposition and `ext`
for a contractible type. What the branch does not do, and what makes
`extend` painful in Cubical Agda, is read the boundary off the goal: here
the checker records, at each path binder, the endpoints as the faces the
body must respect, applies later binders to them, and hands the system to
`hlevel`. The core term keeps the cube variables; evaluation peeks them
at fresh levels, builds the cube there and substitutes, so it is stable
under connections. A type varying over the cube transports the h-level
along it (`isOfHLevelPathP'`). Not yet: a cube of dimension above the
level (needs `isOfHLevelSuc`).

The truncations are built into the HITs: `S1m2` has `trunc`, a 3-cube
constructor with path-typed fields, so its recursor's truncation case is
one `hlevel`. `Helix/2` into `hSet` needs the library up to
`isGroupoidHSet`: Π, Σ and retracts by `hlevel`, `Bool` a set by
encode-decode, `Path Type A B` a set as a retract of `Equiv A B` by `ua`
and `J`. Two things in the checker had to change for it. Conversion
compares the components of two systems under their face: a component is
only meaningful there, and the same one reaches the checker restricted on
one side and not on the other. And evaluation is glued: a definition
stays a head with its spine and its unfolding, compared or quoted by the
spine first and unfolded only when that fails. `notEqSym k i` as a type,
an `hcomp` in the universe over `ua` and `J`, took 15 s to convert with
itself unfolded, and checking the square over it converts it many times;
`S1Mod2.lean` now checks in under a second.

Open: what the closure is worth for printing lines.

Alternatives considered:

- Kripke closures `Sub → Val → Val`: no metaprogramming, but `Val` is
  `unsafe` and closures can't be inspected, so no support skipping and no
  printing of closures.
- Uniform closures, a closed code pointer plus an array of tagged captured
  fields, built by a term elaborator: single pass, no generated inductive,
  generic substitution, but `Val` is `unsafe` and each capture costs a tag
  check on apply.
- Explicit captures: each closure is a named declaration with its captured
  parameters listed, and the macro emits inductive, `apply` and
  substitution. Same output, one pass, no hygiene risk; the only
  difference is inferred versus listed captures.
- Transporting the elaborated `Expr`s from the naive types to the real
  ones instead of re-elaborating: avoids the second pass but has to rewrite
  every auxiliary declaration Lean produced (matchers and their metadata,
  the `partial` implementation split, `let` encodings), all of which have
  changed across Lean releases. Rejected.
