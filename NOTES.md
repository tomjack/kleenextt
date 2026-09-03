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

Not computing: the writhe of the Whitehead square written directly as
nested `hcomp`s (`W22`, cctt's `w22thing`, whose writhe cctt's own file
names `error`) and `hope`. Both run out of memory (9 to 17 GB). Their
cubes are tiny (two `hcomp`s) but have connections in the constructor
arguments, so every `Glue` built from a face has faces on connections
that each filler instantiation splits again; the open `split` of the
`W22` cube has a 41 MB normal form against 111 KB for `w22`. The closed
computations never need that normal form, so what is retained, and why,
is the open question; the memoised `sub` heads and `lazy` bodies are the
suspects (cctt does not memoise forcing).

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
