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
exercised on a toy domain in `DefunTest.lean`; `Eval.lean` does not use
it yet. The evaluator is written naively, with closures as `closure% fun
…` at the use site, inside a `defun … in … end defun` block holding the
domain and its rules. Everything is Lean compile-time work; the Kleenextt
binary runs ordinary cctt-style code.

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
   `Closure.f : P → Closure → Closure` (or `→ Bool`, an `||`-fold, when
   the clause's result is `Bool`) applying the single-method class `K` to
   every field, with `⟨impl⟩ : K Val` as a local instance; the instances
   for the other field types (`IExpr`, `Face`, lists, pairs) are ordinary.

`Closure.mk` and `Closure.apply` exist in both passes, so the rules are
written once. Only the elaborator's public surface is used (elaborating
commands, `Meta.transform` over definition values, delaboration), so the
scheme is not exposed to the internal encodings of matchers, `partial`,
or `let`. Hygiene: the recorded names are reused verbatim for the arm
binders, and a site capturing an inaccessible local is reported.

What porting `Eval.lean` needs:

- Local helper functions captured by lines (`at_`, `atI`, `cod`, `rev`,
  `item`) have function types, which have no substitution action; they
  move to the mutual block.
- A captured `Face` is the face of the component the closure is, so its
  action drops the levels the substitution fixes; this relies on `actSys`
  substituting into a component only under a substitution making its face
  hold, which is what it does.
- Context sizes captured from an enclosing scope (`transpFillNeg` uses
  `L` under `L1`) need either a constant instance for `Nat`, sound because
  a size only bounds the fresh levels from below, or the body to use its
  own parameter.
- Memoisation: `Val.line l body` computes the body once at a fresh
  variable, and this made the open transport over the `w22` cube finish.
  A derived closure recomputes on every instantiation, as cubicaltt does.
  Both can be kept: `line (c : Closure) (body : Thunk Val)`, the closure
  for inspection and substitution, the thunk for instantiation.
- `Val` needs a nullary constructor: the derived functions are `partial`,
  and `Nonempty Closure` is derived from `Nonempty Val`.

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
