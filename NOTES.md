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

Cofibrations are interval elements `r` (read `r = 1`), not face-lattice
elements, so that `¬r` exists and `ghcomp` can be defined
(see REFERENCES.md, "Empty systems"). Two ways to keep empty systems out
of closed terms:

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
