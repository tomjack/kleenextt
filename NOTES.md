# Kleene CCHM — working notes

Goal: CCHM cubical type theory with a Kleene algebra on the interval (a De
Morgan algebra with `r ∧ ¬r ≤ s ∨ ¬s`) in place of the free De Morgan
algebra: cctt's small kernel with an elaboration-zoo-style elaborator, so
that unlike cubicaltt it has implicit arguments and unlike Cubical Agda it
is small enough to trust. The interval theory is the part that differs
from stock CCHM, and it is decidable, which is the argument for Lean: state
it and generate the solver.

## Known gaps

- No interval metavariables, so an interval-binding lambda must be checked
  against a known type.
- The `Glue` eta rule is in unification but not in the computation rules.
- Implicit insertion is §2.6 of Kovács' ICFP 2020 paper only; first-class
  polymorphism (postponed insertion, elaboration-zoo stage 06) is not
  implemented.

## Open

Validity: `ghcomp` is Mörtberg's `hcomp [φ ↦ u, ¬φ ↦ u₀] u₀`; Angiuli's
structural `ghcomdn` (cctt) needs no negation and could replace it. As in
Cubical Agda, ABCFHL validity is not enforced on user systems
(`IExpr.isValid` exists), and `ghcomp` is used where a `∀i.φ` face can
vanish. Enforcing it would reject `hcomp [ (i=0) ↦ u ] u₀`.

Right-nested composition: `examples/Winding.ktt` winds a thousand loops in
0.14 s as `((refl ∙ loop) ∙ …) ∙ loop` and 4.5 s as `loop ∙ (… ∙ refl)`,
a hundred in 12 ms and 41 ms, so the right-nested case is quadratic where
cctt's `test1` winds a million in 8 s.

Parallelism: the evaluator is pure and `Globals` read-only, so fork-join
with `Task.spawn` is deterministic. Candidates: the sides of a system in
`hcompData`, the two components under `transp`/`hcomp` at Σ, the children
of `readback`. Speculative tasks per thunk are rejected (millions, and they
compute what laziness skips); atomic refcounting and peak memory are the
costs. Experiment: `sameCon` and `readback` only, ticks off, the
`BrunerieBench` rungs on one core against all.

What the derived closure is worth for printing lines.

## Derived closures

`Val.line` holds its body as a memoised thunk at a fresh variable, which
cannot be inspected; `Core/Defun.lean` derives a closure per use site so
that the support comes from the captures. On the open transport of the
`w22` cube through `global` (`split (λ k => w22 i j k)` under `i j`):

| lines | time |
|---|---|
| memoised body, substitution deferred, support unknown | 19.7 s |
| derived closure only, body recomputed per instantiation | > 300 s |
| closure and memoised body, substitution eager on the captures | > 300 s |
| memoised body, substitution deferred, support from the captures | 8.8 s |

Re-running the site per instantiation (cubicaltt) holds memory flat at
1.8 GB where the memoised body grows about 300 bytes per `hcomp`, but costs
5x to 50x (`generator` 3.8 s to 174 s). Eager substitution into the
captures copies the shared graph as a tree, so the derived `Line.act` is
unused. `Line.vars` is a bitmask, under 19 bits here, so unboxed.
Components peeked at a fresh level cannot be re-instantiated from a type
line that reduces at the endpoints; `mkBind` binds the level directly.
Rejected designs: Kripke closures and uniform tagged closures (both need an
unsafe `Val`), explicit capture lists (same output, no inference),
transporting pass-1 `Expr`s (rewrites Lean's auxiliary declarations, which
change across releases).

## Evaluation

Substitution is deferred (cctt's `sub`/`force`) and the components built
for every face of a `Glue` or universe composition are `lazy`, since a
total face keeps one. Measured natively:

| probe | eager | deferred substitution | lazy components |
|---|---|---|---|
| `split` of the `w22` cube, open under `i j` | 0.85 s, 201k `hcomp` | 0.20 s, 17k | 0.16 s, 8.7k |
| one transport further, the `S1` loop, open under `i` | 297 s, 57M | 3.7 s, 47k | 0.5 s, 21k |
| `brunerie` | > 15 min | > 15 min | 0.6 s, 27k |

Support is cached in compound values (`generator` 9.0 s to 3.8 s); what
remains is flat. Restriction is a cofibration `κ` in scope, not an
operation (Eval.lean's module doc); a captured cofibration is not part of a
closure's support, and a face scope's captures are pre-restricted once.
That took `brunerieW` from 13 minutes and 21 GB to 32 s and 2.7 GB, and
made the off-face garbage the old rules could produce (a fibre built from
a type not restricted to its face) unwritable; `splitApp`, `unglueU'` and
`transp'` panic on its symptoms. Glued evaluation, and comparing system
components under their face, took `examples/S1Mod2.ktt` from 15 s per
conversion of `notEqSym` to under a second in all.

`hcomp` at a strict inductive type follows cctt's closed rule: a value
mentioning a fibrant variable or a metavariable carries `openBit` in its
support, and with closed sides `hcompData` forces none of them, since by
canonicity they share the base's constructor; each field projects them
lazily. Closedness is a property of the value, not of the context, so the
rule also applies inside a typechecking boundary such as `e 0` in
`π4S3Nontrivial`. Nothing here reaches it (`hcomp data` is 0 for
`brunerieW`, `Pi4S3` and `examples/Winding.ktt`): a closed system is total
under `ghcomp`, and a composition at the endpoint of a `Glue` or
`hcomp Type` line has a total face. cctt's own tests and benchmarks reach
its rule twice, on empty systems, in `tests/tests/indtests2.cctt`. It fires
on a composition at `Nat` written under an interval variable, as in
`examples/Cubical.ktt`.

## `hlevel`

kangrongji's `extend` (`kangrongji/cubical`, branch `extend-all`, commit
`b46c4be`), with the boundary read off the path binders by the checker
rather than off the goal, and truncations as HIT constructors.

## Results

`examples/J2S2.ktt`: the cheat-free `bit` of tomjack/cubical
`Stuff/Pi3JS2` is `true` in 5.5 s, where Agda's `canon` reports "not ok!".
`examples/Pi4S3.ktt`: `π₄(S³)` is nontrivial, cctt's `hope` without its
cheats, in 250 s and 11 GB.
