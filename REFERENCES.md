# References

Slugs match `scripts/refs.tsv`; run `scripts/fetch-refs.sh` to download
everything into `refs/` (gitignored): arXiv sources under `refs/tex/`,
repositories under `refs/repos/`, loose PDFs under `refs/misc/`.

All arXiv IDs and "not on arXiv" claims below were verified against the arXiv
API (2026-08-31).

## Core: CCHM-style cubical type theory

- **cchm** — Cohen, Coquand, Huber, Mörtberg,
  *Cubical Type Theory: a constructive interpretation of the univalence
  axiom*, TYPES 2015 post-proceedings.
  [arXiv:1611.02108](https://arxiv.org/abs/1611.02108).
  The system we are modifying; defines the De Morgan interval, composition,
  glueing. Reference implementation: repo **cubicaltt**.
- **chm-hits** — Coquand, Huber, Mörtberg, *On Higher Inductive Types in
  Cubical Type Theory*, LICS 2018.
  [arXiv:1802.01170](https://arxiv.org/abs/1802.01170).
- **huber-canonicity** — Huber, *Canonicity for Cubical Type Theory*,
  J. Autom. Reasoning 2019.
  [arXiv:1607.04156](https://arxiv.org/abs/1607.04156).
  The operational-semantics canonicity proof for CCHM; the baseline our
  Kleene variant must preserve.
- **chs-homotopy-canonicity** — Coquand, Huber, Sattler, *Canonicity and
  homotopy canonicity for cubical type theory*, LMCS.
  [arXiv:1902.06572](https://arxiv.org/abs/1902.06572).
  Distinct from huber-canonicity; sconing-based.
- **orton-pitts** — Orton, Pitts, *Axioms for Modelling Cubical Type Theory
  in a Topos*, CSL 2016 / LMCS.
  [arXiv:1712.04864](https://arxiv.org/abs/1712.04864).
  Axiomatizes what an interval object needs to model the theory — the natural
  frame for checking which axioms the Kleene interval does and doesn't satisfy.
- **cubical-agda** — Vezzosi, Mörtberg, Abel, *Cubical Agda*, ICFP 2019
  (JFP 2021 extended version). Not on arXiv;
  [author PDF](https://staff.math.su.se/anders.mortberg/papers/cubicalagda.pdf)
  fetched to `refs/misc/`. Library:
  [agda/cubical](https://github.com/agda/cubical).

## Cartesian cubical (contrast: no connections/De Morgan structure)

- **cart-cube** — Angiuli, Brunerie, Coquand, Hou (Favonia), Harper,
  Licata (ABCFHL), *Syntax and Models of Cartesian Cubical Type Theory*,
  MSCS 2021. Not on arXiv; the
  [dlicata335/cart-cube](https://github.com/dlicata335/cart-cube) repo
  carries the PDF and an Agda formalization.
- **chtt3-univalent-universes** — Angiuli, Hou (Favonia), Harper,
  *Computational Higher Type Theory III*.
  [arXiv:1712.01800](https://arxiv.org/abs/1712.01800). Closest arXiv
  counterpart of the CSL 2018 "Cartesian Cubical Computational Type Theory"
  paper (which itself is only in LIPIcs).
- **chtt4-inductive-types** — Cavallo, Harper, *CHTT IV: Inductive Types*.
  [arXiv:1801.01568](https://arxiv.org/abs/1801.01568).
- **unifying-cubical-models** — Cavallo, Mörtberg, Swan, *Unifying Cubical
  Models of Univalent Type Theory*, CSL 2020. Not on arXiv;
  [author PDF](https://staff.math.su.se/anders.mortberg/papers/unifying.pdf).
  Parametrizes cubical models over the interval's algebraic structure
  (connection algebras) — directly relevant to swapping in a Kleene algebra.

## Metatheory of normalization

- **sterling-angiuli-normalization** — Sterling, Angiuli, *Normalization for
  Cubical Type Theory*, LICS 2021.
  [arXiv:2101.11479](https://arxiv.org/abs/2101.11479).

## Interval algebra / cube categories

- **buchholtz-morehouse-varieties** — Buchholtz, Morehouse, *Varieties of
  Cubical Sets*, RAMiCS 2017.
  [arXiv:1701.08189](https://arxiv.org/abs/1701.08189).
  Classifies cube categories by the algebraic theory on the interval; the
  natural place to situate a Kleene-lattice interval. nLab's
  ["Kleene algebra"](https://ncatlab.org/nlab/show/Kleene+algebra) page cites
  it for cubical use of Kleene algebras.
- **Literature gap**: no published work was found building cubical type
  theory on a Kleene algebra interval (De Morgan + `x ∧ ¬x ≤ y ∨ ¬y`).
  This variant appears to be novel.

## Implementation technique (Kovács et al.)

- **cctt** — Kovács, efficient CCHM-style evaluator/typechecker:
  [AndrasKovacs/cctt](https://github.com/AndrasKovacs/cctt).
  No paper exists: the README plus the HoTT 2023 talk slides ("Efficient
  Evaluation for Cubical Type Theories") are the technical writeup.
  Our closest starting point.
- **smalltt** — Kovács, demo of fast elaboration for MLTT (glued
  evaluation, metavariables):
  [AndrasKovacs/smalltt](https://github.com/AndrasKovacs/smalltt).
  No paper; README is the writeup.
- **elaboration-zoo** — Kovács, graded elaborator tutorials from
  bare NbE up to first-class implicits:
  [AndrasKovacs/elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo).
- **implicit-fun-elaboration** — Kovács, *Elaboration with
  First-Class Implicit Function Types*, ICFP 2020. Not on arXiv; the
  [AndrasKovacs/implicit-fun-elaboration](https://github.com/AndrasKovacs/implicit-fun-elaboration)
  repo carries the paper source. The fix for cubicaltt's fatal usability gap.
- **kovacs-thesis-signatures** — Kovács, *Type-Theoretic Signatures for
  Algebraic Theories and Inductive Types* (PhD thesis).
  [arXiv:2302.08837](https://arxiv.org/abs/2302.08837).
  Not about cubical evaluation, but relevant to declaratively specifying
  theories and deriving structure from signatures.

## Empty systems, ghcomp, validity

Consult before implementing `hcomp`/`transp` for `Glue`.

- [agda/agda#3415](https://github.com/agda/agda/issues/3415) — Mörtberg
  proposes `ghcomp^i A [φ ↦ u] u₀ := hcomp^i A [φ ↦ u, ¬φ ↦ u₀] u₀`, which
  reduces to `u₀` when `φ = 0` and so never produces an empty system. Used
  in the `∀i.φ` correction of `transp` for `Glue`. Fixed by
  [PR #3540](https://github.com/agda/agda/pull/3540): the `a1` composition
  becomes a `gcomp`, and `equivProof` gains a `(φ = i0) ↦ c` face. Its test
  `Issue3415.agda` checks that `uaβ` holds up to a trivial transport.
- [agda/agda#3583](https://github.com/agda/agda/issues/3583) — empty
  systems still arise from user `hcomp`s whose cofibration is not a
  *valid* one. Validity = the cofibration is a classical tautology
  (`i ∨ ¬i` yes, `i ∧ j` no); the primitives preserve it, so valid inputs
  never yield empty systems. Not enforced by Agda. Non-valid systems can be
  rewritten with `ghcomp`.
- The validity notion is Definition 12 (`def:valid`) of
  **chtt3-univalent-universes** (`refs/tex/chtt3-univalent-universes/meanings.tex`):
  a list of equations `rᵢ = rᵢ'` is valid if some `rᵢ = rᵢ'` holds
  outright, or it contains both `r = 0` and `r = 1` for the same `r`.
- **cubical-agda** §5.2 explains why this needs cofibrations given by
  interval elements `r` (so that `¬r` exists) rather than by the CCHM face
  lattice, where `0_F` has no canonical representative.

## Other

- **tomjack-cubical** — Tom Jack's fork of the Agda cubical library,
  branch `stuff`: [tomjack/cubical](https://github.com/tomjack/cubical/tree/stuff).
  `Stuff/` holds CCHM-style definitions and examples (Eckmann-Hilton as a
  tube, syllepses, the π₃(JS²) and Brunerie-cobordism experiments); the
  source of the symmetric `EH` in the Lean implementation.
- **zhang-demorgan-tutorial** — Tesla Zhang, *A tutorial on implementing
  De Morgan cubical type theory*.
  [arXiv:2210.08232](https://arxiv.org/abs/2210.08232). Third-party
  implementation walkthrough of the De Morgan flavor.
- [*A hands-on introduction to cubicaltt*](https://homotopytypetheory.org/2017/09/16/a-hands-on-introduction-to-cubicaltt/)
  — blog tutorial by Mörtberg, homotopytypetheory.org (2017). Not fetched;
  linked here for completeness.
