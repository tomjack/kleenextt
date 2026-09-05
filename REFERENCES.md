# References

Slugs match `scripts/refs.tsv`; `scripts/fetch-refs.sh` downloads everything
into `refs/` (gitignored): arXiv sources under `refs/tex/`, repositories
under `refs/repos/`, loose PDFs under `refs/misc/`. arXiv IDs and "not on
arXiv" claims were checked against the arXiv API on 2026-08-31.

## CCHM-style cubical type theory

- **cchm** — Cohen, Coquand, Huber, Mörtberg, *Cubical Type Theory: a
  constructive interpretation of the univalence axiom*, TYPES 2015.
  [arXiv:1611.02108](https://arxiv.org/abs/1611.02108). The system being
  modified: the De Morgan interval, composition, glueing. Implementation:
  **cubicaltt**.
- **chm-hits** — Coquand, Huber, Mörtberg, *On Higher Inductive Types in
  Cubical Type Theory*, LICS 2018.
  [arXiv:1802.01170](https://arxiv.org/abs/1802.01170).
- **huber-canonicity** — Huber, *Canonicity for Cubical Type Theory*,
  J. Autom. Reasoning 2019.
  [arXiv:1607.04156](https://arxiv.org/abs/1607.04156). Operational
  canonicity for CCHM; what the Kleene variant must preserve.
- **chs-homotopy-canonicity** — Coquand, Huber, Sattler, *Canonicity and
  homotopy canonicity for cubical type theory*, LMCS.
  [arXiv:1902.06572](https://arxiv.org/abs/1902.06572). Sconing-based.
- **orton-pitts** — Orton, Pitts, *Axioms for Modelling Cubical Type Theory
  in a Topos*, CSL 2016 / LMCS.
  [arXiv:1712.04864](https://arxiv.org/abs/1712.04864). The frame for
  checking which axioms the Kleene interval satisfies.
- **cubical-agda** — Vezzosi, Mörtberg, Abel, *Cubical Agda*, ICFP 2019
  (JFP 2021 extended version). Not on arXiv;
  [author PDF](https://staff.math.su.se/anders.mortberg/papers/cubicalagda.pdf).
  Library: [agda/cubical](https://github.com/agda/cubical).

## Cartesian cubical (no connections)

- **cart-cube** — Angiuli, Brunerie, Coquand, Hou (Favonia), Harper, Licata
  (ABCFHL), *Syntax and Models of Cartesian Cubical Type Theory*, MSCS 2021.
  Not on arXiv;
  [dlicata335/cart-cube](https://github.com/dlicata335/cart-cube) has the
  PDF and an Agda formalization.
- **chtt3-univalent-universes** — Angiuli, Hou (Favonia), Harper,
  *Computational Higher Type Theory III*.
  [arXiv:1712.01800](https://arxiv.org/abs/1712.01800). Closest arXiv
  counterpart of the CSL 2018 "Cartesian Cubical Computational Type Theory"
  paper, which is only in LIPIcs.
- **chtt4-inductive-types** — Cavallo, Harper, *CHTT IV: Inductive Types*.
  [arXiv:1801.01568](https://arxiv.org/abs/1801.01568).
- **unifying-cubical-models** — Cavallo, Mörtberg, Swan, *Unifying Cubical
  Models of Univalent Type Theory*, CSL 2020. Not on arXiv;
  [author PDF](https://staff.math.su.se/anders.mortberg/papers/unifying.pdf).
  Parametrizes cubical models over the interval's algebraic structure.

## Normalization

- **sterling-angiuli-normalization** — Sterling, Angiuli, *Normalization for
  Cubical Type Theory*, LICS 2021.
  [arXiv:2101.11479](https://arxiv.org/abs/2101.11479).

## Interval algebra

- **buchholtz-morehouse-varieties** — Buchholtz, Morehouse, *Varieties of
  Cubical Sets*, RAMiCS 2017.
  [arXiv:1701.08189](https://arxiv.org/abs/1701.08189). Classifies cube
  categories by the algebraic theory on the interval; nLab's
  ["Kleene algebra"](https://ncatlab.org/nlab/show/Kleene+algebra) cites it
  for the cubical use of Kleene algebras.
- No published work was found building cubical type theory on a Kleene
  algebra interval.

## Implementation technique (Kovács)

- **cctt** — efficient CCHM-style evaluator and typechecker:
  [AndrasKovacs/cctt](https://github.com/AndrasKovacs/cctt). No paper; the
  README and the HoTT 2023 slides ("Efficient Evaluation for Cubical Type
  Theories") are the writeup. The closest starting point.
- **smalltt** — fast elaboration for MLTT (glued evaluation, metavariables):
  [AndrasKovacs/smalltt](https://github.com/AndrasKovacs/smalltt). README
  only.
- **elaboration-zoo** — graded elaborator tutorials up to first-class
  implicits:
  [AndrasKovacs/elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo).
- **implicit-fun-elaboration** — *Elaboration with First-Class Implicit
  Function Types*, ICFP 2020. Not on arXiv; the
  [repository](https://github.com/AndrasKovacs/implicit-fun-elaboration)
  has the paper source.
- **kovacs-thesis-signatures** — *Type-Theoretic Signatures for Algebraic
  Theories and Inductive Types*, PhD thesis.
  [arXiv:2302.08837](https://arxiv.org/abs/2302.08837). Declarative
  specification of theories and derivation from signatures.

## Empty systems, ghcomp, validity

- [agda/agda#3415](https://github.com/agda/agda/issues/3415) — Mörtberg's
  `ghcomp^i A [φ ↦ u] u₀ := hcomp^i A [φ ↦ u, ¬φ ↦ u₀] u₀` reduces to `u₀`
  when `φ = 0`, so never produces an empty system; used in the `∀i.φ`
  correction of `transp` for `Glue`. Fixed by
  [PR #3540](https://github.com/agda/agda/pull/3540): the `a1` composition
  becomes a `gcomp` and `equivProof` gains a `(φ = i0) ↦ c` face; its test
  `Issue3415.agda` checks `uaβ` up to a trivial transport.
- [agda/agda#3583](https://github.com/agda/agda/issues/3583) — empty systems
  still arise from user `hcomp`s whose cofibration is not *valid*, a
  classical tautology (`i ∨ ¬i` yes, `i ∧ j` no); the primitives preserve
  validity. Not enforced by Agda; non-valid systems can be rewritten with
  `ghcomp`.
- Validity is Definition 12 (`def:valid`) of **chtt3-univalent-universes**
  (`refs/tex/chtt3-univalent-universes/meanings.tex`): a list of equations
  `rᵢ = rᵢ'` is valid if one holds outright, or it contains both `r = 0`
  and `r = 1` for the same `r`.
- **cubical-agda** §5.2: this needs cofibrations given by interval elements
  `r` (so that `¬r` exists) rather than the CCHM face lattice, where `0_F`
  has no canonical representative.

## Other

- **tomjack-cubical** — Tom Jack's fork of the Agda cubical library, branch
  `stuff`: [tomjack/cubical](https://github.com/tomjack/cubical/tree/stuff).
  `Stuff/` has the CCHM-style definitions the examples port (Eckmann-Hilton
  as a tube, syllepses, π₃(JS²), the Brunerie cobordism), and the symmetric
  `EH`.
- **zhang-demorgan-tutorial** — Tesla Zhang, *A tutorial on implementing De
  Morgan cubical type theory*.
  [arXiv:2210.08232](https://arxiv.org/abs/2210.08232).
- [*A hands-on introduction to cubicaltt*](https://homotopytypetheory.org/2017/09/16/a-hands-on-introduction-to-cubicaltt/),
  Mörtberg, 2017. Not fetched.
