# References

Slugs match `scripts/refs.tsv`; `scripts/fetch-refs.sh` downloads everything
into `refs/` (gitignored). IDs checked against the arXiv API on 2026-08-31.

## CCHM

- **cchm** — Cohen, Coquand, Huber, Mörtberg, *Cubical Type Theory: a
  constructive interpretation of the univalence axiom*.
  [arXiv:1611.02108](https://arxiv.org/abs/1611.02108). Implementation:
  **cubicaltt**.
- **chm-hits** — Coquand, Huber, Mörtberg, *On Higher Inductive Types in
  Cubical Type Theory*. [arXiv:1802.01170](https://arxiv.org/abs/1802.01170).
- **huber-canonicity** — Huber, *Canonicity for Cubical Type Theory*.
  [arXiv:1607.04156](https://arxiv.org/abs/1607.04156). What the Kleene
  variant must preserve.
- **chs-homotopy-canonicity** — Coquand, Huber, Sattler, *Canonicity and
  homotopy canonicity for cubical type theory*.
  [arXiv:1902.06572](https://arxiv.org/abs/1902.06572).
- **orton-pitts** — Orton, Pitts, *Axioms for Modelling Cubical Type Theory
  in a Topos*. [arXiv:1712.04864](https://arxiv.org/abs/1712.04864). The
  frame for checking which axioms the Kleene interval satisfies.
- **cubical-agda** — Vezzosi, Mörtberg, Abel, *Cubical Agda*.
  [PDF](https://staff.math.su.se/anders.mortberg/papers/cubicalagda.pdf);
  library [agda/cubical](https://github.com/agda/cubical).

## Cartesian

- **cart-cube** — ABCFHL, *Syntax and Models of Cartesian Cubical Type
  Theory*. [dlicata335/cart-cube](https://github.com/dlicata335/cart-cube)
  (PDF and Agda formalization).
- **chtt3-univalent-universes** — Angiuli, Hou (Favonia), Harper,
  *Computational Higher Type Theory III*.
  [arXiv:1712.01800](https://arxiv.org/abs/1712.01800).
- **chtt4-inductive-types** — Cavallo, Harper, *CHTT IV: Inductive Types*.
  [arXiv:1801.01568](https://arxiv.org/abs/1801.01568).
- **unifying-cubical-models** — Cavallo, Mörtberg, Swan, *Unifying Cubical
  Models of Univalent Type Theory*.
  [PDF](https://staff.math.su.se/anders.mortberg/papers/unifying.pdf).
  Models parametrized over the interval's algebraic structure.
- **sterling-angiuli-normalization** — Sterling, Angiuli, *Normalization for
  Cubical Type Theory*. [arXiv:2101.11479](https://arxiv.org/abs/2101.11479).

## Interval algebra

- **buchholtz-morehouse-varieties** — Buchholtz, Morehouse, *Varieties of
  Cubical Sets*. [arXiv:1701.08189](https://arxiv.org/abs/1701.08189). Cube
  categories by the algebraic theory on the interval; cited by nLab's
  ["Kleene algebra"](https://ncatlab.org/nlab/show/Kleene+algebra).
- No published work found on a Kleene algebra interval.

## Kovács

- **cctt** — [AndrasKovacs/cctt](https://github.com/AndrasKovacs/cctt); the
  README and the HoTT 2023 slides are the writeup. The starting point.
- **smalltt** — [AndrasKovacs/smalltt](https://github.com/AndrasKovacs/smalltt).
- **elaboration-zoo** —
  [AndrasKovacs/elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo).
- **implicit-fun-elaboration** — *Elaboration with First-Class Implicit
  Function Types*, ICFP 2020.
  [Repository](https://github.com/AndrasKovacs/implicit-fun-elaboration).
- **kovacs-thesis-signatures** — *Type-Theoretic Signatures for Algebraic
  Theories and Inductive Types*.
  [arXiv:2302.08837](https://arxiv.org/abs/2302.08837).

## Empty systems, ghcomp, validity

- [agda/agda#3415](https://github.com/agda/agda/issues/3415): Mörtberg's
  `ghcomp^i A [φ ↦ u] u₀ := hcomp^i A [φ ↦ u, ¬φ ↦ u₀] u₀`, which is `u₀`
  when `φ = 0`; fixed by [PR #3540](https://github.com/agda/agda/pull/3540)
  (`a1` becomes a `gcomp`, `equivProof` gains a `(φ = i0) ↦ c` face).
- [agda/agda#3583](https://github.com/agda/agda/issues/3583): empty systems
  from user `hcomp`s whose cofibration is not valid (a classical tautology);
  the primitives preserve validity. Not enforced by Agda.
- Validity is Definition 12 of **chtt3-univalent-universes**
  (`meanings.tex`). **cubical-agda** §5.2: cofibrations must be interval
  elements (so `¬r` exists), not the CCHM face lattice.

## Other

- **tomjack-cubical** —
  [tomjack/cubical](https://github.com/tomjack/cubical/tree/stuff), branch
  `stuff`: `Stuff/` has the definitions the examples port.
- **zhang-demorgan-tutorial** — Tesla Zhang, *A tutorial on implementing De
  Morgan cubical type theory*.
  [arXiv:2210.08232](https://arxiv.org/abs/2210.08232).
- [*A hands-on introduction to cubicaltt*](https://homotopytypetheory.org/2017/09/16/a-hands-on-introduction-to-cubicaltt/),
  Mörtberg.
