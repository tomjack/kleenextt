# References

Slugs match `scripts/refs.tsv`; `scripts/fetch-refs.sh` downloads everything
into `refs/` (gitignored). IDs checked against the arXiv API on 2026-08-31,
publication data against doi.org and dblp on 2026-09-05.

## CCHM

- **cchm** — Cyril Cohen, Thierry Coquand, Simon Huber, and Anders Mörtberg.
  *Cubical Type Theory: A Constructive Interpretation of the Univalence
  Axiom*. In *21st International Conference on Types for Proofs and Programs
  (TYPES 2015)*, LIPIcs 69, pp. 5:1–5:34. Schloss Dagstuhl, 2018.
  [doi:10.4230/LIPIcs.TYPES.2015.5](https://doi.org/10.4230/LIPIcs.TYPES.2015.5),
  [arXiv:1611.02108](https://arxiv.org/abs/1611.02108). Implementation:
  **cubicaltt**.
- **chm-hits** — Thierry Coquand, Simon Huber, and Anders Mörtberg. *On
  Higher Inductive Types in Cubical Type Theory*. In *33rd Annual ACM/IEEE
  Symposium on Logic in Computer Science (LICS 2018)*, pp. 255–264. ACM,
  2018. [doi:10.1145/3209108.3209197](https://doi.org/10.1145/3209108.3209197),
  [arXiv:1802.01170](https://arxiv.org/abs/1802.01170).
- **huber-canonicity** — Simon Huber. *Canonicity for Cubical Type Theory*.
  Journal of Automated Reasoning 63(2), pp. 173–210, 2019.
  [doi:10.1007/s10817-018-9469-1](https://doi.org/10.1007/s10817-018-9469-1),
  [arXiv:1607.04156](https://arxiv.org/abs/1607.04156). What the Kleene
  variant must preserve.
- **chs-homotopy-canonicity** — Thierry Coquand, Simon Huber, and Christian
  Sattler. *Canonicity and Homotopy Canonicity for Cubical Type Theory*.
  Logical Methods in Computer Science 18(1), article 28, 2022.
  [doi:10.46298/lmcs-18(1:28)2022](https://doi.org/10.46298/lmcs-18(1:28)2022),
  [arXiv:1902.06572](https://arxiv.org/abs/1902.06572). Conference version:
  *Homotopy Canonicity for Cubical Type Theory*, in *4th International
  Conference on Formal Structures for Computation and Deduction (FSCD 2019)*,
  LIPIcs 131, pp. 11:1–11:23. Schloss Dagstuhl, 2019.
  [doi:10.4230/LIPIcs.FSCD.2019.11](https://doi.org/10.4230/LIPIcs.FSCD.2019.11).
- **orton-pitts** — Ian Orton and Andrew M. Pitts. *Axioms for Modelling
  Cubical Type Theory in a Topos*. Logical Methods in Computer Science 14(4),
  article 23, 2018.
  [doi:10.23638/LMCS-14(4:23)2018](https://doi.org/10.23638/LMCS-14(4:23)2018),
  [arXiv:1712.04864](https://arxiv.org/abs/1712.04864). Conference version
  in *25th EACSL Annual Conference on Computer Science Logic (CSL 2016)*,
  LIPIcs 62, pp. 24:1–24:19. Schloss Dagstuhl, 2016.
  [doi:10.4230/LIPIcs.CSL.2016.24](https://doi.org/10.4230/LIPIcs.CSL.2016.24).
  The frame for checking which axioms the Kleene interval satisfies.
- **cubical-agda** — Andrea Vezzosi, Anders Mörtberg, and Andreas Abel.
  *Cubical Agda: A Dependently Typed Programming Language with Univalence and
  Higher Inductive Types*. Proceedings of the ACM on Programming Languages
  3(ICFP), article 87, 2019.
  [doi:10.1145/3341691](https://doi.org/10.1145/3341691),
  [PDF](https://staff.math.su.se/anders.mortberg/papers/cubicalagda.pdf).
  Extended version: Journal of Functional Programming 31, article e8, 2021.
  [doi:10.1017/S0956796821000034](https://doi.org/10.1017/S0956796821000034).
  Library: [agda/cubical](https://github.com/agda/cubical).

## Cartesian

- **cart-cube** — Carlo Angiuli, Guillaume Brunerie, Thierry Coquand, Robert
  Harper, Kuen-Bang Hou (Favonia), and Daniel R. Licata. *Syntax and Models
  of Cartesian Cubical Type Theory*. Mathematical Structures in Computer
  Science 31(4), pp. 424–468, 2021.
  [doi:10.1017/S0960129521000347](https://doi.org/10.1017/S0960129521000347).
  Preprint, PDF and Agda formalization:
  [dlicata335/cart-cube](https://github.com/dlicata335/cart-cube).
- **chtt3-univalent-universes** — Carlo Angiuli, Kuen-Bang Hou (Favonia), and
  Robert Harper. *Computational Higher Type Theory III: Univalent Universes
  and Exact Equality*. Preprint, 2017.
  [arXiv:1712.01800](https://arxiv.org/abs/1712.01800). Conference version:
  *Cartesian Cubical Computational Type Theory: Constructive Reasoning with
  Paths and Equalities*, in *27th EACSL Annual Conference on Computer Science
  Logic (CSL 2018)*, LIPIcs 119, pp. 6:1–6:17. Schloss Dagstuhl, 2018.
  [doi:10.4230/LIPIcs.CSL.2018.6](https://doi.org/10.4230/LIPIcs.CSL.2018.6).
- **chtt4-inductive-types** — Evan Cavallo and Robert Harper. *Computational
  Higher Type Theory IV: Inductive Types*. Preprint, 2018.
  [arXiv:1801.01568](https://arxiv.org/abs/1801.01568). Conference version:
  *Higher Inductive Types in Cubical Computational Type Theory*, Proceedings
  of the ACM on Programming Languages 3(POPL), article 1, 2019.
  [doi:10.1145/3290314](https://doi.org/10.1145/3290314).
- **unifying-cubical-models** — Evan Cavallo, Anders Mörtberg, and Andrew W
  Swan. *Unifying Cubical Models of Univalent Type Theory*. In *28th EACSL
  Annual Conference on Computer Science Logic (CSL 2020)*, LIPIcs 152,
  pp. 14:1–14:17. Schloss Dagstuhl, 2020.
  [doi:10.4230/LIPIcs.CSL.2020.14](https://doi.org/10.4230/LIPIcs.CSL.2020.14),
  [PDF](https://staff.math.su.se/anders.mortberg/papers/unifying.pdf).
  Models parametrized over the interval's algebraic structure.
- **sterling-angiuli-normalization** — Jonathan Sterling and Carlo Angiuli.
  *Normalization for Cubical Type Theory*. In *36th Annual ACM/IEEE Symposium
  on Logic in Computer Science (LICS 2021)*, pp. 1–15. IEEE, 2021.
  [doi:10.1109/LICS52264.2021.9470719](https://doi.org/10.1109/LICS52264.2021.9470719),
  [arXiv:2101.11479](https://arxiv.org/abs/2101.11479).

## Interval algebra

- **buchholtz-morehouse-varieties** — Ulrik Buchholtz and Edward Morehouse.
  *Varieties of Cubical Sets*. In Peter Höfner, Damien Pous, and Georg Struth
  (eds.), *Relational and Algebraic Methods in Computer Science (RAMiCS
  2017)*, LNCS 10226, pp. 77–92. Springer, 2017.
  [doi:10.1007/978-3-319-57418-9_5](https://doi.org/10.1007/978-3-319-57418-9_5),
  [arXiv:1701.08189](https://arxiv.org/abs/1701.08189). Cube categories by
  the algebraic theory on the interval; cited by nLab's
  ["Kleene algebra"](https://ncatlab.org/nlab/show/Kleene+algebra).
- No published work found on a Kleene algebra interval.

## Kovács

- **cctt** — András Kovács. *cctt: high-performance cubical evaluation*.
  Software, [AndrasKovacs/cctt](https://github.com/AndrasKovacs/cctt). The
  README and the slides are the writeup: András Kovács, Evan Cavallo, Tom
  Jack, and Anders Mörtberg, *Efficient Evaluation for Cubical Type
  Theories*, talk at the 2nd International Conference on Homotopy Type Theory
  (HoTT 2023), Pittsburgh, 24 May 2023.
  [Slides](https://andraskovacs.github.io/pdfs/hott23prez.pdf). The starting
  point.
- **smalltt** — András Kovács. *smalltt: demo for high-performance type
  theory elaboration*. Software,
  [AndrasKovacs/smalltt](https://github.com/AndrasKovacs/smalltt).
- **elaboration-zoo** — András Kovács. *elaboration-zoo: minimal
  implementations for dependent type checking and elaboration*. Software,
  [AndrasKovacs/elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo).
- **implicit-fun-elaboration** — András Kovács. *Elaboration with First-Class
  Implicit Function Types*. Proceedings of the ACM on Programming Languages
  4(ICFP), article 101, 2020.
  [doi:10.1145/3408983](https://doi.org/10.1145/3408983).
  [Repository](https://github.com/AndrasKovacs/implicit-fun-elaboration).
- **kovacs-thesis-signatures** — András Kovács. *Type-Theoretic Signatures
  for Algebraic Theories and Inductive Types*. PhD thesis, Eötvös Loránd
  University, 2022.
  [doi:10.15476/ELTE.2022.070](https://doi.org/10.15476/ELTE.2022.070),
  [arXiv:2302.08837](https://arxiv.org/abs/2302.08837).

## Empty systems, ghcomp, validity

- Anders Mörtberg. *Add ghcomp to get rid of empty systems in cubical agda*.
  [agda/agda#3415](https://github.com/agda/agda/issues/3415), 2018. His
  `ghcomp^i A [φ ↦ u] u₀ := hcomp^i A [φ ↦ u, ¬φ ↦ u₀] u₀`, which is `u₀`
  when `φ = 0`; fixed by *Implement "ghcomp" for cubical mode*,
  [agda/agda#3540](https://github.com/agda/agda/pull/3540), 2019 (`a1`
  becomes a `gcomp`, `equivProof` gains a `(φ = i0) ↦ c` face).
- *Empty systems still exist in cubical agda*.
  [agda/agda#3583](https://github.com/agda/agda/issues/3583), 2019. Empty
  systems from user `hcomp`s whose cofibration is not valid (a classical
  tautology); the primitives preserve validity. Not enforced by Agda.
- Validity is Definition 12 of **chtt3-univalent-universes**
  (`meanings.tex`). **cubical-agda** §5.2: cofibrations must be interval
  elements (so `¬r` exists), not the CCHM face lattice.

## Other

- **tomjack-cubical** — Tom Jack. *cubical*, branch `stuff`. Software,
  [tomjack/cubical](https://github.com/tomjack/cubical/tree/stuff):
  `Stuff/` has the definitions the examples port.
- **zhang-demorgan-tutorial** — Tesla Zhang. *A Tutorial on Implementing De
  Morgan Cubical Type Theory*. Preprint, 2022.
  [arXiv:2210.08232](https://arxiv.org/abs/2210.08232).
- Anders Mörtberg. *A Hands-on Introduction to cubicaltt*. Homotopy Type
  Theory blog, 16 September 2017.
  [homotopytypetheory.org](https://homotopytypetheory.org/2017/09/16/a-hands-on-introduction-to-cubicaltt/).
