# kleenextt

This is an experimental implementation of a "Kleene CCHM" cubical type
theory: the cubical type theory of Cohen, Coquand, Huber, and Mörtberg
[CCHM], with the interval taken to be the free Kleene algebra rather
than the free De Morgan algebra, as suggested in the remark in §2 of
the paper.

[CCHM]: "Cubical Type Theory: a constructive interpretation of the
univalence axiom", 2016. arXiv:1611.02108

## Implementation

Tier 2 of NOTES.md (the interval theory) in Lean 4: interval expressions,
evaluation into a finite algebra, and a decision procedure for the equational
theory of the variety that algebra generates. The Kleene interval is the
instance at the three-element Kleene algebra, stock CCHM's De Morgan interval
the instance at the four-element De Morgan algebra — the theory is one
swappable value.

`Kleenextt/Tests.lean` checks the expected (in)equations at compile time;
`lake build` runs everything.
