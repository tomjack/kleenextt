import Kleenextt.Examples.J2S2

/-! `π₄(S³)` is nontrivial: the Hopf generator `η loop3` of `Ω⁴S³` is not
`refl`. The invariant is `bit` after `Ω⁴S³ → Ω³J₂S²`, transport along the
3-cube of types over `loop3` rotating `J₂S²` by its surfaces (cctt's `hope`
without its cheats): `J₂S²` carries its 4-truncation as a constructor, so
its surfaces over `surf₂` are one `hlevel`, and the family lands in the
2-groupoids. Not in the default build: `lake build Kleenextt.Examples.Pi4S3`
computes the invariant on the generator to `true` in 250 s and 11 GB
(3.9M `hcomp`s). -/

namespace Kleenextt.Examples.Pi4S3

open HLevel S2Mod2 Tubes LocalGlobal J2S2

kdata S3 := base3
  | loop3 (i j k : I) [ (i = 0) ↦ base3, (i = 1) ↦ base3, (j = 0) ↦ base3, (j = 1) ↦ base3,
                        (k = 0) ↦ base3, (k = 1) ↦ base3 ]
kdef Ω4 : (A : Type) → A → Type := λ A x => Ω (Ω3 A x) refl
kdef Z2 : Type → Type := λ A => Ω2 (A → A) (λ x => x)

kdata J2S2t := tjbase
  | tjsurf (i j : I) [ (i = 0) ↦ tjbase, (i = 1) ↦ tjbase, (j = 0) ↦ tjbase, (j = 1) ↦ tjbase ]
  | tjsurfsurf (i j a b : I) [ (i = 0) ↦ tjsurf a b, (i = 1) ↦ tjsurf a b, (j = 0) ↦ tjsurf a b, (j = 1) ↦ tjsurf a b,
                               (a = 0) ↦ tjsurf i j, (a = 1) ↦ tjsurf i j, (b = 0) ↦ tjsurf i j, (b = 1) ↦ tjsurf i j ]
  | jtrunc (x y : J2S2t) (p q : Path J2S2t x y) (r s : Path (Path J2S2t x y) p q)
      (t u : Path (Path (Path J2S2t x y) p q) r s) (v w : Path (Path (Path (Path J2S2t x y) p q) r s) t u)
      (a b c d e : I)
      [ (a = 0) ↦ v b c d e, (a = 1) ↦ w b c d e, (b = 0) ↦ t c d e, (b = 1) ↦ u c d e,
        (c = 0) ↦ r d e, (c = 1) ↦ s d e, (d = 0) ↦ p e, (d = 1) ↦ q e, (e = 0) ↦ x, (e = 1) ↦ y ]
kdef truncJ : is3Groupoid J2S2t := λ x y p q r s t u v w => λ a b c d e => jtrunc x y p q r s t u v w a b c d e

kdef surfsJ : (x : J2S2t) → Ω2 J2S2t x := λ x => case x (λ x => Ω2 J2S2t x)
  [ tjbase ↦ λ k l => tjsurf k l, tjsurf i j ↦ λ k l => tjsurfsurf i j k l,
    tjsurfsurf i j a b ↦ λ k l => hlevel 5 truncJ,
    jtrunc x y p q r s t u v w a b c d e ↦ λ k l => hlevel 5 truncJ ]

-- The family over the truncated `J₂S²`, as over `J₂S²` but into the
-- 2-groupoids, so that the truncation case is a cube by `hlevel`.
kdef is2GroupoidPair : is2Groupoid PairT :=
  is2GroupoidSigma S1t (λ _ => S2m2) (isGroupoidTo2Groupoid S1t truncS1t) (λ _ => truncS2m2)
kdef funPt : J2S2t → h2Groupoid := λ x => case x (λ _ => h2Groupoid)
  [ tjbase ↦ (PairT, is2GroupoidPair),
    tjsurf i j ↦ (globalRL i j, hlevel 1 (isPropIs2Groupoid (globalRL i j))),
    tjsurfsurf i j a b ↦ (gnarly i j a b, hlevel 1 (isPropIs2Groupoid (gnarly i j a b))),
    jtrunc x y p q r s t u v w a b c d e ↦ hlevel 5 is3GroupoidH2Groupoid ]
kdef fun1t : Ω J2S2t tjbase → PairT := λ p => transport (λ i => fst (funPt (p i))) (tbase, sbase)
kdef fun2t : Ω3 J2S2t tjbase → Ω2 S2m2 sbase := λ p => λ i j => snd (fun1t (λ k => p i j k))
kdef bit3t : Ω3 J2S2t tjbase → Bool := λ p => bit2 (fun2t p)

#kconv bit3t (eta J2S2t tjbase (λ i j => tjsurf i j)) = true

-- The 3-cube of types over `loop3`: `J₂S²` rotated by its surfaces.
kdef rot2Equiv : (A : Type) (h : Z2 A) → PathP (λ i => PathP (λ j => Equiv A A) (idEquiv A) (idEquiv A)) refl refl :=
  λ A h => λ i j => (λ x => h i j x, hlevel 1 (propIsEquivDirect A A (λ x => h i j x)))
kdef global3 : (A : Type) (h : Z2 A) → Ω3 Type A :=
  λ A h i j k => Glue A [ (i = 0) ↦ (A, idEquiv A), (i = 1) ↦ (A, idEquiv A), (j = 0) ↦ (A, idEquiv A),
                          (j = 1) ↦ (A, idEquiv A), (k = 0) ↦ (A, rot2Equiv A h i j), (k = 1) ↦ (A, idEquiv A) ]
kdef codeS3 : S3 → Type := λ x => case x (λ _ => Type)
  [ base3 ↦ J2S2t, loop3 i j k ↦ global3 J2S2t (λ i j => λ x => surfsJ x i j) i j k ]
kdef toJ : Ω S3 base3 → J2S2t := λ p => transport (λ i => codeS3 (p i)) tjbase

kdef genπ4S3 : Ω4 S3 base3 := eta (Ω S3 base3) refl (λ i j k => loop3 i j k)
kdef π4Invariant : Ω4 S3 base3 → Bool := λ q => bit3t (λ i j k => toJ (q i j k))

-- Checking this computes the invariant on the generator.
kdef trueNeFalse : Path Bool true false → Empty := λ e => transport (λ i => codeBool true (e i)) tt
kdef π4S3Nontrivial : Path (Ω4 S3 base3) genπ4S3 refl → Empty := λ e => trueNeFalse (λ t => π4Invariant (e t))

end Kleenextt.Examples.Pi4S3
