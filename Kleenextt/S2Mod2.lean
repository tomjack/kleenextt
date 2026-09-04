import Kleenextt.S1Mod2
import Kleenextt.Tubes

/-! `S²/2`, the sphere with `surf ≡ flip surf`, with its 2-truncation built
in as a 4-dimensional constructor (`Stuff/Pi3JS2/S2Mod2.agda`). -/

namespace Kleenextt.S2Mod2

open HLevel

kdata S2m2 := base
  | surf (i j : I) [ (i = 0) ↦ base, (i = 1) ↦ base, (j = 0) ↦ base, (j = 1) ↦ base ]
  | mod2 (k i j : I) [ (k = 0) ↦ surf i j, (k = 1) ↦ surf j i,
                       (i = 0) ↦ base, (i = 1) ↦ base, (j = 0) ↦ base, (j = 1) ↦ base ]
  | trunc (x y : S2m2) (p q : Path S2m2 x y) (r s : Path (Path S2m2 x y) p q)
      (t u : Path (Path (Path S2m2 x y) p q) r s) (a b c d : I)
      [ (a = 0) ↦ t b c d, (a = 1) ↦ u b c d, (b = 0) ↦ r c d, (b = 1) ↦ s c d,
        (c = 0) ↦ p d, (c = 1) ↦ q d, (d = 0) ↦ x, (d = 1) ↦ y ]

kdef truncS2m2 : is2Groupoid S2m2 := λ x y p q r s t u => λ a b c d => trunc x y p q r s t u a b c d

kdef recS2m2 : (B : Type) (h : is2Groupoid B) (b : B) (sf : Path (Path B b b) refl refl)
  (m : Path (Path (Path B b b) refl refl) sf (λ i j => sf j i)) → S2m2 → B :=
  λ B h b sf m x => case x (λ _ => B)
    [ base ↦ b, surf i j ↦ sf i j, mod2 k i j ↦ m k i j,
      trunc x y p q r s t u a b' c d ↦ hlevel 4 h ]

kdef elimS2m2 : (P : S2m2 → Type) (lev : (x : S2m2) → is2Groupoid (P x)) (b : P base)
  (sf : PathP (λ i => PathP (λ j => P (surf i j)) b b) refl refl)
  (m : PathP (λ k => PathP (λ i => PathP (λ j => P (mod2 k i j)) b b) refl refl) sf (λ i j => sf j i))
  → (x : S2m2) → P x :=
  λ P lev b sf m x => case x P
    [ base ↦ b, surf i j ↦ sf i j, mod2 k i j ↦ m k i j,
      trunc x y p q r s t u a b' c d ↦ hlevel 4 (lev (trunc x y p q r s t u a b' c d)) ]

-- `surfs∥S²/2∥₂-lemma1`: the `2,2`-extension of `surf` by itself.
kdef surfsLemma1 : ext22 S2m2 base (λ i j => surf i j) (λ a b => surf a b) :=
  λ i j a b => hlevel 4 truncS2m2

-- The surfaces at every point (`surfs∥S²/2∥₂`): `Ω² S2m2 x` is a set,
-- weakened to the dimension of each cube.
kdef surfsLemma2 : PathP (λ k => PathP (λ i => PathP (λ j => Ω2 S2m2 (mod2 k i j)) (λ a b => surf a b) (λ a b => surf a b))
                            refl refl)
    (λ i j => surfsLemma1 i j) (λ i j => surfsLemma1 j i) :=
  λ k i j => hlevel 3 (isSetToGroupoid (Ω2 S2m2 (mod2 k i j)) (truncS2m2 (mod2 k i j) (mod2 k i j) refl refl))
kdef surfs : (x : S2m2) → Ω2 S2m2 x := λ x => case x (λ x => Ω2 S2m2 x)
  [ base ↦ λ a b => surf a b, surf i j ↦ surfsLemma1 i j, mod2 k i j ↦ surfsLemma2 k i j,
    trunc x y p q r s t u a b c d ↦
      hlevel 4 (isGroupoidTo2Groupoid (Ω2 S2m2 (trunc x y p q r s t u a b c d))
                 (isSetToGroupoid (Ω2 S2m2 (trunc x y p q r s t u a b c d))
                   (truncS2m2 (trunc x y p q r s t u a b c d) (trunc x y p q r s t u a b c d) refl refl))) ]

#kconv (λ (a b : I) => surfs base a b) = (λ a b => surf a b)

-- `thingy`: at every point, the surface equals its flip (`THINGY-base`,
-- `THINGY-surf`, `THINGY-mod2`, `thingy'`); the 5- and 6-cubes are above
-- the level of `S2m2`, and the truncation case fills a 4-cube in a
-- proposition.
kdef thingyBase : Path (Ω2 S2m2 base) (λ a b => surf b a) (λ a b => surf a b) := λ t a b => mod2 (¬ t) a b
kdef thingySurf : PathP (λ i => PathP (λ j => Path (Ω2 S2m2 (surf i j)) (λ a b => surfsLemma1 i j b a) (surfsLemma1 i j))
                          thingyBase thingyBase) refl refl :=
  λ i j t a b => hlevel 4 truncS2m2
kdef thingyMod2 : PathP (λ k => PathP (λ i => PathP (λ j => Path (Ω2 S2m2 (mod2 k i j))
                                                       (λ a b => surfsLemma2 k i j b a) (surfsLemma2 k i j))
                                        (λ t a b => mod2 (¬ t) a b) (λ t a b => mod2 (¬ t) a b))
                          (λ j t a b => mod2 (¬ t) a b) (λ j t a b => mod2 (¬ t) a b))
    (λ i j => thingySurf i j) (λ i j => thingySurf j i) :=
  λ k i j t a b => hlevel 4 truncS2m2
kdef thingy : (y : S2m2) → Path (Ω2 S2m2 y) (λ i j => surfs y j i) (λ i j => surfs y i j) :=
  λ y => case y (λ y => Path (Ω2 S2m2 y) (λ i j => surfs y j i) (λ i j => surfs y i j))
    [ base ↦ thingyBase, surf i j ↦ thingySurf i j, mod2 k i j ↦ thingyMod2 k i j,
      trunc x y p q r s t u a b c d ↦
        hlevel 1 (truncS2m2 (trunc x y p q r s t u a b c d) (trunc x y p q r s t u a b c d) refl refl
                    (λ i j => surfs (trunc x y p q r s t u a b c d) j i)
                    (λ i j => surfs (trunc x y p q r s t u a b c d) i j)) ]

#kconv (λ (t a b : I) => thingy base t a b) = (λ t a b => mod2 (¬ t) a b)

#kconv (λ (B : Type) (h : is2Groupoid B) (b : B) (sf : Path (Path B b b) refl refl)
  (m : Path (Path (Path B b b) refl refl) sf (λ i j => sf j i)) (i j : I)
  => recS2m2 B h b sf m (surf i j)) = (λ B h b sf m i j => sf i j)

end Kleenextt.S2Mod2
