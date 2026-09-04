import Kleenextt.S1Mod2

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

#kconv (λ (B : Type) (h : is2Groupoid B) (b : B) (sf : Path (Path B b b) refl refl)
  (m : Path (Path (Path B b b) refl refl) sf (λ i j => sf j i)) (i j : I)
  => recS2m2 B h b sf m (surf i j)) = (λ B h b sf m i j => sf i j)

end Kleenextt.S2Mod2
