import Kleenextt.HLevel

/-! `S¹/2`, the circle with `loop ≡ sym loop`, with its 1-truncation built
into the type as a constructor (`Stuff/Pi3JS2/S1Mod2.agda` and
`Truncations.agda`, in one HIT): the recursor and eliminator fill the
truncation case by `hlevel`. -/

namespace Kleenextt.S1Mod2

open HLevel

kdata S1m2 := base
  | loop (i : I) [ (i = 0) ↦ base, (i = 1) ↦ base ]
  | mod2 (k i : I) [ (k = 0) ↦ loop i, (k = 1) ↦ loop (¬ i), (i = 0) ↦ base, (i = 1) ↦ base ]
  | trunc (x y : S1m2) (p q : Path S1m2 x y) (r s : Path (Path S1m2 x y) p q) (a b c : I)
      [ (a = 0) ↦ r b c, (a = 1) ↦ s b c, (b = 0) ↦ p c, (b = 1) ↦ q c, (c = 0) ↦ x, (c = 1) ↦ y ]

kdef truncS1m2 : isGroupoid S1m2 := λ x y p q r s => λ a b c => trunc x y p q r s a b c

kdef recS1m2 : (B : Type) (h : isGroupoid B) (b : B) (l : Path B b b)
  (m : Path (Path B b b) l (λ i => l (¬ i))) → S1m2 → B :=
  λ B h b l m x => case x (λ _ => B)
    [ base ↦ b, loop i ↦ l i, mod2 k i ↦ m k i, trunc x y p q r s a b' c ↦ hlevel 3 h ]

kdef elimS1m2 : (P : S1m2 → Type) (lev : (x : S1m2) → isGroupoid (P x)) (b : P base)
  (l : PathP (λ i => P (loop i)) b b)
  (m : PathP (λ k => PathP (λ i => P (mod2 k i)) b b) l (λ i => l (¬ i)))
  → (x : S1m2) → P x :=
  λ P lev b l m x => case x P
    [ base ↦ b, loop i ↦ l i, mod2 k i ↦ m k i,
      trunc x y p q r s a b' c ↦ hlevel 3 (lev (trunc x y p q r s a b' c)) ]

-- `rotS¹/2`: the rotation loop at every point (`rotS¹/2''` and its
-- extension over the truncation, `rotS¹/2'`, in one case). The `mod2`
-- case is Agda's `extendGroupoid` cube, the `trunc` case fills in the path
-- type, a set, weakened to a groupoid.
kdef rot : (x : S1m2) → Path S1m2 x x :=
  λ x => case x (λ x => Path S1m2 x x)
    [ base ↦ λ l => loop l,
      loop i ↦ λ l => constSquare S1m2 base (λ i => loop i) i l,
      mod2 k i ↦ λ l => hlevel 3 truncS1m2,
      trunc x y p q r s a b c ↦
        hlevel 3 (isSetToGroupoid (Path S1m2 (trunc x y p q r s a b c) (trunc x y p q r s a b c))
                    (truncS1m2 (trunc x y p q r s a b c) (trunc x y p q r s a b c))) ]

#kconv (λ (l : I) => rot base l) = (λ l => loop l)

#kconv (λ (B : Type) (h : isGroupoid B) (b : B) (l : Path B b b) (m : Path (Path B b b) l (λ i => l (¬ i))) (i : I)
  => recS1m2 B h b l m (loop i)) = (λ B h b l m i => l i)

end Kleenextt.S1Mod2
