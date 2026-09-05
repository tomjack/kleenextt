import Kleenextt.Examples.HLevel

/-! `S¹/2`, `loop ≡ sym loop`, with its 1-truncation as a constructor
(`Stuff/Pi3JS2/S1Mod2.agda`, `Truncations.agda`). -/

namespace Kleenextt.Examples.S1Mod2

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

-- `rotS¹/2''` and `rotS¹/2'` in one `case`.
kdef rot : (x : S1m2) → Path S1m2 x x :=
  λ x => case x (λ x => Path S1m2 x x)
    [ base ↦ λ l => loop l,
      loop i ↦ λ l => constSquare S1m2 base (λ i => loop i) i l,
      mod2 k i ↦ λ l => hlevel 3 truncS1m2,
      trunc x y p q r s a b c ↦
        hlevel 3 (isSetToGroupoid (Path S1m2 (trunc x y p q r s a b c) (trunc x y p q r s a b c))
                    (truncS1m2 (trunc x y p q r s a b c) (trunc x y p q r s a b c))) ]

-- `Helix/2`: `Bool` twisted by `not`; `loop ≡ sym loop` since both
-- transport as `not`.
kdef notBool : Bool → Bool := λ b => case b (λ _ => Bool) [ true ↦ false, false ↦ true ]
kdef notNot : (b : Bool) → Path Bool (notBool (notBool b)) b :=
  λ b => case b (λ b => Path Bool (notBool (notBool b)) b) [ true ↦ refl, false ↦ refl ]
kdef notEquiv : Equiv Bool Bool := isoToEquiv Bool Bool (notBool, notBool, notNot, notNot)
kdef notEq : Path Type Bool Bool := ua notEquiv

kdef transportSymNotEq : (x : Bool) → Path Bool (transport (sym notEq) x) (notBool x) :=
  λ x => case x (λ x => Path Bool (transport (sym notEq) x) (notBool x)) [ true ↦ refl, false ↦ refl ]
kdef notEqSym : Path (Path Type Bool Bool) notEq (sym notEq) :=
  pathEq Bool Bool notEq (sym notEq) (λ i x => pcomp (uaβ notEquiv x) (sym (transportSymNotEq x)) i)

kdef helix : S1m2 → hSet := λ x => case x (λ _ => hSet)
  [ base ↦ (Bool, isSetBool),
    loop i ↦ (notEq i, hlevel 1 (isPropIsSet (notEq i))),
    mod2 k i ↦ (notEqSym k i, hlevel 2 (isPropToSet (isSet (notEqSym k i)) (isPropIsSet (notEqSym k i)))),
    trunc x y p q r s a b c ↦ hlevel 3 isGroupoidHSet ]

kdef bit : Path S1m2 base base → Bool := λ p => transport (λ i => fst (helix (p i))) false

#kconv (λ (l : I) => rot base l) = (λ l => loop l)

#kconv transport (sym notEq) true = false
#kconv bit (λ i => loop i) = true
#kconv bit (λ i => loop (¬ i)) = true
#kconv bit (λ i => base) = false
#kconv bit (pcomp (λ i => loop i) (λ i => loop i)) = false
#kconv bit (λ i => rot base i) = true
#kconv bit (pcomp (λ i => loop i) (λ i => loop (¬ i))) = false
#kconv bit (pcomp (λ i => loop i) (pcomp (λ i => loop i) (λ i => loop i))) = true

#kconv (λ (B : Type) (h : isGroupoid B) (b : B) (l : Path B b b) (m : Path (Path B b b) l (λ i => l (¬ i))) (i : I)
  => recS1m2 B h b l m (loop i)) = (λ B h b l m i => l i)

end Kleenextt.Examples.S1Mod2
