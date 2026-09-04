import Kleenextt.HLevel

/-! Tom Jack's tubes (`Stuff/Pi3JS2/Tubes.agda`, `Extensions.agda`): a tube
is a partial element on the boundary of a cube, varying along `x`; its path
of types is the cube type with that boundary at `x`, composing along it
takes a cube with the boundary at `0` to one with the boundary at `1`, and
the star is the composition of the constant cube. -/

namespace Kleenextt.Tubes

-- `(α,β)`-extensions: an `n`-cube of `α`s whose faces in the other
-- directions are `β`.
kdef ext11 : (A : Type) (a : A) (α β : Ω A a) → Type :=
  λ A a α β => PathP (λ i => PathP (λ j => A) (α i) (α i)) β β
kdef ext22 : (A : Type) (a : A) (α β : Ω2 A a) → Type := λ A a α β =>
  PathP (λ i => PathP (λ j => PathP (λ a => PathP (λ b => A) (α i j) (α i j)) refl refl)
                  (λ a b => β a b) (λ a b => β a b))
    refl refl

-- `CSQ`: squares with `α` on the left and bottom and `β` on the right and
-- top; composing backwards along the tube gives a loop at `y`.
kdef csqFront : (A : Type) (x y z : A) (α : Path A x y) (β : Path A y z) → Type :=
  λ A x y z α β => PathP (λ i => PathP (λ j => A) (α i) (β i)) (λ j => α j) (λ j => β j)
kdef csqCompInv : (A : Type) (x y z : A) (α : Path A x y) (β : Path A y z) → csqFront A x y z α β → Ω2 A y :=
  λ A x y z α β r => λ i j =>
    hcomp A (λ k => [ (i = 0) ↦ α (j ∨ k), (i = 1) ↦ β (j ∧ ¬ k), (j = 0) ↦ α (i ∨ k), (j = 1) ↦ β (i ∧ ¬ k) ]) (r i j)

-- `+EH`, `-EH`: the tubes of the two Eckmann-Hilton compositions, from
-- `Ω³` to the `1,1`-extensions of `α` and `β` in `Ω`.
kdef ehPlusPath : (A : Type) (a : A) (α β : Ω2 A a) (x : I) → Type := λ A a α β x =>
  PathP (λ i => PathP (λ k => PathP (λ y => A) (β k (¬ x)) (α i x)) (λ y => α i (x ∧ y)) (λ y => α i (x ∧ y)))
    (λ k y => β k (¬ x ∨ y)) (λ k y => β k (¬ x ∨ y))
kdef ehPlusFill : (A : Type) (a : A) (α β : Ω2 A a) (x : I) → ehPlusPath A a α β x :=
  λ A a α β x => λ i k y =>
    hfill A (λ x => [ (i = 0) ↦ β k (¬ x ∨ y), (i = 1) ↦ β k (¬ x ∨ y), (k = 0) ↦ α i (x ∧ y), (k = 1) ↦ α i (x ∧ y),
                      (y = 0) ↦ β k (¬ x), (y = 1) ↦ α i x ]) a x
kdef ehPlusStar : (A : Type) (a : A) (α β : Ω2 A a) → ext11 (Ω A a) refl α β :=
  λ A a α β => λ i k y =>
    hcomp A (λ x => [ (i = 0) ↦ β k (¬ x ∨ y), (i = 1) ↦ β k (¬ x ∨ y), (k = 0) ↦ α i (x ∧ y), (k = 1) ↦ α i (x ∧ y),
                      (y = 0) ↦ β k (¬ x), (y = 1) ↦ α i x ]) a

kdef ehMinusPath : (A : Type) (a : A) (α β : Ω2 A a) (x : I) → Type := λ A a α β x =>
  PathP (λ i => PathP (λ k => PathP (λ y => A) (α i (¬ x)) (β k x)) (λ y => α i (¬ x ∨ y)) (λ y => α i (¬ x ∨ y)))
    (λ k y => β k (x ∧ y)) (λ k y => β k (x ∧ y))
kdef ehMinusFill : (A : Type) (a : A) (α β : Ω2 A a) (x : I) → ehMinusPath A a α β x :=
  λ A a α β x => λ i k y =>
    hfill A (λ x => [ (i = 0) ↦ β k (x ∧ y), (i = 1) ↦ β k (x ∧ y), (k = 0) ↦ α i (¬ x ∨ y), (k = 1) ↦ α i (¬ x ∨ y),
                      (y = 0) ↦ α i (¬ x), (y = 1) ↦ β k x ]) a x
kdef ehMinusStar : (A : Type) (a : A) (α β : Ω2 A a) → ext11 (Ω A a) refl α β :=
  λ A a α β => λ i k y =>
    hcomp A (λ x => [ (i = 0) ↦ β k (x ∧ y), (i = 1) ↦ β k (x ∧ y), (k = 0) ↦ α i (¬ x ∨ y), (k = 1) ↦ α i (¬ x ∨ y),
                      (y = 0) ↦ α i (¬ x), (y = 1) ↦ β k x ]) a

-- `EH'⋆`: the Eckmann-Hilton square composed from `α` itself.
kdef ehPrimeStar : (A : Type) (a : A) (α β : Ω2 A a) → ext11 (Ω A a) refl α β :=
  λ A a α β => λ i k y =>
    hcomp A (λ x => [ (i = 0) ↦ β k (y ∧ x), (i = 1) ↦ β k (y ∧ x), (k = 0) ↦ α i y, (k = 1) ↦ α i y,
                      (y = 0) ↦ a, (y = 1) ↦ β k x ]) (α i y)

-- `η`: the Hopf map on a generator, `CSQ← p p (EH'⋆ p p)`.
kdef eta : (A : Type) (a : A) (p : Ω2 A a) → Ω3 A a :=
  λ A a p => csqCompInv (Ω A a) refl refl refl p p (ehPrimeStar A a p p)

-- `2,2-diag-inv`: a `2,2`-extension from a diagonal `d` with paths from
-- the constant cube to it along the `-EH` and `+EH` tubes.
kdef diagInv22 : (A : Type) (a : A) (α β : Ω2 A a) (d : ext11 (Ω A a) refl α β)
  (q : PathP (λ f => ehMinusPath A a α β f) refl d) (r : PathP (λ f => ehPlusPath A a α β f) refl d)
  → ext22 A a α β :=
  λ A a α β d q r => λ i y k z =>
    hcomp A (λ x => [ (i = 0) ↦ β k (z ∧ (¬ y ∨ x)), (i = 1) ↦ β k (z ∧ (¬ y ∨ x)), (y = 0) ↦ β k z, (y = 1) ↦ q z i k x,
                      (k = 0) ↦ α i (y ∧ (¬ z ∨ x)), (k = 1) ↦ α i (y ∧ (¬ z ∨ x)), (z = 0) ↦ α i y, (z = 1) ↦ r y i k x ])
      (hcomp A (λ x => [ (i = 0) ↦ β k (¬ y ∧ z ∧ x), (i = 1) ↦ β k (¬ y ∧ z ∧ x), (y = 0) ↦ β k (z ∧ x), (y = 1) ↦ α i (¬ z ∧ x),
                         (k = 0) ↦ α i (y ∧ ¬ z ∧ x), (k = 1) ↦ α i (y ∧ ¬ z ∧ x), (z = 0) ↦ α i (y ∧ x), (z = 1) ↦ β k (¬ y ∧ x) ])
         a)

-- The function underlying `2,2-diag-corollary2`: a path from `+EH⋆` to
-- `-EH⋆` gives a `2,2`-extension, with `-EH⋆` as the diagonal.
kdef extFromPath : (A : Type) (a : A) (α β : Ω2 A a)
  → Path (ext11 (Ω A a) refl α β) (ehPlusStar A a α β) (ehMinusStar A a α β) → ext22 A a α β :=
  λ A a α β e => diagInv22 A a α β (ehMinusStar A a α β) (λ f => ehMinusFill A a α β f)
    (λ f => hcomp (ehPlusPath A a α β f) (λ x => [ (f = 0) ↦ ehPlusFill A a α β 0, (f = 1) ↦ e x ])
              (ehPlusFill A a α β f))

end Kleenextt.Tubes
