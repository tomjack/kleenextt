import Kleenextt.Prelude

/-! Cubical tests: paths over the Kleene interval, composition, Booleans, the
circle, and computation through univalence. -/

namespace Kleenextt.Cubical
open Kleenextt.Prelude

-- Paths and connections.
#kconv (λ (A : Type) (x : A) => sym (refl {A} {x})) = (λ A x => refl)
#kconv (λ (A : Type) (x y : A) (p : Path A x y) => sym (sym p)) = (λ A x y p => p)
#kconv (λ (A : Type) (x y : A) (p : Path A x y) (i : I) => p (i ∧ 1)) = (λ A x y p i => p i)
#kconv (λ (A : Type) (x y : A) (p : Path A x y) (i j : I) => p (i ∧ j)) = (λ A x y p i j => p (j ∧ i))

-- The Kleene inequality `i ∧ ¬i ≤ j ∨ ¬j` holds definitionally; the interval
-- is still not Boolean.
#kconv (λ (A : Type) (x y : A) (p : Path A x y) (i j : I) => p (i ∧ ¬ i ∧ (j ∨ ¬ j)))
  = (λ A x y p i j => p (i ∧ ¬ i))
#kdiffer (λ (A : Type) (x y : A) (p : Path A x y) (i : I) => p (i ∧ ¬ i)) = (λ A x y p i => x)
#kdiffer (λ (A : Type) (x y : A) (p : Path A x y) (i j : I) => p (i ∧ ¬ i)) = (λ A x y p i j => p (j ∧ ¬ j))

-- Path endpoints are checked.
kdef the : (A : Type) → A → A := λ A x => x
#kfail λ (A : Type) (x y : A) (p : Path A x y) => the (Path A y x) (λ i => p i)
kdef pathEnds : {A : Type} {x y : A} (p : Path A x y) → Path A x y := λ p i => p i

-- Composition of paths, filling, and the boundary of the filler.
#kconv (λ (A : Type) (x y : A) (p : Path A x y) => pcomp p refl) = (λ A x y p i => hcomp A (λ j => [ (i = 0) ↦ x, (i = 1) ↦ y ]) (p i))
#kconv (λ (A : Type) (x : A) (i : I) => hfill A (λ j => [ (i = 0) ↦ x ]) x 0) = (λ A x i => x)
#kfail λ (A : Type) (x y : A) (p : Path A x y) (i : I) => hcomp A (λ j => [ (i = 0) ↦ y ]) (p i)

-- A system emptied by substitution: at `i = 1` the face `(i = 0)` vanishes.
-- `hcomp` is then stuck at a neutral type; `ghcomp` reduces to the base
-- (agda/agda#3415).
#kdiffer (λ (A : Type) (x : A) => (λ (i : I) => hcomp A (λ j => [ (i = 0) ↦ x ]) x) 1) = (λ A x => x)
#kconv (λ (A : Type) (x : A) => (λ (i : I) => ghcomp A (λ j => [ (i = 0) ↦ x ]) x) 1) = (λ A x => x)

-- Booleans are a strict inductive type: transport and composition compute.
kdef not : Bool → Bool := λ b => Bool.elim (λ _ => Bool) false true b
#kconv not (not true) = true
#kconv transport (λ _ => Bool) true = true
#kconv (λ (i : I) => hcomp Bool (λ j => [ (i = 0) ↦ true, (i = 1) ↦ true ]) true) = (λ i => true)

-- The circle: `loop` is a path, and the eliminator computes on it.
kdef loopPath : Path S1 base base := λ i => loop i
#kconv loop 0 = base
kdef helix : Equiv Bool Bool → S1 → Type := λ e => S1.elim (λ _ => Type) Bool (λ i => ua e i)
#kconv (λ (e : Equiv Bool Bool) => helix e base) = (λ e => Bool)
#kconv (λ (e : Equiv Bool Bool) (i : I) => helix e (loop i)) = (λ e i => ua e i)

-- Univalence computes: transport along `ua e` is the function of `e`, on the
-- nose for Booleans and up to `transportRefl` in general.
#kconv (λ (e : Equiv Bool Bool) => transport (ua e) true) = (λ e => fst e true)
#kconv transport (ua (idEquiv Bool)) false = false
#kconv (λ (e : Equiv Bool Bool) => transport (λ i => helix e (loop i)) true) = (λ e => fst e true)

-- Going around the circle twice: composition in the universe (`hcomp` at
-- `Type` reduces to a `Glue` along `lineToEquiv`) followed by transport.
kdef loop2 : Path S1 base base := pcomp loopPath loopPath
#kconv (λ (e : Equiv Bool Bool) => transport (λ i => helix e (loop2 i)) true) = (λ e => fst e (fst e true))

-- Transport along a partial `ua` path: the `∀i.φ` case of `transp` for
-- `Glue`, with a non-trivial constancy cofibration. Its unglueing connects
-- the function of the equivalence to the full transport.
kdef uaFiller : {A B : Type} (e : Equiv A B) (x : A) → Path B (fst e x) (transport (ua e) x) :=
  λ {A} {B} e x i => unglue (transp (λ j => ua e (i ∧ j)) (¬ i) x)

end Kleenextt.Cubical
