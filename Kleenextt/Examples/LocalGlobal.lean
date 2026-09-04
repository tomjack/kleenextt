import Kleenextt.Examples.Tubes

/-! `Stuff/Pi3JS2/LocalGlobal.agda`: loops of automorphisms of `A` (`Z A`)
against squares of types at `A` (`Ω2 Type A`), `local` by transport and
`global` by `Glue` (Brunerie.lean's), inverse up to a path, and the
naturality of `local` for the Eckmann-Hilton tubes: `local` of `+EH⋆` is
the composite of the two loops and `local` of `-EH⋆` the composite the
other way. -/

namespace Kleenextt.Examples.LocalGlobal
open Tubes

kdef loc : (A : Type) → Ω2 Type A → Z A := λ A P => λ i => λ x => transp (λ j => P i j) (¬ i ∨ i) x

kdef localLemma : (A : Type) (α : Ω2 Type A) (x : A) (p : Ω A x)
  → PathP (λ i => PathP (λ j => α i j) x (p i)) refl refl
  → PathP (λ i => Path A (loc A α i x) (p i)) refl refl :=
  λ A α x p h => λ i j => transp (λ k => α i (k ∨ j)) (¬ i ∨ i ∨ j) (h i j)
kdef globalLemma : (A : Type) (α : Z A) (x : A) (p : Ω A x)
  → PathP (λ i => Path A (α i x) (p i)) refl refl
  → PathP (λ i => PathP (λ j => global A α i j) x (p i)) refl refl :=
  λ A α x p h => λ i j => glue [ (i = 0) ↦ x, (i = 1) ↦ x, (j = 0) ↦ x, (j = 1) ↦ p i ] (h i j)
kdef localGlobalLemma : (A : Type) (α : Z A) (x : A) (p : Ω A x)
  → Path (Ω A x) (λ i => α i x) p → Path (Ω A x) (λ i => loc A (global A α) i x) p :=
  λ A α x p t => λ i j => localLemma A (global A α) x p (globalLemma A α x p (λ i j => t j i)) j i
kdef localGlobal : (A : Type) (α : Z A) → Path (Z A) (loc A (global A α)) α :=
  λ A α => λ t => λ i x => localGlobalLemma A α x (λ i => α i x) refl t i

-- The transport fillers of `local`, forwards from the identity and
-- backwards to it.
kdef localFill' : (A : Type) (P : Ω2 Type A)
  → PathP (λ i => PathP (λ f => A → P i f) (λ x => x) (loc A P i)) (λ _ x => x) (λ _ x => x) :=
  λ A P => λ i j x => transp (λ k => P i (j ∧ k)) (¬ i ∨ i ∨ ¬ j) x
kdef localFill : (A : Type) (α : Ω2 Type A)
  → PathP (λ i => PathP (λ j => α i j → A) (loc A α i) (λ x => x)) (λ i x => x) (λ i x => x) :=
  λ A α => λ i j x => transp (λ k => α i (j ∨ k)) (¬ i ∨ i ∨ j) x

kdef localComm : (A : Type) (P Q : Ω2 Type A) → ext11 (Ω Type A) refl P Q
  → ext11 (A → A) (λ x => x) (loc A P) (loc A Q) :=
  λ A P Q R => λ i j => λ x => transp (λ k => R i j k) ((¬ i ∨ i) ∧ (¬ j ∨ j)) x
kdef localCommFill : (A : Type) (α β : Ω2 Type A) (γ : ext11 (Ω Type A) refl α β)
  → PathP (λ i => PathP (λ j => PathP (λ k => γ i j k → A) (localComm A α β γ i j) (λ x => x))
                          (λ k => localFill A α i k) (λ k => localFill A α i k))
          (λ j k => localFill A β j k) (λ j k => localFill A β j k) :=
  λ A α β γ => λ i j k x => transp (λ l => γ i j (k ∨ l)) (((¬ i ∨ i) ∧ (¬ j ∨ j)) ∨ k) x
kdef localCommFill' : (A : Type) (P Q : Ω2 Type A) (R : ext11 (Ω Type A) refl P Q)
  → PathP (λ i => PathP (λ j => PathP (λ k => A → R i j k) (λ x => x) (localComm A P Q R i j))
                          (localFill' A P i) (localFill' A P i))
          (λ j => localFill' A Q j) (λ j => localFill' A Q j) :=
  λ A P Q R => λ i j k x => transp (λ l => R i j (k ∧ l)) (¬ k ∨ ((¬ i ∨ i) ∧ (¬ j ∨ j))) x

-- The maps above are equivalences, by `hlevel` in the proposition.
kdef localIsEquiv : (A : Type) (α : Ω2 Type A)
  → PathP (λ i => isEquiv (loc A α i)) (snd (idEquiv A)) (snd (idEquiv A)) :=
  λ A α => λ i => hlevel 1 (propIsEquivDirect A A (loc A α i))
kdef localFillIsEquiv : (A : Type) (α : Ω2 Type A)
  → PathP (λ i => PathP (λ j => isEquiv (localFill A α i j)) (localIsEquiv A α i) (snd (idEquiv A)))
          (λ i => snd (idEquiv A)) (λ i => snd (idEquiv A)) :=
  λ A α => λ i j => hlevel 1 (propIsEquivDirect (α i j) A (localFill A α i j))
kdef localCommIsEquiv : (A : Type) (α β : Ω2 Type A) (γ : ext11 (Ω Type A) refl α β)
  → PathP (λ i => PathP (λ j => isEquiv (localComm A α β γ i j)) (localIsEquiv A α i) (localIsEquiv A α i))
          (λ j => localIsEquiv A β j) (λ j => localIsEquiv A β j) :=
  λ A α β γ => λ i j => hlevel 1 (propIsEquivDirect A A (localComm A α β γ i j))
kdef localCommFillIsEquiv : (A : Type) (α β : Ω2 Type A) (γ : ext11 (Ω Type A) refl α β)
  → PathP (λ i => PathP (λ j => PathP (λ k => isEquiv (localCommFill A α β γ i j k))
                                        (localCommIsEquiv A α β γ i j) (snd (idEquiv A)))
                          (λ k => localFillIsEquiv A α i k) (λ k => localFillIsEquiv A α i k))
          (λ j k => localFillIsEquiv A β j k) (λ j k => localFillIsEquiv A β j k) :=
  λ A α β γ => λ i j k => hlevel 1 (propIsEquivDirect (γ i j k) A (localCommFill A α β γ i j k))

-- `globalComm≡`: two `1,1`-extensions of squares of types are equal when
-- their `local`s are.
kdef globalCommEqBridge : (A : Type) (α β : Ω2 Type A) (γ δ : ext11 (Ω Type A) refl α β)
  (ε : Path (ext11 (A → A) (λ x => x) (loc A α) (loc A β)) (localComm A α β γ) (localComm A α β δ))
  → PathP (λ t => PathP (λ i => PathP (λ j => isEquiv (ε t i j)) (localIsEquiv A α i) (localIsEquiv A α i))
                          (λ j => localIsEquiv A β j) (λ j => localIsEquiv A β j))
          (λ i j => localCommIsEquiv A α β γ i j) (λ i j => localCommIsEquiv A α β δ i j) :=
  λ A α β γ δ ε => λ t i j => hlevel 1 (propIsEquivDirect A A (ε t i j))
kdef globalCommEq : (A : Type) (α β : Ω2 Type A) (γ δ : ext11 (Ω Type A) refl α β)
  → Path (ext11 (A → A) (λ x => x) (loc A α) (loc A β)) (localComm A α β γ) (localComm A α β δ)
  → Path (ext11 (Ω Type A) refl α β) γ δ :=
  λ A α β γ δ ε => λ t i j k =>
    Glue A [ (i = 0) ↦ (β j k, localFill A β j k, localFillIsEquiv A β j k),
             (i = 1) ↦ (β j k, localFill A β j k, localFillIsEquiv A β j k),
             (j = 0) ↦ (α i k, localFill A α i k, localFillIsEquiv A α i k),
             (j = 1) ↦ (α i k, localFill A α i k, localFillIsEquiv A α i k),
             (k = 0) ↦ (A, ε t i j, globalCommEqBridge A α β γ δ ε t i j),
             (k = 1) ↦ (A, idEquiv A),
             (t = 0) ↦ (γ i j k, localCommFill A α β γ i j k, localCommFillIsEquiv A α β γ i j k),
             (t = 1) ↦ (δ i j k, localCommFill A α β δ i j k, localCommFillIsEquiv A α β δ i j k) ]

-- `localCommUniq`: `localComm R` is the only `1,1`-extension with a filler
-- from the identity over `R`.
kdef localCommUniq : (A : Type) (P Q : Ω2 Type A) (R : ext11 (Ω Type A) refl P Q)
  (S : ext11 (A → A) (λ x => x) (loc A P) (loc A Q))
  (T : PathP (λ i => PathP (λ j => PathP (λ k => A → R i j k) (λ x => x) (S i j)) (localFill' A P i) (localFill' A P i))
             (λ j => localFill' A Q j) (λ j => localFill' A Q j))
  → Path (ext11 (A → A) (λ x => x) (loc A P) (loc A Q)) (localComm A P Q R) S :=
  λ A P Q R S T => λ t i j =>
    comp (λ l => A → R i j l)
      (λ l => [ (t = 0) ↦ localCommFill' A P Q R i j l, (t = 1) ↦ T i j l,
                (i = 0) ↦ localFill' A Q j l, (i = 1) ↦ localFill' A Q j l,
                (j = 0) ↦ localFill' A P i l, (j = 1) ↦ localFill' A P i l ])
      (λ x => x)

kdef naturalComm : (A : Type) (p q : Z A) → ext11 (A → A) (λ x => x) p q := λ A p q => λ i j => λ x => p i (q j x)
kdef flipNaturalComm : (A : Type) (p q : Z A) → ext11 (A → A) (λ x => x) p q := λ A p q => λ i j => λ x => q j (p i x)

-- `localComm+EHProblem`: `local` of `+EH⋆ P Q` is the composite of the
-- loops. `cancelTransports` is the cube in `A` under the `glueU` element
-- `thing2` of the composition type `+EH⋆ P Q i j k`, with Tom Jack's
-- `erp t x y = (¬t ∧ x) ∨ (t ∧ y) ∨ (x ∧ y)` written out.
kdef cancelTransports : (A : Type) (P Q : Ω2 Type A) (x : A)
  → PathP (λ i => PathP (λ j => PathP (λ k => A) (transport (Q j) x) (transport (sym (P i)) (loc A P i (loc A Q j x))))
                          (λ k => transp (λ l => P i (k ∧ ¬ l)) 0 (localFill' A P i k x))
                          (λ k => transp (λ l => P i (k ∧ ¬ l)) 0 (localFill' A P i k x)))
          (λ j k => transp (λ l => Q j (k ∨ l)) 0 (localFill' A Q j k x))
          (λ j k => transp (λ l => Q j (k ∨ l)) 0 (localFill' A Q j k x)) :=
  λ A P Q x => λ i j k =>
    hcomp A
      (λ h => [ (i = 0) ↦ transp (λ l => Q j (¬ h ∨ (h ∧ (k ∨ l)) ∨ (k ∨ l))) (¬ h ∧ ¬ k)
                            (transp (λ l => Q j ((¬ h ∧ l) ∨ (h ∧ (k ∧ l)) ∨ (l ∧ (k ∧ l))))
                               ((¬ k ∧ h) ∨ (k ∧ (¬ j ∨ j)) ∨ (h ∧ (¬ j ∨ j))) x),
                (i = 1) ↦ transp (λ l => Q j (¬ h ∨ (h ∧ (k ∨ l)) ∨ (k ∨ l))) (¬ h ∧ ¬ k)
                            (transp (λ l => Q j ((¬ h ∧ l) ∨ (h ∧ (k ∧ l)) ∨ (l ∧ (k ∧ l))))
                               ((¬ k ∧ h) ∨ (k ∧ (¬ j ∨ j)) ∨ (h ∧ (¬ j ∨ j))) x),
                (j = 0) ↦ transp (λ l => P i (¬ l ∧ k)) (¬ h ∧ ¬ k)
                            (localFill' A P i k (transp (λ _ => A) ((¬ h ∧ k) ∨ h ∨ k) x)),
                (j = 1) ↦ transp (λ l => P i (¬ l ∧ k)) (¬ h ∧ ¬ k)
                            (localFill' A P i k (transp (λ _ => A) ((¬ h ∧ k) ∨ h ∨ k) x)),
                (k = 0) ↦ transp (λ l => Q j (¬ h ∨ l)) (¬ h) (transp (λ l => Q j (¬ h ∧ l)) h x),
                (k = 1) ↦ transport (sym (P i)) (loc A P i (loc A Q j x)) ])
      (transp (λ l => P i (¬ l ∧ k)) (¬ k)
        (transp (λ l => P i (l ∧ k)) (¬ i ∨ i ∨ ¬ k)
          (transp (λ l => Q j l) (k ∧ (¬ j ∨ j)) x)))
kdef thing2 : (A : Type) (P Q : Ω2 Type A) (x : A)
  → PathP (λ i => PathP (λ j => PathP (λ k => ehPlusStar Type A P Q i j k) x (loc A P i (loc A Q j x)))
                          (λ k => localFill' A P i k x) (λ k => localFill' A P i k x))
          (λ j k => localFill' A Q j k x) (λ j k => localFill' A Q j k x) :=
  λ A P Q x => λ i j k =>
    glueU [ (i = 0) ↦ transp (λ l => Q j (l ∧ k)) (¬ j ∨ j ∨ ¬ k) x, (i = 1) ↦ transp (λ l => Q j (l ∧ k)) (¬ j ∨ j ∨ ¬ k) x,
            (j = 0) ↦ transp (λ l => P i (l ∧ k)) (¬ i ∨ i ∨ ¬ k) x, (j = 1) ↦ transp (λ l => P i (l ∧ k)) (¬ i ∨ i ∨ ¬ k) x,
            (k = 0) ↦ x, (k = 1) ↦ loc A P i (loc A Q j x) ]
      (cancelTransports A P Q x i j k)
kdef localCommPlusEH : (A : Type) (P Q : Ω2 Type A)
  → Path (ext11 (A → A) (λ x => x) (loc A P) (loc A Q))
      (localComm A P Q (ehPlusStar Type A P Q)) (naturalComm A (loc A P) (loc A Q)) :=
  λ A P Q => localCommUniq A P Q (ehPlusStar Type A P Q) (naturalComm A (loc A P) (loc A Q))
    (λ i j k x => thing2 A P Q x i j k)
kdef localCommMinusEH : (A : Type) (P Q : Ω2 Type A)
  → Path (ext11 (A → A) (λ x => x) (loc A P) (loc A Q))
      (localComm A P Q (ehMinusStar Type A P Q)) (flipNaturalComm A (loc A P) (loc A Q)) :=
  λ A P Q => λ t i j => localCommPlusEH A Q P t j i

-- `global≡`: squares of types are equal when their `local`s are.
kdef globalEqBridge : (A : Type) (α β : Ω2 Type A) (eq : Path (Z A) (loc A α) (loc A β))
  → PathP (λ k => PathP (λ i => isEquiv (eq k i)) (snd (idEquiv A)) (snd (idEquiv A)))
          (localIsEquiv A α) (localIsEquiv A β) :=
  λ A α β eq => λ k i => hlevel 1 (propIsEquivDirect A A (eq k i))
kdef globalEq : (A : Type) (α β : Ω2 Type A) → Path (Z A) (loc A α) (loc A β) → Path (Ω2 Type A) α β :=
  λ A α β eq => λ k i j =>
    Glue A [ (i = 0) ↦ (A, idEquiv A), (i = 1) ↦ (A, idEquiv A),
             (j = 0) ↦ (A, eq k i, globalEqBridge A α β eq k i), (j = 1) ↦ (A, idEquiv A),
             (k = 0) ↦ (α i j, localFill A α i j, localFillIsEquiv A α i j),
             (k = 1) ↦ (β i j, localFill A β i j, localFillIsEquiv A β i j) ]
kdef globalLocal : (A : Type) (α : Ω2 Type A) → Path (Ω2 Type A) (global A (loc A α)) α :=
  λ A α => globalEq A (global A (loc A α)) α (localGlobal A (loc A α))

end Kleenextt.Examples.LocalGlobal
