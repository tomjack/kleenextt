import Kleenextt.Brunerie

/-! `hlevel n h`: the cube the enclosing path binders ask for, filled in a
type of h-level `n` by `h`, with the boundary read off the binders' types
(kangrongji's `extend`, with the boundary supplied by the elaborator). -/

namespace Kleenextt.HLevel

kdef isSet : Type → Type := λ A => (a b : A) → isProp (Path A a b)
kdef isGroupoid : Type → Type := λ A => (a b : A) → isSet (Path A a b)
kdef is2Groupoid : Type → Type := λ A => (a b : A) → isGroupoid (Path A a b)

-- Weakening, one level at a time: a square in a proposition (cctt's
-- `isProp-isSet`), then by the path types.
kdef isPropIsSet : (A : Type) → isProp A → isSet A :=
  λ A h a b p q => λ j i => hcomp A (λ k => [ (i = 0) ↦ h a a k, (i = 1) ↦ h a b k,
                                              (j = 0) ↦ h a (p i) k, (j = 1) ↦ h a (q i) k ]) a
kdef isSetIsGroupoid : (A : Type) → isSet A → isGroupoid A :=
  λ A h a b => isPropIsSet (Path A a b) (h a b)
kdef isGroupoidIs2Groupoid : (A : Type) → isGroupoid A → is2Groupoid A :=
  λ A h a b => isSetIsGroupoid (Path A a b) (h a b)

kdef ln : (A : Type) (h : isProp A) (a b : A) → Path A a b :=
  λ A h a b => λ i => hlevel 1 h

kdef sq : (A : Type) (h : isSet A) (a b : A) (p q : Path A a b) → Path (Path A a b) p q :=
  λ A h a b p q => λ i j => hlevel 2 h

kdef cube : (A : Type) (h : isGroupoid A) (a b : A) (p q : Path A a b) (r s : Path (Path A a b) p q)
  → Path (Path (Path A a b) p q) r s :=
  λ A h a b p q r s => λ i j k => hlevel 3 h

-- A fibrant binder between the cube's binders and the point.
kdef sqFun : (A B : Type) (h : isSet B) (f g : A → B) (p q : Path (A → B) f g) → Path (Path (A → B) f g) p q :=
  λ A B h f g p q => λ i j => λ x => hlevel 2 h

-- Families over the cube: `lemPropFam'` and `lemSetFam` of the prelude.
kdef lnFam : (A : I → Type) (h : (i : I) → isProp (A i)) (a0 : A 0) (a1 : A 1) → PathP A a0 a1 :=
  λ A h a0 a1 => λ i => hlevel 1 (h i)

kdef sqFam : (A : I → I → Type) (h : (i j : I) → isSet (A i j)) (p0 : (j : I) → A 0 j) (p1 : (j : I) → A 1 j)
  (q0 : PathP (λ i => A i 0) (p0 0) (p1 0)) (q1 : PathP (λ i => A i 1) (p0 1) (p1 1))
  → PathP (λ i => PathP (λ j => A i j) (q0 i) (q1 i)) (λ j => p0 j) (λ j => p1 j) :=
  λ A h p0 p1 q0 q1 => λ i j => hlevel 2 (h i j)

-- The line is `extend₁`: `h a b` with its endpoints corrected.
#kconv (λ (A : Type) (h : isProp A) (a b : A) => ln A h a b)
  = (λ A h a b => λ i => hcomp A (λ j => [(i = 0) ↦ h a a j, (i = 1) ↦ h b b j]) (h a b i))

#kfail (λ (A : Type) (h : isProp A) (a b : A) => λ (i j : I) => hlevel 1 h)

end Kleenextt.HLevel
