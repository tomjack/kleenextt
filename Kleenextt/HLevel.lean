import Kleenextt.Brunerie

/-! `hlevel n h`: the cube the enclosing path binders ask for, filled in a
type of h-level `n` by `h`, with the boundary read off the binders' types
(kangrongji's `extend`, with the boundary supplied by the elaborator). -/

namespace Kleenextt.HLevel

kdef isSet : Type → Type := λ A => (a b : A) → isProp (Path A a b)
kdef isGroupoid : Type → Type := λ A => (a b : A) → isSet (Path A a b)

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

-- The line is `extend₁`: `h a b` with its endpoints corrected.
#kconv (λ (A : Type) (h : isProp A) (a b : A) => ln A h a b)
  = (λ A h a b => λ i => hcomp A (λ j => [(i = 0) ↦ h a a j, (i = 1) ↦ h b b j]) (h a b i))

#kfail (λ (A : Type) (h : isProp A) (a b : A) => λ (i j : I) => hlevel 1 h)

end Kleenextt.HLevel
