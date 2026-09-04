import Kleenextt.Examples.Brunerie

/-! `hlevel n h`: the cube the enclosing path binders ask for, filled in a
type of h-level `n` by `h`, with the boundary read off the binders' types
(kangrongji's `extend`, with the boundary supplied by the elaborator). -/

namespace Kleenextt.Examples.HLevel

kdef isSet : Type → Type := λ A => (a b : A) → isProp (Path A a b)
kdef isGroupoid : Type → Type := λ A => (a b : A) → isSet (Path A a b)
kdef is2Groupoid : Type → Type := λ A => (a b : A) → isGroupoid (Path A a b)

-- Weakening, one level at a time: a square in a proposition (cctt's
-- `isProp-isSet`), then by the path types.
kdef isPropToSet : (A : Type) → isProp A → isSet A :=
  λ A h a b p q => λ j i => hcomp A (λ k => [ (i = 0) ↦ h a a k, (i = 1) ↦ h a b k,
                                              (j = 0) ↦ h a (p i) k, (j = 1) ↦ h a (q i) k ]) a
kdef isSetToGroupoid : (A : Type) → isSet A → isGroupoid A :=
  λ A h a b => isPropToSet (Path A a b) (h a b)
kdef isGroupoidTo2Groupoid : (A : Type) → isGroupoid A → is2Groupoid A :=
  λ A h a b => isSetToGroupoid (Path A a b) (h a b)

-- Being a proposition or a set is a proposition.
kdef isPropIsProp : (A : Type) → isProp (isProp A) :=
  λ A h1 h2 => λ i => λ a b => hlevel 1 (isPropToSet A h1 a b)
kdef isPropIsSet : (A : Type) → isProp (isSet A) :=
  λ A h1 h2 => λ i => λ a b p q => hlevel 1 (isPropToSet (Path A a b) (h1 a b) p q)

-- Closure under Π and Σ, by `hlevel` in the fibres.
kdef isPropPi : (A : Type) (B : A → Type) → ((x : A) → isProp (B x)) → isProp ((x : A) → B x) :=
  λ A B h f g => λ i => λ x => hlevel 1 (h x)
kdef isSetPi : (A : Type) (B : A → Type) → ((x : A) → isSet (B x)) → isSet ((x : A) → B x) :=
  λ A B h f g p q => λ i j => λ x => hlevel 2 (h x)
kdef isSetSigma : (A : Type) (B : A → Type) → isSet A → ((x : A) → isSet (B x)) → isSet ((x : A) × B x) :=
  λ A B hA hB u v p q => λ i j =>
    (hA (fst u) (fst v) (λ i => fst (p i)) (λ i => fst (q i)) i j,
     hlevel 2 (hB (hA (fst u) (fst v) (λ i => fst (p i)) (λ i => fst (q i)) i j)))

-- A retract of a set is a set.
kdef isSetRetract : (A B : Type) (s : A → B) (r : B → A) (h : (a : A) → Path A (r (s a)) a)
  → isSet B → isSet A :=
  λ A B s r h hB a b p q => λ i j =>
    hcomp A (λ k => [ (i = 0) ↦ h (p j) k, (i = 1) ↦ h (q j) k, (j = 0) ↦ h a k, (j = 1) ↦ h b k ])
      (r (hB (s a) (s b) (λ j => s (p j)) (λ j => s (q j)) i j))

kdef isPropRetract : (A B : Type) (s : A → B) (r : B → A) (h : (a : A) → Path A (r (s a)) a)
  → isProp B → isProp A :=
  λ A B s r h hB a b => λ i => hcomp A (λ k => [ (i = 0) ↦ h a k, (i = 1) ↦ h b k ]) (r (hB (s a) (s b) i))

-- `Bool` is a set, by encode-decode into a family of propositions.
kdata Unit := tt
kdata Empty :=

kdef isPropUnit : isProp Unit :=
  λ a b => case a (λ a => Path Unit a b) [ tt ↦ case b (λ b => Path Unit tt b) [ tt ↦ λ _ => tt ] ]
kdef isPropEmpty : isProp Empty := λ a b => case a (λ a => Path Empty a b) []

kdef codeBool : Bool → Bool → Type := λ a b => case a (λ _ => Type)
  [ true ↦ case b (λ _ => Type) [ true ↦ Unit, false ↦ Empty ],
    false ↦ case b (λ _ => Type) [ true ↦ Empty, false ↦ Unit ] ]
kdef isPropCodeBool : (a b : Bool) → isProp (codeBool a b) := λ a b => case a (λ a => isProp (codeBool a b))
  [ true ↦ case b (λ b => isProp (codeBool true b)) [ true ↦ isPropUnit, false ↦ isPropEmpty ],
    false ↦ case b (λ b => isProp (codeBool false b)) [ true ↦ isPropEmpty, false ↦ isPropUnit ] ]
kdef reflCodeBool : (a : Bool) → codeBool a a := λ a => case a (λ a => codeBool a a) [ true ↦ tt, false ↦ tt ]
kdef encodeBool : (a b : Bool) → Path Bool a b → codeBool a b :=
  λ a b p => transport (λ i => codeBool a (p i)) (reflCodeBool a)
kdef decodeBool : (a b : Bool) → codeBool a b → Path Bool a b := λ a b => case a (λ a => codeBool a b → Path Bool a b)
  [ true ↦ case b (λ b => codeBool true b → Path Bool true b)
      [ true ↦ λ _ => refl, false ↦ λ e => case e (λ _ => Path Bool true false) [] ],
    false ↦ case b (λ b => codeBool false b → Path Bool false b)
      [ true ↦ λ e => case e (λ _ => Path Bool false true) [], false ↦ λ _ => refl ] ]
kdef decodeEncodeBool : (a b : Bool) (p : Path Bool a b) → Path (Path Bool a b) (decodeBool a b (encodeBool a b p)) p :=
  λ a b p => J (λ b p => Path (Path Bool a b) (decodeBool a b (encodeBool a b p)) p)
    (case a (λ a => Path (Path Bool a a) (decodeBool a a (encodeBool a a refl)) refl) [ true ↦ refl, false ↦ refl ]) p
kdef isSetBool : isSet Bool :=
  λ a b => isPropRetract (Path Bool a b) (codeBool a b) (encodeBool a b) (decodeBool a b) (decodeEncodeBool a b) (isPropCodeBool a b)

-- Paths in the universe between sets form a set: `Path Type A B` is a
-- retract of `Equiv A B` by `ua`, since `ua (pathToEquiv p) ≡ p`.
kdef JRefl : {A : Type} {a : A} (C : (x : A) → Path A a x → Type) (d : C a refl) → Path (C a refl) (J C d refl) d :=
  λ {A} {a} C d => transportRefl d
kdef uaIdEquiv : (A : Type) → Path (Path Type A A) (ua (idEquiv A)) refl :=
  λ A i j => Glue A [ (i = 1) ↦ (A, idEquiv A), (j = 0) ↦ (A, idEquiv A), (j = 1) ↦ (A, idEquiv A) ]
kdef pathToEquiv : (A B : Type) → Path Type A B → Equiv A B :=
  λ A B p => J (λ B p => Equiv A B) (idEquiv A) p
kdef uaPathToEquiv : (A B : Type) (p : Path Type A B) → Path (Path Type A B) (ua (pathToEquiv A B p)) p :=
  λ A B p => J (λ B p => Path (Path Type A B) (ua (pathToEquiv A B p)) p)
    (let q : Path (Path Type A A) (ua (pathToEquiv A A refl)) (ua (idEquiv A)) :=
       λ i => ua (JRefl (λ B p => Equiv A B) (idEquiv A) i);
     pcomp q (uaIdEquiv A)) p
kdef pathToEquivFst : (A B : Type) (p : Path Type A B) → Path (A → B) (fst (pathToEquiv A B p)) (transport p) :=
  λ A B p => J (λ B p => Path (A → B) (fst (pathToEquiv A B p)) (transport p))
    (let q : Path (A → A) (fst (pathToEquiv A A refl)) (λ x => x) :=
       λ i => fst (JRefl (λ B p => Equiv A B) (idEquiv A) i);
     let r : Path (A → A) (λ x => x) (transport refl) := λ i x => transportRefl x (¬ i);
     pcomp q r) p

kdef isSetEquiv : (A B : Type) → isSet B → isSet (Equiv A B) :=
  λ A B hB => isSetSigma (A → B) (λ f => isEquiv f) (isSetPi A (λ _ => B) (λ _ => hB))
    (λ f => isPropToSet (isEquiv f) (propIsEquivDirect A B f))
kdef isSetPathType : (A B : Type) → isSet B → isSet (Path Type A B) :=
  λ A B hB => isSetRetract (Path Type A B) (Equiv A B) (pathToEquiv A B) (λ e => ua e) (uaPathToEquiv A B) (isSetEquiv A B hB)

-- Equivalences are equal when their functions are; paths in the universe
-- are equal when their transports are.
kdef equivEq : (A B : Type) (e e' : Equiv A B) → Path (A → B) (fst e) (fst e') → Path (Equiv A B) e e' :=
  λ A B e e' p => λ i => (p i, hlevel 1 (propIsEquivDirect A B (p i)))
kdef pathEq : (A B : Type) (p q : Path Type A B) → Path (A → B) (transport p) (transport q) → Path (Path Type A B) p q :=
  λ A B p q h =>
    let ep : Path (Equiv A B) (pathToEquiv A B p) (pathToEquiv A B q) :=
      equivEq A B (pathToEquiv A B p) (pathToEquiv A B q)
        (pcomp (pathToEquivFst A B p) (pcomp h (sym (pathToEquivFst A B q))));
    let uep : Path (Path Type A B) (ua (pathToEquiv A B p)) (ua (pathToEquiv A B q)) := λ i => ua (ep i);
    pcomp (sym (uaPathToEquiv A B p)) (pcomp uep (uaPathToEquiv A B q))

-- The groupoid of sets.
kdef hSet : Type := (X : Type) × isSet X
kdef hSetPath : (X Y : hSet) → Path Type (fst X) (fst Y) → Path hSet X Y :=
  λ X Y p => λ i => (p i, hlevel 1 (isPropIsSet (p i)))
kdef hSetPathRetract : (X Y : hSet) (P : Path hSet X Y) → Path (Path hSet X Y) (hSetPath X Y (λ i => fst (P i))) P :=
  λ X Y P => λ j i => (fst (P i), hlevel 2 (isPropToSet (isSet (fst (P i))) (isPropIsSet (fst (P i)))))
kdef isGroupoidHSet : isGroupoid hSet :=
  λ X Y => isSetRetract (Path hSet X Y) (Path Type (fst X) (fst Y)) (λ P i => fst (P i)) (hSetPath X Y) (hSetPathRetract X Y)
             (isSetPathType (fst X) (fst Y) (snd Y))

-- One level up: the 2-groupoid of groupoids.
kdef isGroupoidPi : (A : Type) (B : A → Type) → ((x : A) → isGroupoid (B x)) → isGroupoid ((x : A) → B x) :=
  λ A B h f g p q r s => λ i j k => λ x => hlevel 3 (h x)
kdef isGroupoidSigma : (A : Type) (B : A → Type) → isGroupoid A → ((x : A) → isGroupoid (B x))
  → isGroupoid ((x : A) × B x) :=
  λ A B hA hB u v p q r s => λ i j k =>
    (hA (fst u) (fst v) (λ i => fst (p i)) (λ i => fst (q i)) (λ i j => fst (r i j)) (λ i j => fst (s i j)) i j k,
     hlevel 3 (hB (hA (fst u) (fst v) (λ i => fst (p i)) (λ i => fst (q i)) (λ i j => fst (r i j)) (λ i j => fst (s i j)) i j k)))
kdef isGroupoidRetract : (A B : Type) (s : A → B) (r : B → A) (h : (a : A) → Path A (r (s a)) a)
  → isGroupoid B → isGroupoid A :=
  λ A B s r h hB a b p q u v => λ i j k =>
    hcomp A (λ l => [ (i = 0) ↦ h (u j k) l, (i = 1) ↦ h (v j k) l, (j = 0) ↦ h (p k) l, (j = 1) ↦ h (q k) l,
                      (k = 0) ↦ h a l, (k = 1) ↦ h b l ])
      (r (hB (s a) (s b) (λ k => s (p k)) (λ k => s (q k)) (λ j k => s (u j k)) (λ j k => s (v j k)) i j k))
kdef isGroupoidEquiv : (A B : Type) → isGroupoid B → isGroupoid (Equiv A B) :=
  λ A B hB => isGroupoidSigma (A → B) (λ f => isEquiv f) (isGroupoidPi A (λ _ => B) (λ _ => hB))
    (λ f => isSetToGroupoid (isEquiv f) (isPropToSet (isEquiv f) (propIsEquivDirect A B f)))
kdef isGroupoidPathType : (A B : Type) → isGroupoid B → isGroupoid (Path Type A B) :=
  λ A B hB => isGroupoidRetract (Path Type A B) (Equiv A B) (pathToEquiv A B) (λ e => ua e) (uaPathToEquiv A B)
    (isGroupoidEquiv A B hB)
kdef isPropIsGroupoid : (A : Type) → isProp (isGroupoid A) :=
  λ A h1 h2 => λ i => λ a b p q r s => hlevel 1 (isPropToSet (Path (Path A a b) p q) (h1 a b p q) r s)
kdef hGroupoid : Type := (X : Type) × isGroupoid X
kdef hGroupoidPath : (X Y : hGroupoid) → Path Type (fst X) (fst Y) → Path hGroupoid X Y :=
  λ X Y p => λ i => (p i, hlevel 1 (isPropIsGroupoid (p i)))
kdef hGroupoidPathRetract : (X Y : hGroupoid) (P : Path hGroupoid X Y)
  → Path (Path hGroupoid X Y) (hGroupoidPath X Y (λ i => fst (P i))) P :=
  λ X Y P => λ j i => (fst (P i), hlevel 2 (isPropToSet (isGroupoid (fst (P i))) (isPropIsGroupoid (fst (P i)))))
kdef is2GroupoidHGroupoid : is2Groupoid hGroupoid :=
  λ X Y => isGroupoidRetract (Path hGroupoid X Y) (Path Type (fst X) (fst Y)) (λ P i => fst (P i))
             (hGroupoidPath X Y) (hGroupoidPathRetract X Y) (isGroupoidPathType (fst X) (fst Y) (snd Y))

-- One more: the 3-groupoid of 2-groupoids.
kdef is3Groupoid : Type → Type := λ A => (a b : A) → is2Groupoid (Path A a b)
kdef is2GroupoidTo3Groupoid : (A : Type) → is2Groupoid A → is3Groupoid A :=
  λ A h a b => isGroupoidTo2Groupoid (Path A a b) (h a b)
kdef isPropIs2Groupoid : (A : Type) → isProp (is2Groupoid A) :=
  λ A h1 h2 => λ i => λ a b p q r s t u =>
    hlevel 1 (isPropToSet (Path (Path (Path A a b) p q) r s) (h1 a b p q r s) t u)
kdef is2GroupoidPi : (A : Type) (B : A → Type) → ((x : A) → is2Groupoid (B x)) → is2Groupoid ((x : A) → B x) :=
  λ A B h f g p q r s t u => λ i j k l => λ x => hlevel 4 (h x)
kdef is2GroupoidSigma : (A : Type) (B : A → Type) → is2Groupoid A → ((x : A) → is2Groupoid (B x))
  → is2Groupoid ((x : A) × B x) :=
  λ A B hA hB u v p q r s t w => λ i j k l =>
    (hA (fst u) (fst v) (λ i => fst (p i)) (λ i => fst (q i)) (λ i j => fst (r i j)) (λ i j => fst (s i j))
       (λ i j k => fst (t i j k)) (λ i j k => fst (w i j k)) i j k l,
     hlevel 4 (hB (hA (fst u) (fst v) (λ i => fst (p i)) (λ i => fst (q i)) (λ i j => fst (r i j)) (λ i j => fst (s i j))
                     (λ i j k => fst (t i j k)) (λ i j k => fst (w i j k)) i j k l)))
kdef is2GroupoidRetract : (A B : Type) (s : A → B) (r : B → A) (h : (a : A) → Path A (r (s a)) a)
  → is2Groupoid B → is2Groupoid A :=
  λ A B s r h hB a b p q u v t w => λ i j k l =>
    hcomp A (λ m => [ (i = 0) ↦ h (t j k l) m, (i = 1) ↦ h (w j k l) m, (j = 0) ↦ h (u k l) m, (j = 1) ↦ h (v k l) m,
                      (k = 0) ↦ h (p l) m, (k = 1) ↦ h (q l) m, (l = 0) ↦ h a m, (l = 1) ↦ h b m ])
      (r (hB (s a) (s b) (λ l => s (p l)) (λ l => s (q l)) (λ k l => s (u k l)) (λ k l => s (v k l))
            (λ j k l => s (t j k l)) (λ j k l => s (w j k l)) i j k l))
kdef is2GroupoidEquiv : (A B : Type) → is2Groupoid B → is2Groupoid (Equiv A B) :=
  λ A B hB => is2GroupoidSigma (A → B) (λ f => isEquiv f) (is2GroupoidPi A (λ _ => B) (λ _ => hB))
    (λ f => isGroupoidTo2Groupoid (isEquiv f) (isSetToGroupoid (isEquiv f) (isPropToSet (isEquiv f) (propIsEquivDirect A B f))))
kdef is2GroupoidPathType : (A B : Type) → is2Groupoid B → is2Groupoid (Path Type A B) :=
  λ A B hB => is2GroupoidRetract (Path Type A B) (Equiv A B) (pathToEquiv A B) (λ e => ua e) (uaPathToEquiv A B)
    (is2GroupoidEquiv A B hB)
kdef h2Groupoid : Type := (X : Type) × is2Groupoid X
kdef h2GroupoidPath : (X Y : h2Groupoid) → Path Type (fst X) (fst Y) → Path h2Groupoid X Y :=
  λ X Y p => λ i => (p i, hlevel 1 (isPropIs2Groupoid (p i)))
kdef h2GroupoidPathRetract : (X Y : h2Groupoid) (P : Path h2Groupoid X Y)
  → Path (Path h2Groupoid X Y) (h2GroupoidPath X Y (λ i => fst (P i))) P :=
  λ X Y P => λ j i => (fst (P i), hlevel 2 (isPropToSet (is2Groupoid (fst (P i))) (isPropIs2Groupoid (fst (P i)))))
kdef is3GroupoidH2Groupoid : is3Groupoid h2Groupoid :=
  λ X Y => is2GroupoidRetract (Path h2Groupoid X Y) (Path Type (fst X) (fst Y)) (λ P i => fst (P i))
             (h2GroupoidPath X Y) (h2GroupoidPathRetract X Y) (is2GroupoidPathType (fst X) (fst Y) (snd Y))

kdef ln : (A : Type) (h : isProp A) (a b : A) → Path A a b :=
  λ A h => h

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

-- With the whole boundary given, the constructions are the obvious terms.
#kconv (λ (A : Type) (h : isProp A) (a b : A) => ln A h a b) = (λ A h a b => h a b)
#kconv (λ (A : Type) (h : isSet A) (a b : A) (p q : Path A a b) => sq A h a b p q) = (λ A h a b p q => h a b p q)
#kconv (λ (A : Type) (B : A → Type) (h : (x : A) → isProp (B x)) (f g : (x : A) → B x) => isPropPi A B h f g)
  = (λ A B h f g => λ i x => h x (f x) (g x) i)

-- Cubes above the level: `h` weakened up to the dimension.
kdef sqProp : (A : Type) (h : isProp A) (a b : A) (p q : Path A a b) → Path (Path A a b) p q :=
  λ A h a b p q => λ i j => hlevel 1 h
kdef cubeContr : (A : Type) (h : isContr A) (a b : A) (p q : Path A a b) (r s : Path (Path A a b) p q)
  → Path (Path (Path A a b) p q) r s :=
  λ A h a b p q r s => λ i j k => hlevel 0 h

#kfail (λ (A : Type) (h : isSet A) (a b : A) => λ (i : I) => hlevel 2 h)

end Kleenextt.Examples.HLevel
