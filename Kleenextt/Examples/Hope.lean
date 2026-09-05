import Kleenextt.Examples.Brunerie

/-! The rest of cctt's `brunerie_james_revised.cctt`. Not in the default
build. -/

namespace Kleenextt.Examples.Brunerie
open Prelude

kdef Ω4 : (A : Type) → A → Type := λ A x => Ω (Ω3 A x) refl
kdef isSet : Type → Type := λ A => (a b : A) → isProp (Path A a b)

kdef squareConnAnd : (A : Type) (x : A) (p : Ω2 A x)
  → PathP (λ i => PathP (λ j => Path A x (p i j)) refl (λ k => p i k)) refl refl :=
  λ A x p i j k => p i (j ∧ k)

-- tomjack/cubical's symmetric `EH` (`Stuff/BrunerieCobordism.agda`), `erp`
-- unfolded; cctt's costs the same on `generator`.
kdef EH : (A : Type) (x : A) (p q : Ω2 A x) → PathP (λ i => Path (Path A x x) (p i) (p i)) q q :=
  λ A x p q i j k => hcomp A (λ f => [ (i = 0) ↦ q j (f ∧ k), (i = 1) ↦ q j (f ∧ k), (k = 1) ↦ q j f,
                                       (j = 0) ↦ p i (¬ f ∨ k), (j = 1) ↦ p i (¬ f ∨ k), (k = 0) ↦ p i (¬ f) ]) x

kdef csqInv : (A : Type) (x y z : A) (p : Path A x y) (q : Path A y z) (r : PathP (λ i => Path A (p i) (q i)) p q)
  → Ω2 A y :=
  λ A x y z p q r i j =>
  let pface : (m k : I) → A := λ m k => hcom 1 m A (λ l => [ (k = 0) ↦ p l, (k = 1) ↦ y ]) y;
  let qface : (m k : I) → A := λ m k => hcom 0 m A (λ l => [ (k = 0) ↦ q l, (k = 1) ↦ y ]) y;
  hcom 0 1 A (λ l => [ (i = 0) ↦ pface j l, (i = 1) ↦ qface j l, (j = 0) ↦ pface i l, (j = 1) ↦ qface i l ]) (r i j)

kdef hopf : (A : Type) (x : A) (p : Ω2 A x) → Ω3 A x :=
  λ A x p => csqInv (Ω A x) refl refl refl p p (EH A x p p)

kdef generatorS2 : Ω3 S2 base2 := hopf S2 base2 (λ i j => loop2 i j)
kdef generator : Int := writhe generatorS2
kdef generatorflip : Int := writhe (hopf S2 base2 (λ i j => loop2 j i))

#ktime generator
#ktime generatorflip

kdef fromPathPPath : (A : I → Type) (a0 : A 0) (a1 : A 1)
  → Path Type (PathP A a0 a1) (Path (A 1) (coe 0 1 (λ i => A i) a0) a1) :=
  λ A a0 a1 i => PathP (λ j => A (i ∨ j)) (coe 0 i (λ j => A j) a0) a1

kdef isPropSquareSet : (A : I → I → Type) (Aset : (i j : I) → isSet (A i j))
  (p0 : (j : I) → A 0 j) (p1 : (j : I) → A 1 j)
  (q0 : PathP (λ i => A i 0) (p0 0) (p1 0)) (q1 : PathP (λ i => A i 1) (p0 1) (p1 1)) (i : I)
  → isProp (PathP (λ j => A i j) (q0 i) (q1 i)) :=
  λ A Aset p0 p1 q0 q1 i =>
    coe 1 0 (λ t => isProp (fromPathPPath (λ j => A i j) (q0 i) (q1 i) t))
      (Aset i 1 (coe 0 1 (λ j => A i j) (q0 i)) (q1 i))

kdef lemPropFam' : (A : I → Type) (Aprop : (i : I) → isProp (A i)) (a0 : A 0) (a1 : A 1) → PathP A a0 a1 :=
  λ A Aprop a0 a1 i => Aprop i (coe 0 i (λ i => A i) a0) (coe 1 i (λ i => A i) a1) i

kdef lemSetFam : (A : I → I → Type) (Aset : (i j : I) → isSet (A i j))
  (p0 : (j : I) → A 0 j) (p1 : (j : I) → A 1 j)
  (q0 : PathP (λ i => A i 0) (p0 0) (p1 0)) (q1 : PathP (λ i => A i 1) (p0 1) (p1 1))
  → PathP (λ i => PathP (λ j => A i j) (q0 i) (q1 i)) (λ j => p0 j) (λ j => p1 j) :=
  λ A Aset p0 p1 q0 q1 =>
    lemPropFam' (λ i => PathP (λ j => A i j) (q0 i) (q1 i)) (λ i => isPropSquareSet A Aset p0 p1 q0 q1 i)
      (λ j => p0 j) (λ j => p1 j)

kdef isPropIsSet : (A : Type) → isProp A → isSet A :=
  λ A h a b p q j i => hcomp A (λ l => [ (i = 0) ↦ h a a l, (i = 1) ↦ h a b l, (j = 0) ↦ h a (p i) l, (j = 1) ↦ h a (q i) l ]) a

kdef Z2 : Type → Type := λ A => Ω2 (A → A) (λ x => x)

kdef rot2IsEquiv : (A : Type) (h : Z2 A) (i j : I) → isEquiv (λ x => h i j x) :=
  λ A h i j =>
    lemSetFam (λ i j => isEquiv (h i j))
      (λ i j => isPropIsSet (isEquiv (λ x => h i j x)) (propIsEquivDirect A A (λ x => h i j x)))
      (λ j => snd (idEquiv A)) (λ j => snd (idEquiv A)) (λ i => snd (idEquiv A)) (λ i => snd (idEquiv A)) i j

kdef rot2Equiv : (A : Type) (h : Z2 A) (i j : I) → Equiv A A := λ A h i j => (λ x => h i j x, rot2IsEquiv A h i j)

kdef global3 : (A : Type) (h : Z2 A) → Ω3 Type A :=
  λ A h i j k => Glue A [ (i = 0) ↦ (A, idEquiv A), (i = 1) ↦ (A, idEquiv A), (j = 0) ↦ (A, idEquiv A),
                          (j = 1) ↦ (A, idEquiv A), (k = 0) ↦ (A, rot2Equiv A h i j), (k = 1) ↦ (A, idEquiv A) ]

kdata S3 := base3 | loop3 (i j k : I) [ (i = 0) ↦ base3, (i = 1) ↦ base3, (j = 0) ↦ base3, (j = 1) ↦ base3,
                                        (k = 0) ↦ base3, (k = 1) ↦ base3 ]

kdata J2S2 := jbase
  | jsurf (i j : I) [ (i = 0) ↦ jbase, (i = 1) ↦ jbase, (j = 0) ↦ jbase, (j = 1) ↦ jbase ]
  | jsurfsurf (i j a b : I) [ (i = 0) ↦ jsurf a b, (i = 1) ↦ jsurf a b, (j = 0) ↦ jsurf a b, (j = 1) ↦ jsurf a b,
                              (a = 0) ↦ jsurf i j, (a = 1) ↦ jsurf i j, (b = 0) ↦ jsurf i j, (b = 1) ↦ jsurf i j ]

-- The truncation is cheated again.
kdef surfsJ2S2 : (x : J2S2) → Ω2 J2S2 x :=
  λ x => case x (λ x => Ω2 J2S2 x)
    [ jbase ↦ λ k l => jsurf k l, jsurf i j ↦ λ k l => jsurfsurf i j k l, jsurfsurf i j a b ↦ sorry ]

kdef toJ2S2 : Ω S3 base3 → J2S2 :=
  let F : S3 → Type := λ x => case x (λ _ => Type)
    [ base3 ↦ J2S2, loop3 i j k ↦ global3 J2S2 (λ i j x => surfsJ2S2 x i j) i j k ];
  λ p => coe 0 1 (λ i => F (p i)) jbase

kdef genπ4S3 : Ω4 S3 base3 := hopf (Ω S3 base3) refl (λ i j k => loop3 i j k)

kdef ouch : Ω3 J2S2 jbase := λ i j k => toJ2S2 (genπ4S3 i j k)

kdef terribleCheat : J2S2 → S2 :=
  λ x => case x (λ _ => S2) [ jbase ↦ base2, jsurf i j ↦ loop2 i j, jsurfsurf i j a b ↦ sorry ]

end Kleenextt.Examples.Brunerie
