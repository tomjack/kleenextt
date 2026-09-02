import Kleenextt.Prelude

/-! The Brunerie-like number of cctt's `tests/brunerie_james_revised.cctt`
(up to `brunerie`), written in CCHM style after the cubicaltt original
`examples/brunerie_james.ctt`: connections instead of Cartesian `hcom`
encodings, Cubical Agda's `isPropIsContr` and `isoToIsEquiv`, direct `J`.
Equivalences are contractible-fiber. -/

namespace Kleenextt.Brunerie
open Kleenextt.Prelude

kdata Nat := zero | suc (n : Nat)
kdata Int := pos (n : Nat) | neg (n : Nat)
kdata S2 := base2 | loop2 (i j : I) [ (i = 0) ↦ base2, (i = 1) ↦ base2, (j = 0) ↦ base2, (j = 1) ↦ base2 ]

kdef Ω : (A : Type) → A → Type := λ A x => Path A x x
kdef Ω2 : (A : Type) → A → Type := λ A x => Ω (Ω A x) refl
kdef Ω3 : (A : Type) → A → Type := λ A x => Ω (Ω2 A x) refl

kdef isProp : Type → Type := λ A => (a b : A) → Path A a b

kdef J : {A : Type} {a : A} (C : (x : A) → Path A a x → Type) (d : C a refl) {x : A} (p : Path A a x) → C x p :=
  λ {A} {a} C d {x} p => transp (λ i => C (p i) (λ j => p (i ∧ j))) 0 d

-- Isomorphisms to equivalences: Cubical Agda's `isoToIsEquiv`, with the
-- fiber path in our orientation `Path B y (f x)`.

kdef isIso : (A B : Type) (f : A → B) → Type :=
  λ A B f => (g : B → A) × ((x : A) → Path A (g (f x)) x) × ((x : B) → Path B (f (g x)) x)
kdef iso : Type → Type → Type := λ A B => (f : A → B) × isIso A B f

kdef isoToEquiv : (A B : Type) → iso A B → Equiv A B :=
  λ A B is =>
  let f : A → B := fst is;
  let g : B → A := fst (snd is);
  let t : (x : A) → Path A (g (f x)) x := fst (snd (snd is));
  let s : (x : B) → Path B (f (g x)) x := snd (snd (snd is));
  (f, λ y => ((g y, λ j => s y (¬ j)),
    λ z =>
      let x0 : A := g y;
      let p0 : Path B (f x0) y := s y;
      let x1 : A := fst z;
      let p1 : Path B (f x1) y := λ j => snd z (¬ j);
      let fill0 : (i k : I) → A := λ i k => hfill A (λ l => [ (i = 1) ↦ t x0 l, (i = 0) ↦ g y ]) (g (p0 (¬ i))) k;
      let fill1 : (i k : I) → A := λ i k => hfill A (λ l => [ (i = 1) ↦ t x1 l, (i = 0) ↦ g y ]) (g (p1 (¬ i))) k;
      let fill2 : (i k : I) → A := λ i k => hfill A (λ l => [ (i = 1) ↦ fill1 l 1, (i = 0) ↦ fill0 l 1 ]) (g y) k;
      let p : (i : I) → A := λ i => fill2 i 1;
      let sq : (i j : I) → A := λ i j =>
        hcomp A (λ k => [ (i = 1) ↦ fill1 j (¬ k), (i = 0) ↦ fill0 j (¬ k), (j = 1) ↦ t (fill2 i 1) (¬ k), (j = 0) ↦ g y ]) (fill2 i j);
      let sq1 : (i j : I) → B := λ i j =>
        hcomp B (λ k => [ (i = 1) ↦ s (p1 (¬ j)) k, (i = 0) ↦ s (p0 (¬ j)) k, (j = 1) ↦ s (f (p i)) k, (j = 0) ↦ s y k ]) (f (sq i j));
      λ i => (p i, λ j => sq1 i j)))

-- Integers.

kdef predInt : Int → Int := λ x => case x (λ _ => Int)
  [ pos u ↦ case u (λ _ => Int) [ zero ↦ neg zero, suc n ↦ pos n ], neg v ↦ neg (suc v) ]
kdef sucInt : Int → Int := λ x => case x (λ _ => Int)
  [ pos u ↦ pos (suc u), neg v ↦ case v (λ _ => Int) [ zero ↦ pos zero, suc n ↦ neg n ] ]
kdef predsucInt : (x : Int) → Path Int (predInt (sucInt x)) x :=
  λ x => case x (λ x => Path Int (predInt (sucInt x)) x)
    [ pos u ↦ refl, neg v ↦ case v (λ v => Path Int (predInt (sucInt (neg v))) (neg v)) [ zero ↦ refl, suc n ↦ refl ] ]
kdef sucpredInt : (x : Int) → Path Int (sucInt (predInt x)) x :=
  λ x => case x (λ x => Path Int (sucInt (predInt x)) x)
    [ pos u ↦ case u (λ u => Path Int (sucInt (predInt (pos u))) (pos u)) [ zero ↦ refl, suc n ↦ refl ], neg v ↦ refl ]

kdef sucIntIso : iso Int Int := (sucInt, predInt, predsucInt, sucpredInt)
kdef sucPathInt : Path Type Int Int := ua (isoToEquiv Int Int sucIntIso)

kdef helix : S1 → Type := λ x => case x (λ _ => Type) [ base ↦ Int, loop i ↦ sucPathInt i ]
kdef windingS1 : Ω S1 base → Int := λ p => transp (λ i => helix (p i)) 0 (pos zero)

#kconv windingS1 (λ i => loop i) = pos (suc zero)
#kconv windingS1 (λ i => loop (¬ i)) = neg zero
#kconv windingS1 (pcomp (λ i => loop i) (λ i => loop i)) = pos (suc (suc zero))

-- The square with a loop on all four sides, by connections.
kdef constSquare : (A : Type) (a : A) (p : Path A a a) → PathP (λ i => Path A (p i) (p i)) p p :=
  λ A a p i j => hcomp A (λ k => [ (i = 0) ↦ p (j ∨ ¬ k), (i = 1) ↦ p (j ∧ k), (j = 0) ↦ p (i ∨ ¬ k), (j = 1) ↦ p (i ∧ k) ]) a

kdef rotLoop : (a : S1) → Path S1 a a := λ a => case a (λ a => Path S1 a a)
  [ base ↦ λ i => loop i, loop i ↦ λ j => constSquare S1 base (λ i => loop i) i j ]

-- Being an equivalence is a proposition: cubicaltt's `propIsEquivDirect`
-- (`examples/equiv.ctt`), one composition over connections per fiber.
kdef propIsEquivDirect : (A B : Type) (f : A → B) → isProp (isEquiv f) := λ A B f p q i y =>
  let F : Type := fiber f y;
  let p2 : (w : F) → Path F (fst (p y)) w := snd (p y);
  let q2 : (w : F) → Path F (fst (q y)) w := snd (q y);
  (p2 (fst (q y)) i,
   λ w j => hcomp F (λ k => [ (i = 0) ↦ p2 w j, (i = 1) ↦ q2 w (j ∨ ¬ k), (j = 0) ↦ p2 (q2 w (¬ k)) i, (j = 1) ↦ w ])
              (p2 w (i ∨ j)))

-- Local-global looping.

kdef Z : Type → Type := λ A => Ω (A → A) (λ x => x)

-- One transport along the loop, corrected at `i = 1` by the contraction of
-- `isEquiv id` onto `idIsEquiv` (`anyRotIsEquiv` in brunerie_james.ctt).
kdef rotIsEquiv : (A : Type) (h : Z A) (i : I) → isEquiv (λ x => h i x) :=
  λ A h i =>
    hcomp (isEquiv (λ x => h i x))
      (λ k => [ (i = 0) ↦ snd (idEquiv A),
                (i = 1) ↦ propIsEquivDirect A A (λ x => x) (snd (idEquiv A))
                            (transp (λ i => isEquiv (λ x => h i x)) 0 (snd (idEquiv A))) (¬ k) ])
      (transp (λ j => isEquiv (λ x => h (i ∧ j) x)) (¬ i) (snd (idEquiv A)))

kdef rotEquiv : (A : Type) (h : Z A) → Path (Equiv A A) (idEquiv A) (idEquiv A) :=
  λ A h i => (λ x => h i x, rotIsEquiv A h i)

kdef global : (A : Type) (h : Z A) → Ω2 Type A :=
  λ A h i j => Glue A [ (i = 0) ↦ (A, idEquiv A), (i = 1) ↦ (A, idEquiv A),
                        (j = 0) ↦ (A, rotEquiv A h i), (j = 1) ↦ (A, idEquiv A) ]

kdef globalS2 : (A : Type) (h : Z A) → S2 → Type :=
  λ A h x => case x (λ _ => Type) [ base2 ↦ A, loop2 i j ↦ global A h i j ]

kdef ΩS2 : Type := Ω S2 base2

kdef recΩS2 : (A : Type) (x : A) (h : Z A) → ΩS2 → A :=
  λ A x h p => transp (λ i => globalS2 A h (p i)) 0 x

kdef windingS2 : Ω2 S2 base2 → Int :=
  λ p => windingS1 (λ i => recΩS2 S1 base (λ i x => rotLoop x i) (p i))

#kconv windingS2 (λ i j => loop2 i j) = pos (suc zero)

-- The Whitehead product [loop2, loop2].

kdef w22' : Ω (Ω2 S2 base2) (λ a b => loop2 a b) :=
  λ j a b => hcomp S2 (λ i => [ (j = 0) ↦ loop2 a b, (j = 1) ↦ loop2 a b, (a = 0) ↦ loop2 i j, (a = 1) ↦ loop2 i j,
                                (b = 0) ↦ loop2 i j, (b = 1) ↦ loop2 i j ]) (loop2 a b)

kdef dsqInv : (A : Type) (x y : A) (p : Path A x y) (r : Path (Path A x y) p p) → Ω2 A x :=
  λ A x y p r => J (λ y p => Path (Path A x y) p p → Ω2 A x) (λ r => r) p r

kdef w22 : Ω3 S2 base2 := dsqInv ΩS2 refl refl (λ i j => loop2 i j) w22'

-- The 2-truncation is cheated, as in the original.
kdef tr2S2 : Type := S2

kdef cheating : (y : tr2S2) → Ω2 tr2S2 y :=
  λ y => case y (λ y => Ω2 S2 y) [ base2 ↦ λ i j => loop2 i j, loop2 i j ↦ sorry ]

kdef direct2 : S1 → (y : tr2S2) → Ω tr2S2 y :=
  λ x => case x (λ _ => (y : tr2S2) → Ω tr2S2 y) [ base ↦ λ y => refl, loop i ↦ λ y => cheating y i ]

kdef direct : Z (S1 × tr2S2) := λ i x => (rotLoop (fst x) i, direct2 (fst x) (snd x) i)

kdef split : ΩS2 → S1 × tr2S2 := recΩS2 (S1 × tr2S2) (base, base2) direct

kdef writhe : Ω3 S2 base2 → Int := λ p => windingS2 (λ i j => snd (split (λ k => p i j k)))

kdef brunerie : Int := writhe w22

/- The rest of cctt's file, ported with the `hcom`/`coe` sugar; it elaborates
except `hope`, whose elaboration does not finish. Disabled until `brunerie`
normalises.

kdef Ω4 : (A : Type) → A → Type := λ A x => Ω (Ω3 A x) refl
kdef isSet : Type → Type := λ A => (a b : A) → isProp (Path A a b)

-- Eckmann-Hilton and the Hopf construction.

kdef squareConnAnd : (A : Type) (x : A) (p : Ω2 A x)
  → PathP (λ i => PathP (λ j => Path A x (p i j)) refl (λ k => p i k)) refl refl :=
  λ A x p i j k => p i (j ∧ k)

kdef EH : (A : Type) (x : A) (p q : Ω2 A x) → PathP (λ i => Path (Path A x x) (p i) (p i)) q q :=
  λ A x p q i j k => hcomp A (λ l => [ (i = 0) ↦ q j (k ∧ l), (i = 1) ↦ q j (k ∧ l), (j = 0) ↦ p i k, (j = 1) ↦ p i k,
                                       (k = 0) ↦ x, (k = 1) ↦ q j l ]) (p i k)

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

-- Towards π₄(S³): squares over families of sets.

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
      (λ i j => isPropIsSet (isEquiv (λ x => h i j x)) (isPropIsEquiv A A (λ x => h i j x)))
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

kdef hope : Int := writhe (λ i j k => terribleCheat (ouch i j k))
-/

end Kleenextt.Brunerie
