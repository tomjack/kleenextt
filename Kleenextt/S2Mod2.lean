import Kleenextt.S1Mod2
import Kleenextt.Tubes
import Kleenextt.LocalGlobal

/-! `S²/2`, the sphere with `surf ≡ flip surf`, with its 2-truncation built
in as a 4-dimensional constructor (`Stuff/Pi3JS2/S2Mod2.agda`), and its
code family into the groupoid of groupoids, giving `π₂S²/2 → Bool`. The
constructors are `sbase`, `surf`, `smod2`, `strunc`, next to `S1m2`'s. -/

namespace Kleenextt.S2Mod2

open HLevel

kdata S2m2 := sbase
  | surf (i j : I) [ (i = 0) ↦ sbase, (i = 1) ↦ sbase, (j = 0) ↦ sbase, (j = 1) ↦ sbase ]
  | smod2 (k i j : I) [ (k = 0) ↦ surf i j, (k = 1) ↦ surf j i,
                        (i = 0) ↦ sbase, (i = 1) ↦ sbase, (j = 0) ↦ sbase, (j = 1) ↦ sbase ]
  | strunc (x y : S2m2) (p q : Path S2m2 x y) (r s : Path (Path S2m2 x y) p q)
      (t u : Path (Path (Path S2m2 x y) p q) r s) (a b c d : I)
      [ (a = 0) ↦ t b c d, (a = 1) ↦ u b c d, (b = 0) ↦ r c d, (b = 1) ↦ s c d,
        (c = 0) ↦ p d, (c = 1) ↦ q d, (d = 0) ↦ x, (d = 1) ↦ y ]

kdef truncS2m2 : is2Groupoid S2m2 := λ x y p q r s t u => λ a b c d => strunc x y p q r s t u a b c d

kdef recS2m2 : (B : Type) (h : is2Groupoid B) (b : B) (sf : Path (Path B b b) refl refl)
  (m : Path (Path (Path B b b) refl refl) sf (λ i j => sf j i)) → S2m2 → B :=
  λ B h b sf m x => case x (λ _ => B)
    [ sbase ↦ b, surf i j ↦ sf i j, smod2 k i j ↦ m k i j,
      strunc x y p q r s t u a b' c d ↦ hlevel 4 h ]

kdef elimS2m2 : (P : S2m2 → Type) (lev : (x : S2m2) → is2Groupoid (P x)) (b : P sbase)
  (sf : PathP (λ i => PathP (λ j => P (surf i j)) b b) refl refl)
  (m : PathP (λ k => PathP (λ i => PathP (λ j => P (smod2 k i j)) b b) refl refl) sf (λ i j => sf j i))
  → (x : S2m2) → P x :=
  λ P lev b sf m x => case x P
    [ sbase ↦ b, surf i j ↦ sf i j, smod2 k i j ↦ m k i j,
      strunc x y p q r s t u a b' c d ↦ hlevel 4 (lev (strunc x y p q r s t u a b' c d)) ]

-- `surfs∥S²/2∥₂-lemma1`: the `2,2`-extension of `surf` by itself.
kdef surfsLemma1 : ext22 S2m2 sbase (λ i j => surf i j) (λ a b => surf a b) :=
  λ i j a b => hlevel 4 truncS2m2

-- The surfaces at every point (`surfs∥S²/2∥₂`): `Ω² S2m2 x` is a set,
-- weakened to the dimension of each cube.
kdef surfsLemma2 : PathP (λ k => PathP (λ i => PathP (λ j => Ω2 S2m2 (smod2 k i j)) (λ a b => surf a b) (λ a b => surf a b))
                            refl refl)
    (λ i j => surfsLemma1 i j) (λ i j => surfsLemma1 j i) :=
  λ k i j => hlevel 3 (isSetToGroupoid (Ω2 S2m2 (smod2 k i j)) (truncS2m2 (smod2 k i j) (smod2 k i j) refl refl))
kdef surfs : (x : S2m2) → Ω2 S2m2 x := λ x => case x (λ x => Ω2 S2m2 x)
  [ sbase ↦ λ a b => surf a b, surf i j ↦ surfsLemma1 i j, smod2 k i j ↦ surfsLemma2 k i j,
    strunc x y p q r s t u a b c d ↦
      hlevel 4 (isGroupoidTo2Groupoid (Ω2 S2m2 (strunc x y p q r s t u a b c d))
                 (isSetToGroupoid (Ω2 S2m2 (strunc x y p q r s t u a b c d))
                   (truncS2m2 (strunc x y p q r s t u a b c d) (strunc x y p q r s t u a b c d) refl refl))) ]

#kconv (λ (a b : I) => surfs sbase a b) = (λ a b => surf a b)

-- `thingy`: at every point, the surface equals its flip (`THINGY-base`,
-- `THINGY-surf`, `THINGY-mod2`, `thingy'`); the 5- and 6-cubes are above
-- the level of `S2m2`, and the truncation case fills a 4-cube in a
-- proposition.
kdef thingyBase : Path (Ω2 S2m2 sbase) (λ a b => surf b a) (λ a b => surf a b) := λ t a b => smod2 (¬ t) a b
kdef thingySurf : PathP (λ i => PathP (λ j => Path (Ω2 S2m2 (surf i j)) (λ a b => surfsLemma1 i j b a) (surfsLemma1 i j))
                          thingyBase thingyBase) refl refl :=
  λ i j t a b => hlevel 4 truncS2m2
kdef thingyMod2 : PathP (λ k => PathP (λ i => PathP (λ j => Path (Ω2 S2m2 (smod2 k i j))
                                                       (λ a b => surfsLemma2 k i j b a) (surfsLemma2 k i j))
                                        (λ t a b => smod2 (¬ t) a b) (λ t a b => smod2 (¬ t) a b))
                          (λ j t a b => smod2 (¬ t) a b) (λ j t a b => smod2 (¬ t) a b))
    (λ i j => thingySurf i j) (λ i j => thingySurf j i) :=
  λ k i j t a b => hlevel 4 truncS2m2
kdef thingy : (y : S2m2) → Path (Ω2 S2m2 y) (λ i j => surfs y j i) (λ i j => surfs y i j) :=
  λ y => case y (λ y => Path (Ω2 S2m2 y) (λ i j => surfs y j i) (λ i j => surfs y i j))
    [ sbase ↦ thingyBase, surf i j ↦ thingySurf i j, smod2 k i j ↦ thingyMod2 k i j,
      strunc x y p q r s t u a b c d ↦
        hlevel 1 (truncS2m2 (strunc x y p q r s t u a b c d) (strunc x y p q r s t u a b c d) refl refl
                    (λ i j => surfs (strunc x y p q r s t u a b c d) j i)
                    (λ i j => surfs (strunc x y p q r s t u a b c d) i j)) ]

#kconv (λ (t a b : I) => thingy sbase t a b) = (λ t a b => smod2 (¬ t) a b)

-- The truncated circle, with the rotation loop; its groupoid structure
-- is a constructor, where Agda proves `isGroupoidS¹`.
kdata S1t := tbase
  | tloop (i : I) [ (i = 0) ↦ tbase, (i = 1) ↦ tbase ]
  | ttrunc (x y : S1t) (p q : Path S1t x y) (r s : Path (Path S1t x y) p q) (a b c : I)
      [ (a = 0) ↦ r b c, (a = 1) ↦ s b c, (b = 0) ↦ p c, (b = 1) ↦ q c, (c = 0) ↦ x, (c = 1) ↦ y ]
kdef truncS1t : isGroupoid S1t := λ x y p q r s => λ a b c => ttrunc x y p q r s a b c
kdef rotLoopT : (x : S1t) → Path S1t x x := λ x => case x (λ x => Path S1t x x)
  [ tbase ↦ λ l => tloop l,
    tloop i ↦ λ l => constSquare S1t tbase (λ i => tloop i) i l,
    ttrunc x y p q r s a b c ↦ λ l => hlevel 3 truncS1t ]

-- `rotLoopsMod2`: the loop of automorphisms of `S¹ × ∥S²/2∥₂` rotating
-- the circle and applying the surfaces, and the square showing that it
-- commutes with itself either way (`rotLoopsMod2Mod2`).
kdef rotHelp : (x : S1t) (y : S2m2) → Ω S2m2 y := λ x y => case x (λ _ => Ω S2m2 y)
  [ tbase ↦ refl, tloop i ↦ λ j => surfs y i j,
    ttrunc x' y' p q r s a b c ↦ λ j => hlevel 4 truncS2m2 ]
kdef PairT : Type := S1t × S2m2
kdef rotLoops : Z PairT := λ i => λ p => (rotLoopT (fst p) i, rotHelp (fst p) (snd p) i)
kdef rotSq : (x : S1t)
  → Path (PathP (λ i => PathP (λ j => S1t) (rotLoopT x i) (rotLoopT x i)) (λ j => rotLoopT x j) (λ j => rotLoopT x j))
      (λ i j => rotLoopT (rotLoopT x j) i) (λ i j => rotLoopT (rotLoopT x i) j) :=
  λ x => case x (λ x => Path (PathP (λ i => PathP (λ j => S1t) (rotLoopT x i) (rotLoopT x i)) (λ j => rotLoopT x j) (λ j => rotLoopT x j))
                          (λ i j => rotLoopT (rotLoopT x j) i) (λ i j => rotLoopT (rotLoopT x i) j))
    [ tbase ↦ refl, tloop i ↦ λ j k l => hlevel 3 truncS1t, ttrunc x y p q r s a b c ↦ λ j k l => hlevel 3 truncS1t ]
kdef rotHelpSq : (x : S1t) (y : S2m2)
  → PathP (λ t => PathP (λ i => PathP (λ j => S2m2) (rotHelp x y i) (rotHelp x y i)) (λ j => rotHelp x y j) (λ j => rotHelp x y j))
      (λ i j => rotHelp (rotLoopT x j) (rotHelp x y j) i) (λ i j => rotHelp (rotLoopT x i) (rotHelp x y i) j) :=
  λ x y => case x (λ x => PathP (λ t => PathP (λ i => PathP (λ j => S2m2) (rotHelp x y i) (rotHelp x y i)) (λ j => rotHelp x y j) (λ j => rotHelp x y j))
                            (λ i j => rotHelp (rotLoopT x j) (rotHelp x y j) i) (λ i j => rotHelp (rotLoopT x i) (rotHelp x y i) j))
    [ tbase ↦ thingy y, tloop k ↦ λ t i j => hlevel 4 truncS2m2, ttrunc x' y' p q r s a b c ↦ λ t i j => hlevel 4 truncS2m2 ]
kdef rotLoopsSq : Path (ext11 (PairT → PairT) (λ x => x) rotLoops rotLoops)
    (naturalComm PairT rotLoops rotLoops) (flipNaturalComm PairT rotLoops rotLoops) :=
  λ t i j => λ p => (rotSq (fst p) t i j, rotHelpSq (fst p) (snd p) t i j)

-- `Code`: the family of groupoids over the truncated sphere, `∥S¹/2∥₁`
-- twisted by its rotation, with `global rotS¹/2 ≡ flipSquare (global
-- rotS¹/2)` over `smod2` (`Code'-mod2`) by `global≡`.
kdef symFlipB : (A : Type) (x : A) (q : Ω A x) (i : I) → Type :=
  λ A x q i => PathP (λ j => Path A x (q (i ∨ j))) (λ k => q (i ∧ k)) refl
kdef symFlipMain : (A : Type) (x : A) (q : Ω A x) (p : Path (Ω A x) refl q)
  → PathP (λ i => symFlipB A x q i) (λ i j => p j i) (sym p) :=
  λ A x q p => J (λ q p => PathP (λ i => symFlipB A x q i) (λ i j => p j i) (sym p)) refl p
kdef symFlipSquare : (A : Type) (x : A) (P : Ω2 A x) → Path (Ω2 A x) (sym P) (λ i j => P j i) :=
  λ A x P => sym (symFlipMain A x refl P)

kdef rotS : Z S1m2 := λ i => λ x => rot x i
kdef globalRot : Ω2 Type S1m2 := global S1m2 rotS
kdef globalRotFlip : Ω2 Type S1m2 := λ i j => global S1m2 rotS j i
kdef ouch3 : Path (Ω S1m2 base) (λ i => loop i) (λ i => loc S1m2 globalRot (¬ i) base) :=
  let m : Path (Ω S1m2 base) (λ i => loop i) (λ i => loop (¬ i)) := λ t i => mod2 t i;
  let g : Path (Ω S1m2 base) (λ i => loop (¬ i)) (λ i => loc S1m2 globalRot (¬ i) base) :=
    λ t i => localGlobal S1m2 rotS (¬ t) (¬ i) base;
  pcomp m g
kdef ouchBase : PathP (λ t => Path S1m2 base base) (λ i => loc S1m2 globalRot i base) (λ i => loc S1m2 globalRotFlip i base) :=
  λ t i => hcomp S1m2 (λ k => [ (t = 0) ↦ localGlobal S1m2 rotS (¬ k) i base,
                                (t = 1) ↦ loc S1m2 (symFlipSquare Type S1m2 globalRot k) i base,
                                (i = 0) ↦ base, (i = 1) ↦ base ]) (ouch3 t i)
kdef ouchLoop : PathP (λ k => PathP (λ t => PathP (λ i => S1m2) (loop k) (loop k))
                                (λ i => loc S1m2 globalRot i (loop k)) (λ i => loc S1m2 globalRotFlip i (loop k)))
                  ouchBase ouchBase :=
  λ k t i => hlevel 3 truncS1m2
kdef ouchMod2 : PathP (λ k => PathP (λ l => PathP (λ t => PathP (λ i => S1m2) (mod2 k l) (mod2 k l))
                                                (λ i => loc S1m2 globalRot i (mod2 k l)) (λ i => loc S1m2 globalRotFlip i (mod2 k l)))
                                  ouchBase ouchBase)
                  ouchLoop (λ l => ouchLoop (¬ l)) :=
  λ k l t i => hlevel 3 truncS1m2
kdef ouch1 : (x : S1m2) → PathP (λ t => Path S1m2 x x) (λ i => loc S1m2 globalRot i x) (λ i => loc S1m2 globalRotFlip i x) :=
  λ x => case x (λ x => PathP (λ t => Path S1m2 x x) (λ i => loc S1m2 globalRot i x) (λ i => loc S1m2 globalRotFlip i x))
    [ base ↦ ouchBase, loop k ↦ ouchLoop k, mod2 k l ↦ ouchMod2 k l,
      trunc x y p q r s a b c ↦ λ t i => hlevel 3 truncS1m2 ]
kdef codeMod2 : Path (Ω2 Type S1m2) globalRot globalRotFlip :=
  globalEq S1m2 globalRot globalRotFlip (λ t i => λ x => ouch1 x t i)

kdef code : S2m2 → hGroupoid := λ x => case x (λ _ => hGroupoid)
  [ sbase ↦ (S1m2, truncS1m2),
    surf i j ↦ (globalRot i j, hlevel 1 (isPropIsGroupoid (globalRot i j))),
    smod2 k i j ↦ (codeMod2 k i j, hlevel 1 (isPropIsGroupoid (codeMod2 k i j))),
    strunc x y p q r s t u a b c d ↦ hlevel 4 is2GroupoidHGroupoid ]
kdef encodeΩ2 : Ω2 S2m2 sbase → Ω S1m2 base := λ p => λ i => transport (λ j => fst (code (p i j))) base
kdef bit2 : Ω2 S2m2 sbase → Bool := λ p => bit (encodeΩ2 p)

#kconv bit2 (λ i j => sbase) = false
#kconv bit2 (λ i j => surf j i) = true
#kconv bit2 (λ i j => surf i j) = true
kdef surfSq : Ω2 S2m2 sbase := λ i j => surf i j
#kconv bit2 (pcomp surfSq surfSq) = false

#kconv (λ (B : Type) (h : is2Groupoid B) (b : B) (sf : Path (Path B b b) refl refl)
  (m : Path (Path (Path B b b) refl refl) sf (λ i j => sf j i)) (i j : I)
  => recS2m2 B h b sf m (surf i j)) = (λ B h b sf m i j => sf i j)

end Kleenextt.S2Mod2
