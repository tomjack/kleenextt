import Kleenextt.S2Mod2

/-! `Stuff/Pi3JS2/J2S2.agda`: the family over `J₂S²` into the universe
with fibre `S¹ × ∥S²/2∥₂`, `global rotLoopsMod2` over `surf₁` and over
`surf₂` the `2,2`-extension that `rotLoopsMod2Mod2` gives through
`LocalGlobal`. Transport along it takes `π₃(J₂S²)` to `π₂∥S²/2∥₂`, then
`Bool`; `bit` is the value on the Hopf generator `η surf₁`. -/

namespace Kleenextt.J2S2

open HLevel S2Mod2 Tubes LocalGlobal

kdata J2S2 := jbase
  | jsurf (i j : I) [ (i = 0) ↦ jbase, (i = 1) ↦ jbase, (j = 0) ↦ jbase, (j = 1) ↦ jbase ]
  | jsurfsurf (i j a b : I) [ (i = 0) ↦ jsurf a b, (i = 1) ↦ jsurf a b, (j = 0) ↦ jsurf a b, (j = 1) ↦ jsurf a b,
                              (a = 0) ↦ jsurf i j, (a = 1) ↦ jsurf i j, (b = 0) ↦ jsurf i j, (b = 1) ↦ jsurf i j ]

kdef globalRL : Ω2 Type PairT := global PairT rotLoops

-- `gnarly'`: `+EH⋆ ≡ -EH⋆` for `global rotLoops`, from `rotLoopsSq`
-- carried through `local`.
kdef gnarlyPath : Path (ext11 (Ω Type PairT) refl globalRL globalRL)
    (ehPlusStar Type PairT globalRL globalRL) (ehMinusStar Type PairT globalRL globalRL) :=
  let step : Path (ext11 (PairT → PairT) (λ x => x) (loc PairT globalRL) (loc PairT globalRL))
      (naturalComm PairT (loc PairT globalRL) (loc PairT globalRL))
      (flipNaturalComm PairT (loc PairT globalRL) (loc PairT globalRL)) :=
    transport
      (λ t => Path (ext11 (PairT → PairT) (λ x => x) (localGlobal PairT rotLoops (¬ t)) (localGlobal PairT rotLoops (¬ t)))
                (naturalComm PairT (localGlobal PairT rotLoops (¬ t)) (localGlobal PairT rotLoops (¬ t)))
                (flipNaturalComm PairT (localGlobal PairT rotLoops (¬ t)) (localGlobal PairT rotLoops (¬ t))))
      rotLoopsSq;
  globalCommEq PairT globalRL globalRL (ehPlusStar Type PairT globalRL globalRL) (ehMinusStar Type PairT globalRL globalRL)
    (pcomp (localCommPlusEH PairT globalRL globalRL) (pcomp step (sym (localCommMinusEH PairT globalRL globalRL))))
kdef gnarly : ext22 Type PairT globalRL globalRL := extFromPath Type PairT globalRL globalRL gnarlyPath

kdef funP : J2S2 → Type := λ x => case x (λ _ => Type)
  [ jbase ↦ PairT, jsurf i j ↦ globalRL i j, jsurfsurf i j a b ↦ gnarly i j a b ]
kdef fun1 : Ω J2S2 jbase → PairT := λ p => transport (λ i => funP (p i)) (tbase, sbase)
kdef fun2 : Ω3 J2S2 jbase → Ω2 S2m2 sbase := λ p => λ i j => snd (fun1 (λ k => p i j k))
kdef bit3 : Ω3 J2S2 jbase → Bool := λ p => bit2 (fun2 p)
kdef gen : Ω3 J2S2 jbase := eta J2S2 jbase (λ i j => jsurf i j)
kdef bitJ : Bool := bit3 gen

#ktime bitJ
#kconv bitJ = true
#kconv bit3 (eta J2S2 jbase (λ i j => jsurf j i)) = true
#kconv bit3 (λ i j k => jbase) = false
#kconv bit3 (pcomp gen gen) = false

end Kleenextt.J2S2
