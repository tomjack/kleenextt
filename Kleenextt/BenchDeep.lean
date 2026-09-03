import Kleenextt.Brunerie

/-! One transport further than the split cube: the loop in `S1` that
`windingS1` then counts. -/

namespace Kleenextt.Brunerie

#ktime λ (i : I) => recΩS2 S1 base (λ i x => rotLoop x i) (λ j => snd (split (λ k => w22 i j k)))

end Kleenextt.Brunerie
