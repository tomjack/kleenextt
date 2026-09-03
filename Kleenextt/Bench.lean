import Kleenextt.Brunerie

/-! The timing ladder towards the Brunerie number. Not part of the default
build: `lake build Kleenextt.Bench`, and `Kleenextt.BenchDeep` and
`Kleenextt.BenchBrunerie` for the slow steps. -/

namespace Kleenextt.Brunerie

#ktime windingS1 (λ i => loop i)
#ktime windingS2 (λ i j => loop2 i j)
#ktime λ (i j : I) => split (λ k => w22 i j k)
#ktime writhe (λ i j k => base2)

end Kleenextt.Brunerie
