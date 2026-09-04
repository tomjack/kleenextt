import Kleenextt.Examples.Brunerie

/-! The timing ladder towards the Brunerie number. Not part of the default
build: `lake build Kleenextt.Examples.Bench`, and
`Kleenextt.Examples.BenchDeep` and `Kleenextt.Examples.BenchBrunerie` for
the slow steps. -/

namespace Kleenextt.Examples.Brunerie

#ktime windingS1 (λ i => loop i)
#ktime windingS2 (λ i j => loop2 i j)
#ktime λ (i j : I) => split (λ k => w22 i j k)
#ktime writhe (λ i j k => base2)

end Kleenextt.Examples.Brunerie
