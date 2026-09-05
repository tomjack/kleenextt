import Kleenextt.Examples.Brunerie

/-! The ladder to the Brunerie number; `BenchDeep` and `BenchBrunerie` are
the slow steps. Not in the default build. -/

namespace Kleenextt.Examples.Brunerie

#ktime windingS1 (λ i => loop i)
#ktime windingS2 (λ i j => loop2 i j)
#ktime λ (i j : I) => split (λ k => w22 i j k)
#ktime writhe (λ i j k => base2)

end Kleenextt.Examples.Brunerie
