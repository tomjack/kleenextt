import Kleenextt.Examples.Hope

/-! Cubes written as nested `hcomp`s with connections. `brunerieW` is +2 in
33 s and 3.4 GB; `hope` is +1 in about eight minutes and 11 GB. -/

namespace Kleenextt.Examples.Brunerie

#ktime brunerieW

kdef hope : Int := writhe (λ i j k => terribleCheat (ouch i j k))

#ktime hope

end Kleenextt.Examples.Brunerie
