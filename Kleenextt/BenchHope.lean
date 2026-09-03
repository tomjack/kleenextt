import Kleenextt.Hope

/-! The numbers that do not compute yet, each running out of memory:
`lake build Kleenextt.BenchHope`. Both take a cube written directly as
nested `hcomp`s with connections in the constructor arguments; the open
`split` of such a cube has a normal form of 41 MB against 111 KB for
`w22`. -/

namespace Kleenextt.Brunerie

#ktime brunerieW

kdef hope : Int := writhe (λ i j k => terribleCheat (ouch i j k))

#ktime hope

end Kleenextt.Brunerie
