import Kleenextt.Hope

/-! The expensive numbers: `lake build Kleenextt.BenchHope`. Both take a
cube written directly as nested `hcomp`s with connections in the
constructor arguments; the open `split` of such a cube has a normal form
of 41 MB against 111 KB for `w22`. `brunerieW` is +2 in 33 s and 3.4 GB
(1.06M `hcomp`s); `hope` is +1 in about eight minutes, peaking at 11 GB
(5.8M). -/

namespace Kleenextt.Brunerie

#ktime brunerieW

kdef hope : Int := writhe (λ i j k => terribleCheat (ouch i j k))

#ktime hope

end Kleenextt.Brunerie
