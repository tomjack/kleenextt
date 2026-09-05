import Kleenextt.Core.Interval

/-! Each `rfl` runs the decision procedure in the kernel. -/

namespace Kleenextt.Core.Tests

private def i : IExpr := .var 0
private def j : IExpr := .var 1
private def k : IExpr := .var 2

-- The Kleene inequality, what Kleene adds over De Morgan.
example : kleene.decLe (.meet i (.neg i)) (.join j (.neg j)) = true := rfl
example : deMorgan.decLe (.meet i (.neg i)) (.join j (.neg j)) = false := rfl

-- Both theories are De Morgan: involution, De Morgan duality, distributivity.
example : kleene.decEq (.neg (.neg i)) i = true := rfl
example : kleene.decEq (.neg (.meet i j)) (.join (.neg i) (.neg j)) = true := rfl
example : kleene.decEq (.meet i (.join j k)) (.join (.meet i j) (.meet i k)) = true := rfl
example : deMorgan.decEq (.neg (.meet i j)) (.join (.neg i) (.neg j)) = true := rfl

-- Neither theory is Boolean.
example : kleene.decEq (.meet i (.neg i)) .zero = false := rfl
example : deMorgan.decEq (.meet i (.neg i)) .zero = false := rfl

-- The Kleene inequality is not an equation between its two sides.
example : kleene.decEq (.meet i (.neg i)) (.meet j (.neg j)) = false := rfl

example : kleene.decEq (.neg .zero) .one = true := rfl

end Kleenextt.Core.Tests
