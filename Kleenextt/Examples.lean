import Kleenextt.Frontend

/-! Object-language programs, written directly in this Lean file and checked by
the Kleenextt kernel when it is elaborated. Ported from elaboration-zoo 02. -/

namespace Kleenextt.Examples

kdef id : (A : Type) → A → A := λ A x => x
kdef const : (A B : Type) → A → B → A := λ A B x y => x

#ktype const
#knf id ((A B : Type) → A → B → A) const

-- Church naturals: the standard evaluator stress test.
kdef CNat : Type := (N : Type) → (N → N) → N → N
kdef two : CNat := λ N s z => s (s z)
kdef five : CNat := λ N s z => s (s (s (s (s z))))
kdef add : CNat → CNat → CNat := λ a b N s z => a N s (b N s z)
kdef mul : CNat → CNat → CNat := λ a b N s z => a N (b N s) z
kdef ten : CNat := add five five
kdef hundred : CNat := mul ten ten

#kconv add ten ten = mul two ten
#kconv mul ten hundred = mul hundred ten

-- Eta: a bare neutral against its expansion.
kdef etaL : (A : Type) → (A → A) → A → A := λ A f => f
kdef etaR : (A : Type) → (A → A) → A → A := λ A f x => f x
#kconv etaL = etaR

-- let, and type-in-type.
#knf let f : CNat → CNat := λ n => add n two; f five
kdef tit : Type := Type

-- Ill-typed programs are rejected.
#kfail id id
#kfail λ x => x
#kfail (λ A x => x) Type

end Kleenextt.Examples
