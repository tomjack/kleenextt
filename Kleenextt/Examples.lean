import Kleenextt.Frontend

/-! Object-language programs, written directly in this Lean file and checked by
the Kleenextt elaborator when it is elaborated. Ported from elaboration-zoo
02 and 04. -/

namespace Kleenextt.Examples

-- Implicit lambdas are inserted; implicit argument types may be holes.
kdef id : {A : Type} → A → A := λ x => x
kdef const : {A B : _} → A → B → A := λ x y => x
kdef the : (A : _) → A → A := λ _ x => x

#knf id
#ktype const

-- Implicit arguments given explicitly, positionally or by name.
#knf const {Type} {Type} Type
#knf const {B := Type} Type

-- Explicit and named implicit lambdas.
kdef id2 : {A : _} → A → A := λ {A} x => x
kdef namedLam : {A B C : _} → A → B → C → A := λ {B := X} a b c => a
#kconv id = id2

-- Insertion: `id` at an implicit type is eta-expanded to `λ {A} => id {A}`.
kdef insert : {A : _} → A → A := id
#knf insert
-- No insertion when the term already is an implicit lambda.
kdef noinsert : {A : Type} → A → A := λ {A} x => the A x
-- But an implicit lambda applied explicitly gets its implicit inserted.
#knf (λ {A} x => the A x) Type

-- Church booleans and lists, with inferred implicit arguments.
kdef Bool : Type := (B : _) → B → B → B
kdef true : Bool := λ B t f => t
kdef false : Bool := λ B t f => f
kdef List : Type → Type := λ A => (L : _) → (A → L → L) → L → L
kdef nil : {A : _} → List A := λ L cons nil => nil
kdef cons : {A : _} → A → List A → List A := λ x xs L cons nil => cons x (xs L cons nil)
kdef map : {A B : _} → (A → B) → List A → List B := λ {A} {B} f xs L c n => xs L (λ a => c (f a)) n
kdef list1 : List Bool := cons true (cons false (cons true nil))

-- Dependent composition with higher-rank implicit function types.
kdef compose : {A : _} {B : A → Type} {C : {a : A} → B a → Type}
  (f : {a : A} (b : B a) → C b) (g : (a : A) → B a) (a : A) → C (g a)
  := λ f g a => f (g a)
kdef composeExample : List Bool := compose (cons true) (cons false) nil

-- Church naturals: the standard evaluator stress test.
kdef CNat : Type := (N : Type) → (N → N) → N → N
kdef two : CNat := λ N s z => s (s z)
kdef five : CNat := λ N s z => s (s (s (s (s z))))
kdef add : CNat → CNat → CNat := λ a b N s z => a N s (b N s z)
kdef mul : CNat → CNat → CNat := λ a b N s z => a _ (b _ s) z
kdef ten : CNat := add five five
kdef hundred : CNat := mul ten ten

#kconv add ten ten = mul two ten
#kconv mul ten hundred = mul hundred ten

-- Leibniz equality, with metavariables solved by unification.
kdef Eq : {A : _} → A → A → Type := λ {A} x y => (P : A → Type) → P x → P y
kdef refl : {A : _} {x : A} → Eq x x := λ _ px => px
kdef sym : {A x y : _} → Eq {A} x y → Eq y x := λ {A} {x} {y} p => p (λ y => Eq y x) refl
kdef tenTen : Eq (mul ten ten) hundred := refl

-- Eta: a bare neutral against its expansion.
kdef etaL : (A : Type) → (A → A) → A → A := λ A f => f
kdef etaR : (A : Type) → (A → A) → A → A := λ A f x => f x
#kconv etaL = etaR

-- let, and type-in-type.
#knf let f : CNat → CNat := λ n => add n two; f five
kdef tit : Type := Type

-- Ill-typed programs are rejected.
#kfail id id
#kfail (λ A x => x) Type
#kfail const {C := Type}
#kfail the Bool Type
-- Unsolved metavariables are rejected too.
#kfail λ x => x

end Kleenextt.Examples
