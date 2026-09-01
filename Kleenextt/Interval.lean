namespace Kleenextt

/-- Formal interval expressions: terms in the signature of bounded lattices
with an involution, over numbered generators. -/
inductive IExpr where
  | zero
  | one
  | var (i : Nat)
  | neg (r : IExpr)
  | meet (r s : IExpr)
  | join (r s : IExpr)
  deriving Repr, DecidableEq

namespace IExpr

/-- One more than the largest generator mentioned. -/
def arity : IExpr → Nat
  | zero | one => 0
  | var i => i + 1
  | neg r => r.arity
  | meet r s | join r s => max r.arity s.arity

end IExpr

/-- A finite algebra in the interval signature, carrier listed in `elems`.
If `A` generates a variety `V`, then an equation holds in the free `V`-algebra
iff it holds under every assignment into `A` — so `elems` makes the equational
theory of `V` decidable by enumeration. -/
structure Alg (α : Type) where
  elems : List α
  bot : α
  top : α
  neg : α → α
  meet : α → α → α
  join : α → α → α

namespace Alg

variable {α : Type} (A : Alg α)

def eval (ρ : Nat → α) : IExpr → α
  | .zero => A.bot
  | .one => A.top
  | .var i => ρ i
  | .neg r => A.neg (eval ρ r)
  | .meet r s => A.meet (eval ρ r) (eval ρ s)
  | .join r s => A.join (eval ρ r) (eval ρ s)

/-- Every assignment of `n` generators to elements of `A`. -/
def envs : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => (envs n).flatMap fun ρ => A.elems.map (· :: ρ)

/-- Decide `r = s` in the variety `A` generates. -/
def decEq [DecidableEq α] (r s : IExpr) : Bool :=
  (A.envs (max r.arity s.arity)).all fun ρ =>
    A.eval (fun i => ρ.getD i A.bot) r == A.eval (fun i => ρ.getD i A.bot) s

/-- Decide `r ≤ s` (i.e. `r ∨ s = s`) in the variety `A` generates. -/
def decLe [DecidableEq α] (r s : IExpr) : Bool :=
  A.decEq (.join r s) s

end Alg

/-- The three-element Kleene algebra `0 < ½ < 1` with `¬½ = ½`. It generates
the variety of Kleene algebras (Kalman 1958), so it decides the equational
theory of the free Kleene interval. -/
inductive K3 where
  | zero | half | one
  deriving Repr, DecidableEq

namespace K3

def neg : K3 → K3
  | .zero => .one
  | .half => .half
  | .one => .zero

def meet : K3 → K3 → K3
  | .zero, _ => .zero
  | .half, .zero => .zero
  | .half, _ => .half
  | .one, y => y

def join : K3 → K3 → K3
  | .one, _ => .one
  | .half, .one => .one
  | .half, _ => .half
  | .zero, y => y

end K3

/-- The Kleene interval theory. -/
def kleene : Alg K3 where
  elems := [.zero, .half, .one]
  bot := .zero
  top := .one
  neg := K3.neg
  meet := K3.meet
  join := K3.join

/-- The four-element De Morgan algebra: `0 < a, b < 1` with `a`, `b`
incomparable and `¬` fixing both. It generates the variety of De Morgan
algebras, so it decides the interval theory of stock CCHM. -/
inductive DM4 where
  | zero | a | b | one
  deriving Repr, DecidableEq

namespace DM4

def neg : DM4 → DM4
  | .zero => .one
  | .a => .a
  | .b => .b
  | .one => .zero

def meet : DM4 → DM4 → DM4
  | .one, y => y
  | x, .one => x
  | .zero, _ => .zero
  | _, .zero => .zero
  | .a, .a => .a
  | .b, .b => .b
  | _, _ => .zero

def join : DM4 → DM4 → DM4
  | .zero, y => y
  | x, .zero => x
  | .one, _ => .one
  | _, .one => .one
  | .a, .a => .a
  | .b, .b => .b
  | _, _ => .one

end DM4

/-- The stock CCHM interval theory. -/
def deMorgan : Alg DM4 where
  elems := [.zero, .a, .b, .one]
  bot := .zero
  top := .one
  neg := DM4.neg
  meet := DM4.meet
  join := DM4.join

end Kleenextt
