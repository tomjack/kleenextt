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
  deriving Repr, DecidableEq, Inhabited

namespace IExpr

/-- One more than the largest generator mentioned. -/
def arity : IExpr → Nat
  | zero | one => 0
  | var i => i + 1
  | neg r => r.arity
  | meet r s | join r s => max r.arity s.arity

/-- The generators mentioned, without duplicates. -/
def vars : IExpr → List Nat
  | zero | one => []
  | var i => [i]
  | neg r => r.vars
  | meet r s | join r s => (r.vars ++ s.vars).eraseDups

def mapVars (f : Nat → IExpr) : IExpr → IExpr
  | zero => zero
  | one => one
  | var i => f i
  | neg r => neg (r.mapVars f)
  | meet r s => meet (r.mapVars f) (s.mapVars f)
  | join r s => join (r.mapVars f) (s.mapVars f)

def mapVarsM [Monad m] (f : Nat → m IExpr) : IExpr → m IExpr
  | zero => pure zero
  | one => pure one
  | var i => f i
  | neg r => do pure (neg (← r.mapVarsM f))
  | meet r s => do pure (meet (← r.mapVarsM f) (← s.mapVarsM f))
  | join r s => do pure (join (← r.mapVarsM f) (← s.mapVarsM f))

def ofBool : Bool → IExpr
  | false => zero
  | true => one

/-- Precedences: 0 ∨, 1 ∧, 2 atoms. -/
def pretty (name : Nat → String) (p : Nat) : IExpr → String
  | zero => "0"
  | one => "1"
  | var i => name i
  | neg r => s!"¬{r.pretty name 2}"
  | meet r s =>
    let str := s!"{r.pretty name 1} ∧ {s.pretty name 1}"
    if p > 1 then s!"({str})" else str
  | join r s =>
    let str := s!"{r.pretty name 0} ∨ {s.pretty name 0}"
    if p > 0 then s!"({str})" else str

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

/-- `decEq`, enumerating assignments only for the generators that occur, so
the cost is exponential in the number of generators mentioned rather than
in the largest generator index. -/
def decEqOn [DecidableEq α] (r s : IExpr) : Bool :=
  let vs := (r.vars ++ s.vars).eraseDups
  (A.envs vs.length).all fun ρ =>
    let f := fun i => match vs.idxOf? i with
      | some k => ρ.getD k A.bot
      | none => A.bot
    A.eval f r == A.eval f s

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

/-- The two-element Boolean algebra: the classical reading of a cofibration. -/
def boolean : Alg Bool where
  elems := [false, true]
  bot := false
  top := true
  neg := not
  meet := and
  join := or

/-! ## The interval used by the kernel

Interval expressions in values are `IExpr`s over de Bruijn levels; the
equational theory is the free Kleene algebra. -/

/-! ### Normal forms

A clause is a sorted list of literals `(i, d)`; a clause may contain both
polarities of a generator, since `i ∧ ¬i ≠ 0` in a Kleene algebra. Constants
are propagated and absorption (`x ∨ (x ∧ y) = x`) is applied, which is valid
in any lattice, so the normal form is a De Morgan normal form: it decides
`r = 0` and `r = 1` and gives the faces on which `r = 1`, but two Kleene-equal
expressions may still have different normal forms. -/

abbrev Clause := List (Nat × Bool)

namespace Clause

private def litLt (l m : Nat × Bool) : Bool :=
  l.1 < m.1 || (l.1 == m.1 && !l.2 && m.2)

def insertLit (l : Nat × Bool) : Clause → Clause
  | [] => [l]
  | m :: c => if litLt l m then l :: m :: c else if l == m then m :: c else m :: insertLit l c

def union (c d : Clause) : Clause := d.foldl (fun acc l => acc.insertLit l) c

/-- `c` is at least as strong as `d`: it contains every literal of `d`. -/
def implies (c d : Clause) : Bool := d.all c.contains

def consistent (c : Clause) : Bool := !c.any fun (i, d) => c.contains (i, !d)

end Clause

/-- Drop duplicate clauses and clauses that imply another one. -/
def absorb (cs : List Clause) : List Clause :=
  let cs := cs.eraseDups
  cs.filter fun c => !cs.any fun d => d != c && c.implies d

private def product (cs ds : List Clause) : List Clause :=
  absorb <| cs.flatMap fun c => ds.map fun d => c.union d

/-- The DNF clauses of `r` (`neg = false`) or of `¬r` (`neg = true`). -/
partial def dnf (r : IExpr) (neg : Bool) : List Clause :=
  match r, neg with
  | .zero, false | .one, true => []
  | .zero, true | .one, false => [[]]
  | .var i, b => [[(i, !b)]]
  | .neg r, b => dnf r (!b)
  | .meet r s, false | .join r s, true => product (dnf r neg) (dnf s neg)
  | .meet r s, true | .join r s, false => absorb (dnf r neg ++ dnf s neg)

private def ofClauses (cs : List Clause) : IExpr :=
  let lit (l : Nat × Bool) : IExpr := if l.2 then .var l.1 else .neg (.var l.1)
  let clause (c : Clause) : IExpr := match c.map lit with
    | [] => .one
    | l :: ls => ls.foldl .meet l
  match cs.map clause with
  | [] => .zero
  | c :: cs => cs.foldl .join c

namespace IExpr

def norm (r : IExpr) : IExpr := ofClauses (dnf r false)

/-- Normal forms decide the constants outright. -/
def isZero (r : IExpr) : Bool := (dnf r false).isEmpty
def isOne (r : IExpr) : Bool := (dnf r false).any (·.isEmpty)

/-- ABCFHL validity: the cofibration `r = 1` holds classically, so no closed
instance of a system on `r` can be empty. -/
def isValid (r : IExpr) : Bool := boolean.decEqOn r one

end IExpr

/-- Equality in the free Kleene interval: by normal form when possible,
otherwise by evaluation into the three-element Kleene algebra. -/
def ieq (r s : IExpr) : Bool :=
  let (cr, cs) := (dnf r false, dnf s false)
  cr == cs || kleene.decEqOn (ofClauses cr) (ofClauses cs)

/-- A face: a partial assignment of generators to endpoints, sorted by
generator and without repetition. -/
abbrev Face := List (Nat × Bool)

namespace Face

def lookup (α : Face) (i : Nat) : Option Bool :=
  (α.find? (·.1 == i)).map (·.2)

def mentions (α : Face) (i : Nat) : Bool :=
  (α.lookup i).isSome

/-- Extend by `i ↦ d`; `none` if `α` already sends `i` elsewhere. -/
def insert (i : Nat) (d : Bool) : Face → Option Face
  | [] => some [(i, d)]
  | (j, e) :: α =>
    if i < j then some ((i, d) :: (j, e) :: α)
    else if i == j then (if d == e then some ((j, e) :: α) else none)
    else ((j, e) :: ·) <$> insert i d α

/-- The conjunction of two faces; `none` if they disagree on a generator. -/
def meet (α β : Face) : Option Face :=
  β.foldlM (fun γ (i, d) => γ.insert i d) α

def compatible (α β : Face) : Bool :=
  (α.meet β).isSome

/-- `α ≤ β`: `α` is at least as specific as `β` (it fixes every generator `β` fixes, the same way). -/
def le (α β : Face) : Bool :=
  β.all fun (i, d) => α.lookup i == some d

/-- The generators fixed by `α` but not by `β`. -/
def minus (α β : Face) : Face :=
  α.filter fun (i, _) => !β.mentions i

/-- The substitution `α` performs on interval expressions. -/
def apply (α : Face) (r : IExpr) : IExpr :=
  r.mapVars fun i => match α.lookup i with
    | some d => .ofBool d
    | none => .var i

/-- The cofibration `α` denotes: the conjunction of its literals. -/
def toIExpr (α : Face) : IExpr :=
  match α.map (fun (i, d) => if d then IExpr.var i else .neg (.var i)) with
  | [] => .one
  | l :: ls => ls.foldl .meet l

end Face

/-- Keep only the maximal faces: drop any face that is at least as specific as
another one in the list. -/
def maximalFaces (fs : List Face) : List Face :=
  absorb fs

/-- The maximal faces on which `r = b`: the consistent clauses of the normal
form of `r` (of `¬r` for `b = false`); cubicaltt's `invFormula`. -/
def invFormula (r : IExpr) (b : Bool) : List Face :=
  (dnf r (!b)).filter Clause.consistent

end Kleenextt
