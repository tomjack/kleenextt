import Kleenextt.Interval
import Kleenextt.Defun

/-! A toy semantic domain exercising `defun`: lines as derived closures,
with substitution and the support check derived over the captured fields. -/

namespace Kleenextt.DefunTest

abbrev Subst := List (Nat × IExpr)

def Subst.apply (σ : Subst) (r : IExpr) : IExpr :=
  (r.mapVars fun l => ((σ.find? (·.1 == l)).map (·.2)).getD (.var l)).norm

/-- Interval substitution on a field type. -/
class Act (α : Type) where
  act : Nat → Subst → α → α

/-- The interval levels a field may mention, as a bitmask. -/
class Vars (α : Type) where
  vars : α → Nat

def levelSet (ls : List Nat) : Nat := ls.foldl (· ||| 1 <<< ·) 0

instance : Act IExpr := ⟨fun _ σ r => σ.apply r⟩
instance : Vars IExpr := ⟨fun r => levelSet r.vars⟩
/-- A captured face is the face of the system component the closure is, so
substitution into the component is under a substitution making it hold. -/
instance : Act Face := ⟨fun _ σ α => α.filter fun (l, _) => (σ.find? (·.1 == l)).isNone⟩
instance : Vars Face := ⟨fun α => levelSet (α.map (·.1))⟩
instance [Act α] [Act β] : Act (α × β) := ⟨fun L σ (a, b) => (Act.act L σ a, Act.act L σ b)⟩
instance [Vars α] [Vars β] : Vars (α × β) := ⟨fun (a, b) => Vars.vars a ||| Vars.vars b⟩
instance [Act α] : Act (List α) := ⟨fun L σ xs => xs.map (Act.act L σ)⟩
instance [Vars α] : Vars (List α) := ⟨fun xs => xs.foldl (· ||| Vars.vars ·) 0⟩
instance : Act String := ⟨fun _ _ s => s⟩
instance : Vars String := ⟨fun _ => 0⟩

defun Line (L : Nat) (i : IExpr) : Val
  deriving act (L : Nat) (σ : Subst) via Act.act := act
  deriving vars : Nat folding (· ||| ·) 0 via Vars.vars := varsOf
in

inductive Val where
  | var (l : Nat)
  | i (r : IExpr)
  | line (c : Line)
  | app (t u : Val)
  | pair (u v : Val)
  | sys (entries : List (Face × Val))
  | tag (name : String) (v : Val)
  deriving Repr, BEq

instance : Inhabited Val := ⟨.var 0⟩

structure Globals where
  fuel : Nat

section
variable (G : Globals)
include G

mutual
  partial def lineApp (L : Nat) (f : Val) (r : IExpr) : Val :=
    match f with
    | .line c => c.apply L r
    | f => .app f (.i r)

  partial def vApp (L : Nat) (t u : Val) : Val :=
    match t, u with
    | .line c, .i r => c.apply L r
    | t, u => .app t u

  partial def act (L : Nat) (σ : Subst) (v : Val) : Val :=
    match v with
    | .var l => .var l
    | .i r => .i (σ.apply r)
    | .line c => .line (Line.act L σ c)
    | .app t u => vApp L (act L σ t) (act L σ u)
    | .pair u w => .pair (act L σ u) (act L σ w)
    | .sys es =>
      let _ : Act Val := ⟨act⟩
      .sys (Act.act L σ es)
    | .tag n v => .tag n (act L σ v)

  partial def varsOf (v : Val) : Nat :=
    match v with
    | .var _ => 0
    | .i r => Vars.vars r
    | .line c => Line.vars c
    | .app t u | .pair t u => varsOf t ||| varsOf u
    | .sys es =>
      let _ : Vars Val := ⟨varsOf⟩
      Vars.vars es
    | .tag _ v => varsOf v

  /-- The section variable is used but not captured. -/
  partial def constLine (v : Val) : Val :=
    .line (closure% fun _ _ => if G.fuel == 0 then v else v)

  /-- Captures a `match`-bound local. -/
  partial def firstLine (x : Val) : Val :=
    match x with
    | .pair a _ => .line (closure% fun _ _ => a)
    | x => constLine x

  /-- At `j`: the pair of `a j` and the line `k ↦ s (j ∧ k)`; the inner site
  captures the outer site's binder. -/
  partial def fill (a s : Val) : Val :=
    .line (closure% fun L1 j =>
      .pair (lineApp L1 a j) (.line (closure% fun L2 k => lineApp L2 s (.meet j k))))

  /-- A component under `α`, tagged; captures a face and a string. -/
  partial def component (name : String) (α : Face) (x : Val) : Val :=
    .line (closure% fun L1 _ => .tag name (act L1 (α.map fun (l, d) => (l, IExpr.ofBool d)) x))
end

end

end defun

#print Line

private def G : Globals := ⟨0⟩
private def ln : Val := fill G (.i (.var 1)) (.i (.var 5))

#eval ln

-- Sites became constructors holding exactly their captures.
#guard ln == .line (.fill_1 (.i (.var 1)) (.i (.var 5)))
#guard constLine G (.var 3) == .line (.constLine_1 (.var 3))
#guard firstLine G (.pair (.var 3) (.var 4)) == .line (.firstLine_1 (.var 3))

-- `apply` re-runs the site's body; the inner site captures the outer binder.
#guard lineApp G 3 ln (.var 2)
  == .pair (.app (.i (.var 1)) (.i (.var 2))) (.line (.fill_2 (.i (.var 5)) (.var 2)))

-- The support of a line is that of its captures.
#guard (varsOf G ln).testBit 5
#guard !(varsOf G ln).testBit 7

-- Substitution acts on the fields, and commutes with instantiation.
#guard act G 3 [(5, .one)] ln == fill G (.i (.var 1)) (.i .one)
#guard lineApp G 3 (act G 3 [(5, .one)] ln) (.var 2) == act G 3 [(5, .one)] (lineApp G 3 ln (.var 2))

-- Face fields are restricted to the levels the substitution leaves.
private def comp : Val := component G "c" [(4, true)] (.i (.meet (.var 4) (.var 6)))

#guard lineApp G 3 comp .zero == .tag "c" (.i (.var 6))
#guard act G 3 [(4, .one)] comp == component G "c" [] (.i (.var 6))

end Kleenextt.DefunTest
