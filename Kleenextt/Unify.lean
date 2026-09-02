import Std.Data.HashMap
import Kleenextt.Eval

/-! Pattern unification, after elaboration-zoo 04. A metavariable applied to
distinct bound variables is solved by inverting the spine into a partial
renaming and renaming the other side under it. -/

namespace Kleenextt

abbrev UnifyM := StateT MetaCxt (Except String)

/-- Partial renaming from `Γ` (size `dom`) to `Δ` (size `cod`): `ren` maps
levels of `Δ` to levels of `Γ`. -/
structure PRen where
  dom : Nat
  cod : Nat
  ren : Std.HashMap Nat Nat

namespace PRen

/-- Lift over an extra bound variable. -/
def lift (p : PRen) : PRen :=
  { dom := p.dom + 1, cod := p.cod + 1, ren := p.ren.insert p.cod p.dom }

end PRen

/-- Invert a spine of distinct bound variables. -/
def invert (M : MetaCxt) (gamma : Nat) (sp : Spine) : Except String PRen := do
  let rec go : Spine → Except String (Nat × Std.HashMap Nat Nat)
    | [] => pure (0, {})
    | (t, _) :: sp => do
      let (dom, ren) ← go sp
      match force M t with
      | .rigid x [] =>
        if ren.contains x then throw "unify: non-linear spine"
        else pure (dom + 1, ren.insert x dom)
      | _ => throw "unify: spine argument is not a variable"
  let (dom, ren) ← go sp
  pure { dom, cod := gamma, ren }

/-- Rename `v` under `pren` into a term in `pren.dom`, failing on an
occurrence of `m` or of a variable outside the renaming. -/
partial def rename (M : MetaCxt) (m : Nat) : PRen → Val → Except String Tm
  | pren, v => do
    let rec goSp (pren : PRen) (t : Tm) : Spine → Except String Tm
      | [] => pure t
      | (u, i) :: sp => do pure (.app (← goSp pren t sp) (← rename M m pren u) i)
    match force M v with
    | .flex m' sp =>
      if m == m' then throw "unify: occurs check"
      else goSp pren (.mvar m') sp
    | .rigid x sp =>
      match pren.ren.get? x with
      | none => throw "unify: variable escapes its scope"
      | some x' => goSp pren (.var (pren.dom - x' - 1)) sp
    | .lam x i c => do pure (.lam x i (← rename M m pren.lift (c.apply M (.var pren.cod))))
    | .pi x i a c => do
      pure (.pi x i (← rename M m pren a) (← rename M m pren.lift (c.apply M (.var pren.cod))))
    | .univ => pure .univ

/-- Wrap a term in lambdas matching the spine's implicitness. -/
private def lams (is : List Icit) (t : Tm) : Tm :=
  let rec go (n : Nat) : List Icit → Tm
    | [] => t
    | i :: is => .lam s!"x{n + 1}" i (go (n + 1) is)
  go 0 is

def solve (gamma : Nat) (m : Nat) (sp : Spine) (rhs : Val) : UnifyM Unit := do
  let M ← get
  let pren ← invert M gamma sp
  let rhs ← rename M m pren rhs
  let solution := eval M [] (lams (sp.map (·.2)).reverse rhs)
  set { M with entries := M.entries.set! m (.solved solution) }

mutual
  partial def unifySp (l : Nat) : Spine → Spine → UnifyM Unit
    | [], [] => pure ()
    | (t, _) :: sp, (t', _) :: sp' => do unifySp l sp sp'; unify l t t'
    | _, _ => throw "unify: spine length mismatch"

  partial def unify (l : Nat) (t u : Val) : UnifyM Unit := do
    let M ← get
    match force M t, force M u with
    | .lam _ _ c, .lam _ _ c' => unify (l + 1) (c.apply M (.var l)) (c'.apply M (.var l))
    | t, .lam _ i c' => unify (l + 1) (vApp M t (.var l) i) (c'.apply M (.var l))
    | .lam _ i c, t' => unify (l + 1) (c.apply M (.var l)) (vApp M t' (.var l) i)
    | .univ, .univ => pure ()
    | .pi _ i a c, .pi _ i' a' c' =>
      if i != i' then throw "unify: implicitness mismatch"
      unify l a a'
      unify (l + 1) (c.apply M (.var l)) (c'.apply M (.var l))
    | .rigid x sp, .rigid x' sp' =>
      if x == x' then unifySp l sp sp' else throw "unify: rigid mismatch"
    | .flex m sp, .flex m' sp' =>
      if m == m' then unifySp l sp sp' else solve l m sp (.flex m' sp')
    | .flex m sp, t' => solve l m sp t'
    | t, .flex m' sp' => solve l m' sp' t
    | _, _ => throw "unify: rigid mismatch"
end

end Kleenextt
