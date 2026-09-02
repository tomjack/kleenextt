import Kleenextt.Syntax

namespace Kleenextt

mutual
  /-- Semantic values. Neutrals are spines headed by a de Bruijn level
  (`rigid`) or by a metavariable (`flex`). Spines are snoc lists: the head
  of the list is the last argument. -/
  inductive Val where
    | rigid (l : Nat) (sp : List (Val × Icit))
    | flex (m : Nat) (sp : List (Val × Icit))
    | lam (x : String) (i : Icit) (c : Closure)
    | pi (x : String) (i : Icit) (a : Val) (c : Closure)
    | univ

  inductive Closure where
    | mk (env : List Val) (t : Tm)
end

instance : Inhabited Val := ⟨.univ⟩

abbrev Env := List Val
abbrev Spine := List (Val × Icit)

def Val.var (l : Nat) : Val := .rigid l []

inductive MetaEntry where
  | unsolved
  | solved (v : Val)

/-- Metavariables are numbered densely in creation order. -/
structure MetaCxt where
  entries : Array MetaEntry := #[]

def MetaCxt.lookup (M : MetaCxt) (m : Nat) : MetaEntry :=
  M.entries.getD m .unsolved

section
variable (M : MetaCxt)

mutual
  partial def Closure.apply : Closure → Val → Val
    | .mk env t, u => eval (u :: env) t

  partial def vApp (t u : Val) (i : Icit) : Val :=
    match t with
    | .lam _ _ c => c.apply u
    | .flex m sp => .flex m ((u, i) :: sp)
    | .rigid l sp => .rigid l ((u, i) :: sp)
    | _ => panic! "vApp: not a function"

  partial def vAppSp (t : Val) : Spine → Val
    | [] => t
    | (u, i) :: sp => vApp (vAppSp t sp) u i

  partial def vMeta (m : Nat) : Val :=
    match M.lookup m with
    | .solved v => v
    | .unsolved => .flex m []

  /-- Apply a meta to the bound variables of the environment it was created in. -/
  partial def vAppBDs (env : Env) (v : Val) (bds : List BD) : Val :=
    match env, bds with
    | [], [] => v
    | t :: env, .bound :: bds => vApp (vAppBDs env v bds) t .expl
    | _ :: env, .defined :: bds => vAppBDs env v bds
    | _, _ => panic! "vAppBDs: environment and binder list disagree"

  partial def eval (env : Env) : Tm → Val
    | .var i => env.getD i default
    | .app t u i => vApp (eval env t) (eval env u) i
    | .lam x i t => .lam x i (.mk env t)
    | .pi x i a b => .pi x i (eval env a) (.mk env b)
    | .letE _ _ t u => eval (eval env t :: env) u
    | .univ => .univ
    | .mvar m => vMeta m
    | .insertedMeta m bds => vAppBDs env (vMeta m) bds
end

/-- Unfold solved metavariables at the head. -/
partial def force (v : Val) : Val :=
  match v with
  | .flex m sp =>
    match M.lookup m with
    | .solved t => force (vAppSp M t sp)
    | .unsolved => v
  | v => v

/-- Read a value back into core syntax; `l` fresh-variable supply (levels → indices). -/
partial def quote (l : Nat) (v : Val) : Tm :=
  let rec quoteSp (t : Tm) : Spine → Tm
    | [] => t
    | (u, i) :: sp => .app (quoteSp t sp) (quote l u) i
  match force M v with
  | .flex m sp => quoteSp (.mvar m) sp
  | .rigid x sp => quoteSp (.var (l - x - 1)) sp
  | .lam x i c => .lam x i (quote (l + 1) (c.apply M (.var l)))
  | .pi x i a c => .pi x i (quote l a) (quote (l + 1) (c.apply M (.var l)))
  | .univ => .univ

def nf (env : Env) (t : Tm) : Tm :=
  quote M env.length (eval M env t)

end

end Kleenextt
