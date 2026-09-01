import Kleenextt.Eval

namespace Kleenextt

structure Cxt where
  env : Env := []
  types : List (String × Val) := []
  lvl : Nat := 0

namespace Cxt

def names (cxt : Cxt) : List String :=
  cxt.types.map (·.1)

/-- Extend with a bound variable (a fresh neutral). -/
def bind (cxt : Cxt) (x : String) (a : Val) : Cxt where
  env := .var cxt.lvl :: cxt.env
  types := (x, a) :: cxt.types
  lvl := cxt.lvl + 1

/-- Extend with a definition. -/
def define (cxt : Cxt) (x : String) (t a : Val) : Cxt where
  env := t :: cxt.env
  types := (x, a) :: cxt.types
  lvl := cxt.lvl + 1

def showVal (cxt : Cxt) (v : Val) : String :=
  (quote cxt.lvl v).pretty 0 cxt.names

end Cxt

private def lookupVar (x : String) : Nat → List (String × Val) → Except String (Nat × Val)
  | _, [] => throw s!"variable out of scope: {x}"
  | i, (x', a) :: tys => if x == x' then pure (i, a) else lookupVar x (i + 1) tys

mutual
  partial def check (cxt : Cxt) (t : Raw) (a : Val) : Except String Tm := do
    match t, a with
    | .lam x t, .pi _ a c =>
      return .lam x (← check (cxt.bind x a) t (c.apply (.var cxt.lvl)))
    | .letE x a t u, a' =>
      let a ← check cxt a .univ
      let va := eval cxt.env a
      let t ← check cxt t va
      let u ← check (cxt.define x (eval cxt.env t) va) u a'
      return .letE x a t u
    | t, a =>
      let (t, tty) ← infer cxt t
      unless conv cxt.lvl tty a do
        throw s!"type mismatch\nexpected: {cxt.showVal a}\ninferred: {cxt.showVal tty}"
      return t

  partial def infer (cxt : Cxt) : Raw → Except String (Tm × Val)
    | .var x => do
      let (i, a) ← lookupVar x 0 cxt.types
      pure (.var i, a)
    | .univ => pure (.univ, .univ)
    | .app t u => do
      let (t, tty) ← infer cxt t
      match tty with
      | .pi _ a c =>
        let u ← check cxt u a
        pure (.app t u, c.apply (eval cxt.env u))
      | tty => throw s!"expected a function type, inferred: {cxt.showVal tty}"
    | .lam .. => throw "can't infer a type for a lambda"
    | .pi x a b => do
      let a ← check cxt a .univ
      let b ← check (cxt.bind x (eval cxt.env a)) b .univ
      pure (.pi x a b, .univ)
    | .letE x a t u => do
      let a ← check cxt a .univ
      let va := eval cxt.env a
      let t ← check cxt t va
      let (u, uty) ← infer (cxt.define x (eval cxt.env t) va) u
      pure (.letE x a t u, uty)
end

end Kleenextt
