import Kleenextt.Unify

/-! Bidirectional elaboration with implicit arguments, after elaboration-zoo 04:
implicit applications are inserted when an inferred type is an implicit Pi
(unless the term is an implicit lambda), and implicit lambdas are inserted
when checking against an implicit Pi. -/

namespace Kleenextt

/-- Whether a name came from the source or from an inserted implicit lambda;
only source names are in scope for lookup. -/
inductive NameOrigin where
  | source
  | inserted
  deriving DecidableEq

structure Cxt where
  env : Env := []
  types : List (String × NameOrigin × Val) := []
  bds : List BD := []
  lvl : Nat := 0

namespace Cxt

def names (cxt : Cxt) : List String :=
  cxt.types.map (·.1)

/-- Extend with a bound variable (a fresh neutral). -/
def bind (cxt : Cxt) (x : String) (a : Val) (origin := NameOrigin.source) : Cxt where
  env := .var cxt.lvl :: cxt.env
  types := (x, origin, a) :: cxt.types
  bds := .bound :: cxt.bds
  lvl := cxt.lvl + 1

/-- Extend with a definition. -/
def define (cxt : Cxt) (x : String) (t a : Val) : Cxt where
  env := t :: cxt.env
  types := (x, .source, a) :: cxt.types
  bds := .defined :: cxt.bds
  lvl := cxt.lvl + 1

def showVal (M : MetaCxt) (cxt : Cxt) (v : Val) : String :=
  (quote M cxt.lvl v).pretty 0 cxt.names

def showTm (cxt : Cxt) (t : Tm) : String :=
  t.pretty 0 cxt.names

/-- Close a value over the last variable of the context. -/
def closeVal (M : MetaCxt) (cxt : Cxt) (v : Val) : Closure :=
  .mk cxt.env (quote M (cxt.lvl + 1) v)

end Cxt

abbrev ElabM := StateT MetaCxt (Except String)

def freshMeta (cxt : Cxt) : ElabM Tm := do
  let M ← get
  let m := M.entries.size
  set { M with entries := M.entries.push .unsolved }
  pure (.insertedMeta m cxt.bds)

def unifyCatch (cxt : Cxt) (expected inferred : Val) : ElabM Unit := do
  try unify cxt.lvl expected inferred
  catch e =>
    let M ← get
    throw s!"type mismatch ({e})\nexpected: {cxt.showVal M expected}\ninferred: {cxt.showVal M inferred}"

/-- Insert fresh implicit applications while the type is an implicit Pi. -/
partial def insertAll (cxt : Cxt) (t : Tm) (a : Val) : ElabM (Tm × Val) := do
  let M ← get
  match force M a with
  | .pi _ .impl _ c =>
    let m ← freshMeta cxt
    insertAll cxt (.app t m .impl) (c.apply M (eval M cxt.env m))
  | a => pure (t, a)

/-- Insert implicit applications unless the term is an implicit lambda. -/
def insert (cxt : Cxt) : Tm × Val → ElabM (Tm × Val)
  | (t@(.lam _ .impl _), a) => pure (t, a)
  | (t, a) => insertAll cxt t a

/-- Insert implicit applications until the implicit Pi named `name`. -/
partial def insertUntilName (cxt : Cxt) (name : String) (t : Tm) (a : Val) : ElabM (Tm × Val) := do
  let M ← get
  match force M a with
  | a@(.pi x .impl _ c) =>
    if x == name then pure (t, a)
    else
      let m ← freshMeta cxt
      insertUntilName cxt name (.app t m .impl) (c.apply M (eval M cxt.env m))
  | _ => throw s!"no implicit argument named {name}"

private def lookupVar (x : String) : Nat → List (String × NameOrigin × Val) → Except String (Nat × Val)
  | _, [] => throw s!"variable out of scope: {x}"
  | i, (x', origin, a) :: tys =>
    if x == x' && origin == .source then pure (i, a) else lookupVar x (i + 1) tys

mutual
  partial def check (cxt : Cxt) (t : Raw) (a : Val) : ElabM Tm := do
    let M ← get
    match t, force M a with
    | .lam x k t, .pi x' i a c =>
      let fits := match k with
        | .expl => i == Icit.expl
        | .impl => i == Icit.impl
        | .named n => n == x' && i == Icit.impl
      if fits then
        return .lam x i (← check (cxt.bind x a) t (c.apply M (.var cxt.lvl)))
      else if i == Icit.impl then
        return .lam x' .impl (← check (cxt.bind x' a .inserted) (.lam x k t) (c.apply M (.var cxt.lvl)))
      else
        fallback cxt (.lam x k t) (.pi x' i a c)
    | t, .pi x .impl a c =>
      return .lam x .impl (← check (cxt.bind x a .inserted) t (c.apply M (.var cxt.lvl)))
    | .letE x a t u, a' =>
      let a ← check cxt a .univ
      let M ← get
      let va := eval M cxt.env a
      let t ← check cxt t va
      let M ← get
      let u ← check (cxt.define x (eval M cxt.env t) va) u a'
      return .letE x a t u
    | .hole, _ => freshMeta cxt
    | t, a => fallback cxt t a

  partial def fallback (cxt : Cxt) (t : Raw) (expected : Val) : ElabM Tm := do
    let (t, inferred) ← insert cxt (← infer cxt t)
    unifyCatch cxt expected inferred
    return t

  partial def infer (cxt : Cxt) : Raw → ElabM (Tm × Val)
    | .var x => do
      let (i, a) ← lookupVar x 0 cxt.types
      pure (.var i, a)
    | .univ => pure (.univ, .univ)
    | .app t u k => do
      let (i, t, tty) ← match k with
        | .named n =>
          let (t, tty) ← infer cxt t
          let (t, tty) ← insertUntilName cxt n t tty
          pure (Icit.impl, t, tty)
        | .impl =>
          let (t, tty) ← infer cxt t
          pure (Icit.impl, t, tty)
        | .expl =>
          let (t, tty) ← infer cxt t
          let (t, tty) ← insertAll cxt t tty
          pure (Icit.expl, t, tty)
      let M ← get
      let (a, c) ← match force M tty with
        | .pi _ i' a c =>
          if i != i' then throw "implicitness mismatch in application"
          pure (a, c)
        | tty =>
          let a := eval M cxt.env (← freshMeta cxt)
          let c := Closure.mk cxt.env (← freshMeta (cxt.bind "x" a))
          unifyCatch cxt tty (.pi "x" i a c)
          pure (a, c)
      let u ← check cxt u a
      let M ← get
      pure (.app t u i, c.apply M (eval M cxt.env u))
    | .lam x k t => do
      let i ← match k with
        | .expl => pure Icit.expl
        | .impl => pure Icit.impl
        | .named _ => throw "can't infer a type for a named implicit lambda"
      let M ← get
      let a := eval M cxt.env (← freshMeta cxt)
      let cxt' := cxt.bind x a
      let (t, b) ← insert cxt' (← infer cxt' t)
      let M ← get
      pure (.lam x i t, .pi x i a (cxt.closeVal M b))
    | .pi x i a b => do
      let a ← check cxt a .univ
      let M ← get
      let b ← check (cxt.bind x (eval M cxt.env a)) b .univ
      pure (.pi x i a b, .univ)
    | .letE x a t u => do
      let a ← check cxt a .univ
      let M ← get
      let va := eval M cxt.env a
      let t ← check cxt t va
      let M ← get
      let (u, uty) ← infer (cxt.define x (eval M cxt.env t) va) u
      pure (.letE x a t u, uty)
    | .hole => do
      let M ← get
      let a := eval M cxt.env (← freshMeta cxt)
      let t ← freshMeta cxt
      pure (t, a)
end

/-- Replace solved metavariables by their solutions; fail on unsolved ones. -/
partial def zonk (M : MetaCxt) (env : Env) (l : Nat) : Tm → Except String Tm
  | .mvar m => metaSolution m
  | .insertedMeta m bds => do
    let _ ← metaSolution m
    pure (quote M l (eval M env (.insertedMeta m bds)))
  | .var i => pure (.var i)
  | .univ => pure .univ
  | .app t u i => do pure (.app (← zonk M env l t) (← zonk M env l u) i)
  | .lam x i t => do pure (.lam x i (← zonk M (.var l :: env) (l + 1) t))
  | .pi x i a b => do pure (.pi x i (← zonk M env l a) (← zonk M (.var l :: env) (l + 1) b))
  | .letE x a t u => do
    pure (.letE x (← zonk M env l a) (← zonk M env l t) (← zonk M (.var l :: env) (l + 1) u))
where
  metaSolution (m : Nat) : Except String Tm :=
    match M.lookup m with
    | .solved v => pure (quote M l v)
    | .unsolved => throw s!"unsolved metavariable ?{m}"

end Kleenextt
