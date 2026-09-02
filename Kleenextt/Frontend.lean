import Lean
import Kleenextt.Check

/-! Lean as the surface language: object-level programs are written directly in
Lean files through the `kexpr` syntax category, and the `kdef`/`#knf`/`#ktype`/
`#kconv`/`#kfail` commands run the Kleenextt elaborator at elaboration time, so
object-level type errors surface as ordinary Lean errors. Only existing Lean
tokens are used, so the grammar reserves nothing new at the term level. -/

namespace Kleenextt

open Lean Elab Command

/-- A checked top-level object definition; `ty` and `tm` are metavariable-free
core terms in the context of the preceding definitions. -/
structure KDef where
  name : String
  ty : Tm
  tm : Tm

initialize kDefsExt : SimplePersistentEnvExtension KDef (Array KDef) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := Array.flatten
  }

/-- The context with every `kdef` so far defined. -/
def kCxt (defs : Array KDef) : Cxt :=
  defs.foldl (init := {}) fun cxt d =>
    cxt.define d.name (eval {} cxt.env d.tm) (eval {} cxt.env d.ty)

declare_syntax_cat kexpr
declare_syntax_cat kbinder
declare_syntax_cat kpibinder

syntax ident : kbinder
syntax "_" : kbinder
syntax "{" ident "}" : kbinder
syntax "{" ident " := " ident "}" : kbinder

syntax "(" ident+ " : " kexpr ")" : kpibinder
syntax "{" ident+ " : " kexpr "}" : kpibinder
syntax "{" ident+ "}" : kpibinder

syntax:max ident : kexpr
syntax:max "Type" : kexpr
syntax:max "_" : kexpr
syntax:max "(" kexpr ")" : kexpr
syntax:60 kexpr:60 kexpr:61 : kexpr
syntax:60 kexpr:60 "{" kexpr "}" : kexpr
syntax:60 kexpr:60 "{" ident " := " kexpr "}" : kexpr
syntax:25 kexpr:26 " → " kexpr:25 : kexpr
syntax:25 kpibinder+ " → " kexpr:25 : kexpr
syntax:25 kexpr:26 " -> " kexpr:25 : kexpr
syntax:25 kpibinder+ " -> " kexpr:25 : kexpr
syntax:10 "λ" kbinder+ " => " kexpr:10 : kexpr
syntax:10 "let " ident " : " kexpr " := " kexpr "; " kexpr:10 : kexpr

private def binderToRaw : TSyntax `kbinder → Except String (String × ArgKind)
  | `(kbinder| $x:ident) => pure (x.getId.toString, .expl)
  | `(kbinder| _) => pure ("_", .expl)
  | `(kbinder| {$x:ident}) => pure (x.getId.toString, .impl)
  | `(kbinder| {$n:ident := $x:ident}) => pure (x.getId.toString, .named n.getId.toString)
  | stx => throw s!"unsupported binder: {stx.raw.getKind}"

/-- A binder group as a list of (name, implicitness, domain). -/
private def piBinderToRaw (toRaw : TSyntax `kexpr → Except String Raw) :
    TSyntax `kpibinder → Except String (List (String × Icit × Raw))
  | `(kpibinder| ($xs:ident* : $a)) => do
    let a ← toRaw a
    pure (xs.toList.map fun x => (x.getId.toString, .expl, a))
  | `(kpibinder| {$xs:ident* : $a}) => do
    let a ← toRaw a
    pure (xs.toList.map fun x => (x.getId.toString, .impl, a))
  | `(kpibinder| {$xs:ident*}) =>
    pure (xs.toList.map fun x => (x.getId.toString, .impl, .hole))
  | stx => throw s!"unsupported binder: {stx.raw.getKind}"

partial def toRaw : TSyntax `kexpr → Except String Raw
  | `(kexpr| $x:ident) => pure (.var x.getId.toString)
  | `(kexpr| Type) => pure .univ
  | `(kexpr| _) => pure .hole
  | `(kexpr| ($e)) => toRaw e
  | `(kexpr| $t $u) => do pure (.app (← toRaw t) (← toRaw u) .expl)
  | `(kexpr| $t {$u}) => do pure (.app (← toRaw t) (← toRaw u) .impl)
  | `(kexpr| $t {$n:ident := $u}) => do pure (.app (← toRaw t) (← toRaw u) (.named n.getId.toString))
  | `(kexpr| $a → $b)
  | `(kexpr| $a -> $b) => do pure (.pi "_" .expl (← toRaw a) (← toRaw b))
  | `(kexpr| $bs:kpibinder* → $b)
  | `(kexpr| $bs:kpibinder* -> $b) => do
    let b ← toRaw b
    let bs ← bs.toList.mapM (piBinderToRaw toRaw)
    pure (bs.flatten.foldr (fun (x, i, a) acc => .pi x i a acc) b)
  | `(kexpr| λ $bs:kbinder* => $t) => do
    let t ← toRaw t
    let bs ← bs.mapM binderToRaw
    pure (bs.foldr (fun (x, k) acc => .lam x k acc) t)
  | `(kexpr| let $x:ident : $a := $t; $u) => do
    pure (.letE x.getId.toString (← toRaw a) (← toRaw t) (← toRaw u))
  | stx => throw s!"unsupported syntax: {stx.raw.getKind}"

private def orThrowAt [Monad m] [MonadError m] (ref : Syntax) : Except String α → m α
  | .error msg => throwErrorAt ref msg
  | .ok a => pure a

/-- Run an elaboration action in a fresh metavariable context. -/
private def runElab (act : ElabM α) : Except String (α × MetaCxt) :=
  act.run {}

elab "kdef " x:ident " : " a:kexpr " := " t:kexpr : command => do
  let cxt := kCxt (kDefsExt.getState (← getEnv))
  let r : Except String (Tm × Tm) := do
    let ((ty, tm), M) ← runElab do
      let ty ← check cxt (← toRaw a) .univ
      let M ← get
      let tm ← check cxt (← toRaw t) (eval M cxt.env ty)
      pure (ty, tm)
    pure (← zonk M cxt.env cxt.lvl ty, ← zonk M cxt.env cxt.lvl tm)
  let (ty, tm) ← orThrowAt x r
  modifyEnv (kDefsExt.addEntry · { name := x.getId.toString, ty, tm })

elab tk:"#knf " e:kexpr : command => do
  let cxt := kCxt (kDefsExt.getState (← getEnv))
  let r : Except String (String × String) := do
    let ((t, a), M) ← runElab do infer cxt (← toRaw e)
    pure ((nf M cxt.env t).pretty 0 cxt.names, cxt.showVal M a)
  let (n, ty) ← orThrowAt e r
  logInfoAt tk m!"{n}\n  : {ty}"

elab tk:"#ktype " e:kexpr : command => do
  let cxt := kCxt (kDefsExt.getState (← getEnv))
  let r : Except String String := do
    let ((_, a), M) ← runElab do infer cxt (← toRaw e)
    pure (cxt.showVal M a)
  logInfoAt tk m!"{← orThrowAt e r}"

/-- Assert that both sides elaborate, at unifiable types, to unifiable values. -/
elab "#kconv " a:kexpr " = " b:kexpr : command => do
  let cxt := kCxt (kDefsExt.getState (← getEnv))
  let r : Except String Unit := do
    let (_, _) ← runElab do
      let (ta, tya) ← infer cxt (← toRaw a)
      let (tb, tyb) ← infer cxt (← toRaw b)
      let M ← get
      try unify cxt.lvl tya tyb
      catch _ => throw s!"types differ:\n  {cxt.showVal M tya}\n  {cxt.showVal M tyb}"
      let M ← get
      try unify cxt.lvl (eval M cxt.env ta) (eval M cxt.env tb)
      catch _ =>
        throw s!"not convertible:\n  {(nf M cxt.env ta).pretty 0 cxt.names}\n  {(nf M cxt.env tb).pretty 0 cxt.names}"
    pure ()
  orThrowAt a r

/-- Assert that a term does not elaborate, or leaves metavariables unsolved. -/
elab "#kfail " e:kexpr : command => do
  let cxt := kCxt (kDefsExt.getState (← getEnv))
  let r : Except String (Tm × Tm) := do
    let ((t, a), M) ← runElab do infer cxt (← toRaw e)
    pure (← zonk M cxt.env cxt.lvl t, ← zonk M cxt.env cxt.lvl (quote M cxt.lvl a))
  match r with
  | .error _ => pure ()
  | .ok _ => throwErrorAt e "expected an elaboration error, but the term elaborated"

end Kleenextt
