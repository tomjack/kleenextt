import Lean
import Kleenextt.Check

/-! Lean as the surface language: object-level programs are written directly in
Lean files through the `kexpr` syntax category, and the `kdef`/`#knf`/`#ktype`/
`#kconv`/`#kfail` commands run the Kleenextt checker at elaboration time, so
object-level type errors surface as ordinary Lean errors. Only existing Lean
tokens are used, so the grammar reserves nothing new at the term level. -/

namespace Kleenextt

open Lean Elab Command

/-- A checked top-level object definition; `ty` and `tm` are core terms in the
context of the preceding definitions. -/
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
    cxt.define d.name (eval cxt.env d.tm) (eval cxt.env d.ty)

declare_syntax_cat kexpr

syntax:max ident : kexpr
syntax:max "Type" : kexpr
syntax:max "(" kexpr ")" : kexpr
syntax:60 kexpr:60 kexpr:61 : kexpr
syntax:25 kexpr:26 " → " kexpr:25 : kexpr
syntax:25 "(" ident+ " : " kexpr ")" " → " kexpr:25 : kexpr
syntax:25 kexpr:26 " -> " kexpr:25 : kexpr
syntax:25 "(" ident+ " : " kexpr ")" " -> " kexpr:25 : kexpr
syntax:10 "λ" ident+ " => " kexpr:10 : kexpr
syntax:10 "let " ident " : " kexpr " := " kexpr "; " kexpr:10 : kexpr

partial def toRaw : TSyntax `kexpr → Except String Raw
  | `(kexpr| $x:ident) => pure (.var x.getId.toString)
  | `(kexpr| Type) => pure .univ
  | `(kexpr| ($e)) => toRaw e
  | `(kexpr| $t $u) => do pure (.app (← toRaw t) (← toRaw u))
  | `(kexpr| $a → $b)
  | `(kexpr| $a -> $b) => do pure (.pi "_" (← toRaw a) (← toRaw b))
  | `(kexpr| ($xs:ident* : $a) → $b)
  | `(kexpr| ($xs:ident* : $a) -> $b) => do
    let a ← toRaw a
    let b ← toRaw b
    pure (xs.foldr (fun x acc => .pi x.getId.toString a acc) b)
  | `(kexpr| λ $xs:ident* => $t) => do
    let t ← toRaw t
    pure (xs.foldr (fun x acc => .lam x.getId.toString acc) t)
  | `(kexpr| let $x:ident : $a := $t; $u) => do
    pure (.letE x.getId.toString (← toRaw a) (← toRaw t) (← toRaw u))
  | stx => throw s!"unsupported syntax: {stx.raw.getKind}"

private def orThrowAt [Monad m] [MonadError m] (ref : Syntax) : Except String α → m α
  | .error msg => throwErrorAt ref msg
  | .ok a => pure a

elab "kdef " x:ident " : " a:kexpr " := " t:kexpr : command => do
  let cxt := kCxt (kDefsExt.getState (← getEnv))
  let r : Except String (Tm × Tm) := do
    let ty ← check cxt (← toRaw a) .univ
    let tm ← check cxt (← toRaw t) (eval cxt.env ty)
    pure (ty, tm)
  let (ty, tm) ← orThrowAt x r
  modifyEnv (kDefsExt.addEntry · { name := x.getId.toString, ty, tm })

elab tk:"#knf " e:kexpr : command => do
  let cxt := kCxt (kDefsExt.getState (← getEnv))
  let r : Except String (String × String) := do
    let (t, a) ← infer cxt (← toRaw e)
    pure ((nf cxt.env t).pretty 0 cxt.names, cxt.showVal a)
  let (n, ty) ← orThrowAt e r
  logInfoAt tk m!"{n}\n  : {ty}"

elab tk:"#ktype " e:kexpr : command => do
  let cxt := kCxt (kDefsExt.getState (← getEnv))
  let r : Except String String := do
    let (_, a) ← infer cxt (← toRaw e)
    pure (cxt.showVal a)
  logInfoAt tk m!"{← orThrowAt e r}"

/-- Assert that both sides typecheck, at convertible types, to convertible values. -/
elab "#kconv " a:kexpr " = " b:kexpr : command => do
  let cxt := kCxt (kDefsExt.getState (← getEnv))
  let va ← orThrowAt a (do infer cxt (← toRaw a))
  let vb ← orThrowAt b (do infer cxt (← toRaw b))
  unless conv cxt.lvl va.2 vb.2 do
    throwErrorAt a m!"types differ:\n  {cxt.showVal va.2}\n  {cxt.showVal vb.2}"
  unless conv cxt.lvl (eval cxt.env va.1) (eval cxt.env vb.1) do
    throwErrorAt a
      m!"not convertible:\n  {(nf cxt.env va.1).pretty 0 cxt.names}\n  {(nf cxt.env vb.1).pretty 0 cxt.names}"

/-- Assert that a term is ill-typed. -/
elab "#kfail " e:kexpr : command => do
  let cxt := kCxt (kDefsExt.getState (← getEnv))
  match do infer cxt (← toRaw e) with
  | .error _ => pure ()
  | .ok _ => throwErrorAt e "expected a type error, but the term typechecked"

end Kleenextt
