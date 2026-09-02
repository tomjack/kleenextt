import Lean
import Kleenextt.Check

/-! Lean as the surface language: object-level programs are written directly in
Lean files through the `kexpr` syntax category, and the `kdef`/`#knf`/`#ktype`/
`#kconv`/`#kdiffer`/`#kfail` commands run the Kleenextt elaborator at
elaboration time, so object-level type errors surface as ordinary Lean errors.
Only existing Lean tokens are used, so the grammar reserves nothing new at the
term level; the cubical primitives are ordinary identifiers that `toRaw`
recognises at the head of an application. -/

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

/-- Names of `kdef`s the kernel's computation rules refer to. -/
initialize kBuiltinsExt : SimplePersistentEnvExtension String (List String) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun xs x => x :: xs
    addImportedFn := fun xss => xss.flatten.toList
  }

/-- The context with every `kdef` so far defined, and the globals with the
registered builtins. -/
def kCxt (defs : Array KDef) (builtins : List String) : Cxt × Globals :=
  defs.foldl (init := ({}, {})) fun (cxt, G) d =>
    let v := eval G cxt.lvl cxt.env d.tm
    let G := if builtins.contains d.name && d.name == "lineToEquiv" then { G with lineToEquiv := some v } else G
    (cxt.define d.name v (eval G cxt.lvl cxt.env d.ty), G)

declare_syntax_cat kexpr
declare_syntax_cat kbinder
declare_syntax_cat kpibinder
declare_syntax_cat kface
declare_syntax_cat kentry

syntax ident : kbinder
syntax "_" : kbinder
syntax "(" ident+ " : " kexpr ")" : kbinder
syntax "{" ident "}" : kbinder
syntax "{" ident " := " ident "}" : kbinder

syntax "(" ident+ " : " kexpr ")" : kpibinder
syntax "{" ident+ " : " kexpr "}" : kpibinder
syntax "{" ident+ "}" : kpibinder

syntax "(" kexpr " = " num ")" : kface
syntax kface+ " ↦ " kexpr : kentry

syntax:max ident : kexpr
syntax:max "Type" : kexpr
syntax:max "_" : kexpr
syntax:max num : kexpr
syntax:max "(" kexpr ")" : kexpr
syntax:max "(" kexpr ", " kexpr,+ ")" : kexpr
syntax:max "[" kentry,* "]" : kexpr
syntax:60 kexpr:60 kexpr:61 : kexpr
syntax:60 kexpr:60 "{" kexpr "}" : kexpr
syntax:60 kexpr:60 "{" ident " := " kexpr "}" : kexpr
syntax:40 "¬" kexpr:40 : kexpr
syntax:35 kexpr:36 " ∧ " kexpr:35 : kexpr
syntax:30 kexpr:31 " ∨ " kexpr:30 : kexpr
syntax:35 "(" ident " : " kexpr ")" " × " kexpr:35 : kexpr
syntax:35 kexpr:36 " × " kexpr:35 : kexpr
syntax:25 kexpr:26 " → " kexpr:25 : kexpr
syntax:25 kpibinder+ " → " kexpr:25 : kexpr
syntax:25 kexpr:26 " -> " kexpr:25 : kexpr
syntax:25 kpibinder+ " -> " kexpr:25 : kexpr
syntax:10 "λ" kbinder+ " => " kexpr:10 : kexpr
syntax:10 "let " ident " : " kexpr " := " kexpr "; " kexpr:10 : kexpr

/-- Lambda binders: name, implicitness, and an optional domain annotation. -/
private def binderToRaw (toRaw : TSyntax `kexpr → Except String Raw) :
    TSyntax `kbinder → Except String (List (String × ArgKind × Option Raw))
  | `(kbinder| $x:ident) => pure [(x.getId.toString, .expl, none)]
  | `(kbinder| _) => pure [("_", .expl, none)]
  | `(kbinder| ($xs:ident* : $a)) => do
    let a ← toRaw a
    pure (xs.toList.map fun x => (x.getId.toString, .expl, some a))
  | `(kbinder| {$x:ident}) => pure [(x.getId.toString, .impl, none)]
  | `(kbinder| {$n:ident := $x:ident}) => pure [(x.getId.toString, .named n.getId.toString, none)]
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

/-- Split an application spine into its head and explicit arguments. -/
private partial def spine (stx : TSyntax `kexpr) : TSyntax `kexpr × List (TSyntax `kexpr) :=
  match stx with
  | `(kexpr| $t $u) =>
    let (hd, args) := spine t
    (hd, args ++ [u])
  | _ => (stx, [])

/-- The special forms: primitives that take systems or bind variables, with
their arities. Further arguments are ordinary applications. -/
private def special (name : String) (args : List Raw) : Except String (Option Raw) := do
  let system (r : Raw) : Except String (List (Raw × Raw)) :=
    match r with
    | .system sys => pure sys
    | _ => throw s!"{name}: expected a system [φ ↦ t, …]"
  let boundSystem (r : Raw) : Except String (String × List (Raw × Raw)) :=
    match r with
    | .lam j .expl (.system sys) => pure (j, sys)
    | _ => throw s!"{name}: expected λ j => [φ ↦ t, …]"
  let line (r : Raw) : Except String (String × Raw) :=
    match r with
    | .lam i .expl a => pure (i, a)
    | _ => throw s!"{name}: expected λ i => A"
  let arity : Option Nat := match name with
    | "fst" | "snd" | "unglue" => some 1
    | "Glue" | "glue" => some 2
    | "transp" | "hcomp" | "ghcomp" | "comp" => some 3
    | "hfill" => some 4
    | _ => none
  match arity with
  | none => pure none
  | some n =>
    if args.length < n then throw s!"{name}: expected {n} arguments"
    let rest := args.drop n
    let hd ← match name, args.take n with
      | "fst", [t] => pure (Raw.fst t)
      | "snd", [t] => pure (Raw.snd t)
      | "unglue", [b] => pure (Raw.unglue b)
      | "Glue", [a, sys] => do pure (Raw.glueTy a (← system sys))
      | "glue", [sys, a] => do pure (Raw.glue (← system sys) a)
      | "transp", [a, r, u] => pure (Raw.transp a r u)
      | "hcomp", [a, sys, u] => do let (j, sys) ← boundSystem sys; pure (Raw.hcomp false a j sys u)
      | "ghcomp", [a, sys, u] => do let (j, sys) ← boundSystem sys; pure (Raw.hcomp true a j sys u)
      | "comp", [a, sys, u] => do
        let (i, a) ← line a
        let (j, sys) ← boundSystem sys
        pure (Raw.comp i a j sys u)
      | "hfill", [a, sys, u, r] => do let (j, sys) ← boundSystem sys; pure (Raw.hfill a j sys u r)
      | _, _ => throw s!"{name}: wrong number of arguments"
    pure (some (rest.foldl (fun f a => .app f a .expl) hd))

partial def toRaw : TSyntax `kexpr → Except String Raw
  | `(kexpr| $x:ident) => pure (.var x.getId.toString)
  | `(kexpr| Type) => pure .univ
  | `(kexpr| _) => pure .hole
  | `(kexpr| $n:num) =>
    match n.getNat with
    | 0 => pure .i0
    | 1 => pure .i1
    | _ => throw "the only interval literals are 0 and 1"
  | `(kexpr| ($e)) => toRaw e
  | `(kexpr| ($t, $us,*)) => do
    let ts ← (t :: us.getElems.toList).mapM toRaw
    match ts.reverse with
    | last :: rest => pure (rest.foldl (fun acc t => .pair t acc) last)
    | [] => throw "empty tuple"
  | `(kexpr| [$entries,*]) => do
    let sys ← entries.getElems.toList.mapM fun (entry : TSyntax `kentry) => do
      match entry with
      | `(kentry| $faces:kface* ↦ $t) =>
        let cofs ← faces.toList.mapM fun (face : TSyntax `kface) => do
          match face with
          | `(kface| ($r = $d:num)) =>
            let r ← toRaw r
            match d.getNat with
            | 1 => pure r
            | 0 => pure (.ineg r)
            | _ => throw "a face is (r = 0) or (r = 1)"
          | _ => throw "unsupported face"
        let φ := match cofs with
          | [] => Raw.i1
          | c :: cs => cs.foldl (fun acc c => .imeet acc c) c
        pure (φ, ← toRaw t)
      | _ => throw "unsupported system entry"
    pure (.system sys)
  | stx@`(kexpr| $_ $_) => do
    let (hd, args) := spine stx
    let args ← args.mapM toRaw
    match hd with
    | `(kexpr| $x:ident) =>
      match ← special x.getId.toString args with
      | some r => pure r
      | none => pure (args.foldl (fun f a => .app f a .expl) (.var x.getId.toString))
    | hd => do pure (args.foldl (fun f a => .app f a .expl) (← toRaw hd))
  | `(kexpr| $t {$u}) => do pure (.app (← toRaw t) (← toRaw u) .impl)
  | `(kexpr| $t {$n:ident := $u}) => do pure (.app (← toRaw t) (← toRaw u) (.named n.getId.toString))
  | `(kexpr| ¬ $r) => do pure (.ineg (← toRaw r))
  | `(kexpr| $r ∧ $s) => do pure (.imeet (← toRaw r) (← toRaw s))
  | `(kexpr| $r ∨ $s) => do pure (.ijoin (← toRaw r) (← toRaw s))
  | `(kexpr| ($x:ident : $a) × $b) => do pure (.sigma x.getId.toString (← toRaw a) (← toRaw b))
  | `(kexpr| $a × $b) => do pure (.sigma "_" (← toRaw a) (← toRaw b))
  | `(kexpr| $a → $b)
  | `(kexpr| $a -> $b) => do pure (.pi "_" .expl (← toRaw a) (← toRaw b))
  | `(kexpr| $bs:kpibinder* → $b)
  | `(kexpr| $bs:kpibinder* -> $b) => do
    let b ← toRaw b
    let bs ← bs.toList.mapM (piBinderToRaw toRaw)
    pure (bs.flatten.foldr (fun (x, i, a) acc => .pi x i a acc) b)
  | `(kexpr| λ $bs:kbinder* => $t) => do
    let t ← toRaw t
    let bs ← bs.toList.mapM (binderToRaw toRaw)
    -- An annotated binder `(x : A)` ascribes the type `(x : A) → _`.
    pure (bs.flatten.foldr (fun (x, k, a?) acc =>
      match a? with
      | some a => .ann (.lam x k acc) (.pi x .expl a .hole)
      | none => .lam x k acc) t)
  | `(kexpr| let $x:ident : $a := $t; $u) => do
    pure (.letE x.getId.toString (← toRaw a) (← toRaw t) (← toRaw u))
  | stx => throw s!"unsupported syntax: {stx.raw.getKind}"

private def orThrowAt [Monad m] [MonadError m] (ref : Syntax) : Except String α → m α
  | .error msg => throwErrorAt ref msg
  | .ok a => pure a

private def currentCxt : CommandElabM (Cxt × Globals) := do
  let env ← getEnv
  pure (kCxt (kDefsExt.getState env) (kBuiltinsExt.getState env))

elab "kdef " x:ident " : " a:kexpr " := " t:kexpr : command => do
  let (cxt, G) ← currentCxt
  let r : Except String (Tm × Tm) := do
    let ((ty, tm), G) ← (do
        let ty ← checkType cxt (← toRaw a)
        let G ← get
        let tm ← check cxt (← toRaw t) (eval G cxt.lvl cxt.env ty)
        pure (ty, tm) : ElabM (Tm × Tm)).run G
    pure (← zonk G cxt.env cxt.lvl ty, ← zonk G cxt.env cxt.lvl tm)
  let (ty, tm) ← orThrowAt x r
  modifyEnv (kDefsExt.addEntry · { name := x.getId.toString, ty, tm })

/-- Register a `kdef` the kernel's computation rules refer to. -/
elab "#kbuiltin " x:ident : command => do
  let defs := kDefsExt.getState (← getEnv)
  unless defs.any (·.name == x.getId.toString) do
    throwErrorAt x "not a kdef"
  modifyEnv (kBuiltinsExt.addEntry · x.getId.toString)

elab tk:"#knf " e:kexpr : command => do
  let (cxt, G) ← currentCxt
  let r : Except String (String × String) := do
    let ((t, a), G) ← (do infer cxt (← toRaw e) : ElabM (Tm × Val)).run G
    pure ((nf G cxt.env t).pretty 0 cxt.names, cxt.showVal G a)
  let (n, ty) ← orThrowAt e r
  logInfoAt tk m!"{n}\n  : {ty}"

elab tk:"#ktype " e:kexpr : command => do
  let (cxt, G) ← currentCxt
  let r : Except String String := do
    let ((_, a), G) ← (do infer cxt (← toRaw e) : ElabM (Tm × Val)).run G
    pure (cxt.showVal G a)
  logInfoAt tk m!"{← orThrowAt e r}"

/-- Infer the left side, check the right side against its type, and unify the
values; on failure return both normal forms. -/
private def convSides (cxt : Cxt) (a b : TSyntax `kexpr) : ElabM (Option (String × String)) := do
  let (ta, tya) ← infer cxt (← toRaw a)
  let tb ← check cxt (← toRaw b) tya
  let G ← get
  try
    unify cxt.lvl (eval G cxt.lvl cxt.env ta) (eval G cxt.lvl cxt.env tb)
    pure none
  catch _ =>
    let G ← get
    pure (some ((nf G cxt.env ta).pretty 0 cxt.names, (nf G cxt.env tb).pretty 0 cxt.names))

/-- Assert that the right side checks at the left side's type and that the
two are convertible. -/
elab "#kconv " a:kexpr " = " b:kexpr : command => do
  let (cxt, G) ← currentCxt
  match (convSides cxt a b).run G with
  | .error e => throwErrorAt a e
  | .ok (none, _) => pure ()
  | .ok (some (na, nb), _) => throwErrorAt a s!"not convertible:\n  {na}\n  {nb}"

/-- Assert that the right side checks at the left side's type but the two are
not convertible. -/
elab "#kdiffer " a:kexpr " = " b:kexpr : command => do
  let (cxt, G) ← currentCxt
  match (convSides cxt a b).run G with
  | .error e => throwErrorAt a e
  | .ok (some _, _) => pure ()
  | .ok (none, _) => throwErrorAt a "expected the sides to differ, but they are convertible"

/-- Assert that a term does not elaborate, or leaves metavariables unsolved. -/
elab "#kfail " e:kexpr : command => do
  let (cxt, G) ← currentCxt
  let r : Except String (Tm × Tm) := do
    let ((t, a), G) ← (do infer cxt (← toRaw e) : ElabM (Tm × Val)).run G
    pure (← zonk G cxt.env cxt.lvl t, ← zonk G cxt.env cxt.lvl (quote G cxt.lvl a))
  match r with
  | .error _ => pure ()
  | .ok _ => throwErrorAt e "expected an elaboration error, but the term elaborated"

end Kleenextt
