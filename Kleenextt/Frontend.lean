import Lean
import Kleenextt.Check

/-! Lean as the surface language: object-level programs are written directly in
Lean files through the `kexpr` syntax category, and the `kdef`/`#knf`/`#ktype`/
`#kconv`/`#kdiffer`/`#kfail` commands run the Kleenextt elaborator at
elaboration time, so object-level type errors surface as ordinary Lean errors.
Only existing Lean tokens are used, so the grammar reserves nothing new at the
term level; the cubical primitives are ordinary identifiers that `toRaw`
recognises at the head of an application. System faces are conjunctions of
`(i = 0)`/`(i = 1)` on variables, written by juxtaposition as in cubicaltt;
no other cofibrations can be written. -/

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

/-- Declared inductive types, most recent first. -/
initialize kDatasExt : SimplePersistentEnvExtension DataInfo (List DataInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun xs x => x :: xs
    addImportedFn := fun xss => xss.flatten.reverse.toList
  }

/-- The globals with every `kdef` so far defined (closed terms, evaluated in
order) and the inductive types; the elaboration context itself is empty. -/
def kCxt (defs : Array KDef) (datas : List DataInfo) : Cxt × Globals :=
  let G := defs.foldl (init := { datas : Globals }) fun G d =>
    let v := Thunk.mk fun _ => eval G 0 [] [] d.tm
    { G with defs := (d.name, v, eval G 0 [] [] d.ty) :: G.defs }
  ({}, G)

declare_syntax_cat kexpr
declare_syntax_cat kbinder
declare_syntax_cat kpibinder
declare_syntax_cat kface
declare_syntax_cat kentry
declare_syntax_cat kcase
declare_syntax_cat kcon

syntax ident : kbinder
syntax "_" : kbinder
syntax "(" ident+ " : " kexpr ")" : kbinder
syntax "{" ident "}" : kbinder
syntax "{" ident " := " ident "}" : kbinder

syntax "(" ident+ " : " kexpr ")" : kpibinder
syntax "{" ident+ " : " kexpr "}" : kpibinder
syntax "{" ident+ "}" : kpibinder

syntax "(" ident " = " num ")" : kface
syntax kface+ " ↦ " kexpr : kentry
syntax ident ident* " ↦ " kexpr : kcase
syntax ident kpibinder* ("[" kentry,* "]")? : kcon

syntax:max ident : kexpr
syntax:max "Type" : kexpr
syntax:max "sorry" : kexpr
syntax:max "case " kexpr:max kexpr:max "[" kcase,* "]" : kexpr
syntax:max "hlevel " num kexpr:max : kexpr
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

/-- System entries `(i = 0)(j = 1) ↦ t`: the face as a conjunction of literals. -/
private def entriesToRaw (toRaw : TSyntax `kexpr → Except String Raw)
    (entries : List (TSyntax `kentry)) : Except String (List (Raw × Raw)) :=
  entries.mapM fun (entry : TSyntax `kentry) => do
    match entry with
    | `(kentry| $faces:kface* ↦ $t) =>
      let cofs ← faces.toList.mapM fun (face : TSyntax `kface) => do
        match face with
        | `(kface| ($x:ident = $d:num)) =>
          let r := Raw.var x.getId.toString
          match d.getNat with
          | 1 => pure r
          | 0 => pure (.ineg r)
          | _ => throw "a face is (i = 0) or (i = 1)"
        | _ => throw "unsupported face"
      let φ := match cofs with
        | [] => Raw.i1
        | c :: cs => cs.foldl (fun acc c => .imeet acc c) c
      pure (φ, ← toRaw t)
    | _ => throw "unsupported system entry"

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
  -- `coe r r' (λ i => A) u` and `hcom r r' A (λ l => […]) u` are the Cartesian
  -- operations, expressed with connections: the direction `r → r'` is the
  -- interpolation `l ↦ (¬l ∧ r) ∨ (l ∧ r') ∨ (r ∧ r')`, whose last disjunct
  -- makes it constantly `r` when `r = r'`. The Cartesian law `r = r' ⇒ u₀`
  -- is the face `(r = r')`, expressible only when one endpoint is a constant:
  -- it is `coe`'s constancy cofibration and an extra side of `hcom`. With two
  -- variable endpoints `hcom k k` does not reduce to its base.
  let dir (r r' l : Raw) : Raw := .ijoin (.ijoin (.imeet (.ineg l) r) (.imeet l r')) (.imeet r r')
  let eqCof (r r' : Raw) : Option Raw :=
    match r, r' with
    | .i0, s | s, .i0 => some (.ineg s)
    | .i1, s | s, .i1 => some s
    | _, _ => none
  let arity : Option Nat := match name with
    | "fst" | "snd" | "unglue" => some 1
    | "Glue" | "glue" | "glueU" => some 2
    | "transp" | "hcomp" | "ghcomp" | "comp" => some 3
    | "hfill" | "coe" => some 4
    | "hcom" => some 5
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
      | "glueU", [sys, a] => do pure (Raw.glueU (← system sys) a)
      | "transp", [a, r, u] => pure (Raw.transp a r u)
      | "hcomp", [a, sys, u] => do let (j, sys) ← boundSystem sys; pure (Raw.hcomp false a j sys u)
      | "ghcomp", [a, sys, u] => do let (j, sys) ← boundSystem sys; pure (Raw.hcomp true a j sys u)
      | "comp", [a, sys, u] => do
        let (i, a) ← line a
        let (j, sys) ← boundSystem sys
        pure (Raw.comp i a j sys u)
      | "hfill", [a, sys, u, r] => do let (j, sys) ← boundSystem sys; pure (Raw.hfill a j sys u r)
      | "coe", [r, r', a, u] => do
        let (i, a) ← line a
        let j := i ++ "'"
        let some φ := eqCof r r' | throw "coe: one endpoint must be 0 or 1"
        pure (Raw.transp (.lam j .expl (.letE i (.var "I") (dir r r' (.var j)) a)) φ u)
      | "hcom", [r, r', a, sys, u] => do
        let (l, sys) ← boundSystem sys
        let l' := l ++ "'"
        let sys := sys.map fun (φ, t) => (φ, Raw.letE l (.var "I") (dir r r' (.var l')) t)
        let sys := match eqCof r r' with
          | some φ => sys ++ [(φ, u)]
          | none => sys
        pure (Raw.hcomp false a l' sys u)
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
  | `(kexpr| [$entries,*]) => do pure (.system (← entriesToRaw toRaw entries.getElems.toList))
  | `(kexpr| sorry) => pure .sorry
  | `(kexpr| hlevel $n:num $h) => do pure (.hlevel n.getNat (← toRaw h))
  | `(kexpr| case $x $P [$cs,*]) => do
    let cases ← cs.getElems.toList.mapM fun (c : TSyntax `kcase) => do
      match c with
      | `(kcase| $con:ident $xs:ident* ↦ $t) =>
        pure (con.getId.toString, xs.toList.map (·.getId.toString), ← toRaw t)
      | _ => throw "unsupported case"
    pure (.split (← toRaw x) (← toRaw P) cases)
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
  pure (kCxt (kDefsExt.getState env) (kDatasExt.getState env))

/-- `kdata D := c (x : A) … (i : I) … [ (i = 0) ↦ t, … ] | …`: a parameterless
inductive type, higher if a constructor binds interval variables. Field
types are checked in the context of the previous fields only (primitives
and other inductive types are in scope, `kdef`s are not). -/
elab "kdata " x:ident " := " cons:sepBy(kcon, " | ") : command => do
  let (_, G) ← currentCxt
  let name := x.getId.toString
  let mut d : DataInfo := { name, cons := [] }
  for con in cons.getElems do
    let (cname, binders, boundary) ← match con with
      | `(kcon| $c:ident $bs:kpibinder* $[[$es,*]]?) => do
        let bs ← orThrowAt con (bs.toList.mapM (piBinderToRaw toRaw))
        let es := match es with
          | some es => es.getElems.toList
          | none => []
        let es ← orThrowAt con (entriesToRaw toRaw es)
        pure (c.getId.toString, bs.flatten, es)
      | _ => throwErrorAt con "unsupported constructor"
    let isI : Raw → Bool
      | .var "I" => true
      | _ => false
    let fields := binders.takeWhile fun (_, _, a) => !isI a
    let ivars := binders.drop fields.length
    unless ivars.all (fun (_, _, a) => isI a) do
      throwErrorAt con "interval binders must come after the fields"
    let G' := { G with datas := d :: G.datas }
    let r : Except String ConInfo := do
      let (c, _) ← (do
        let mut c : Cxt := {}
        let mut fieldTms : List (String × Tm) := []
        for (f, _, a) in fields do
          let T ← check c a .univ
          let vT ← evalC c T
          c := c.bind f vT
          fieldTms := fieldTms ++ [(f, T)]
        for (i, _, _) in ivars do
          c := c.bind i .interval
        let (entries, _) ← checkFlatSys c boundary (.prim name [])
        let G ← get
        let entries ← entries.mapM fun (φ, t) => do pure (φ, ← zonk G c.env c.lvl t)
        let fields ← fieldTms.mapM fun (f, T) => do pure (f, ← zonk G [] 0 T)
        pure ({ name := cname, fields, ivars := ivars.map (·.1), boundary := entries } : ConInfo)
        : ElabM ConInfo).run G'
      pure c
    let con ← orThrowAt con r
    d := { d with cons := d.cons ++ [con] }
  modifyEnv (kDatasExt.addEntry · d)

elab "kdef " x:ident " : " a:kexpr " := " t:kexpr : command => do
  let (cxt, G) ← currentCxt
  let r : Except String (Tm × Tm) := do
    let ((ty, tm), G) ← (do
        let ty ← checkType cxt (← toRaw a)
        let G ← get
        let tm ← check cxt (← toRaw t) (eval G cxt.lvl [] cxt.env ty)
        pure (ty, tm) : ElabM (Tm × Tm)).run G
    pure (← zonk G cxt.env cxt.lvl ty, ← zonk G cxt.env cxt.lvl tm)
  let (ty, tm) ← orThrowAt x r
  modifyEnv (kDefsExt.addEntry · { name := x.getId.toString, ty, tm })

elab tk:"#knf " e:kexpr : command => do
  let (cxt, G) ← currentCxt
  let r : Except String (String × String) := do
    let ((t, a), G) ← (do infer cxt (← toRaw e) : ElabM (Tm × Val)).run G
    pure ((nf G cxt.env t).pretty 0 cxt.names, cxt.showVal G a)
  let (n, ty) ← orThrowAt e r
  logInfoAt tk m!"{n}\n  : {ty}"

/-- Normalise, reporting the time of evaluation and of quotation, the
evaluation counters, and the start of the normal form. -/
elab tk:"#ktime " e:kexpr : command => do
  let (cxt, G) ← currentCxt
  let r : Except String (Tm × Globals) := do
    let ((t, _), G) ← (do infer cxt (← toRaw e) : ElabM (Tm × Val)).run G
    pure (t, G)
  let (t, G) ← orThrowAt e r
  Stats.reset
  let t0 ← IO.monoMsNow
  let v ← IO.lazyPure fun _ => eval G cxt.lvl [] cxt.env t
  let t1 ← IO.monoMsNow
  let n ← IO.lazyPure fun _ => (quote G cxt.lvl v true).pretty 0 cxt.names
  let t2 ← IO.monoMsNow
  let s ← Stats.read
  let shown := if n.length > 200 then String.ofList (n.toList.take 200) ++ "…" else n
  logInfoAt tk m!"eval {t1 - t0} ms, quote {t2 - t1} ms\n  {s.pretty}\n  {shown}"

/-- `#ktime` on a task, printing the counters and the resident set size to
stderr every two seconds until it finishes: a growth curve that survives
running out of memory. The elaborator buffers the standard streams into
the message log, so the samples go through a fresh handle on the
process's stderr, or on the file named by `KTIME_LOG`. -/
elab tk:"#ktrace " e:kexpr : command => do
  let (cxt, G) ← currentCxt
  let r : Except String (Tm × Globals) := do
    let ((t, _), G) ← (do infer cxt (← toRaw e) : ElabM (Tm × Val)).run G
    pure (t, G)
  let (t, G) ← orThrowAt e r
  let err ← IO.FS.Handle.mk ((← IO.getEnv "KTIME_LOG").getD "/dev/stderr") .append
  Stats.reset
  let t0 ← IO.monoMsNow
  let task ← IO.asTask (prio := .dedicated) do
    let v ← IO.lazyPure fun _ => eval G cxt.lvl [] cxt.env t
    let t1 ← IO.monoMsNow
    let n ← IO.lazyPure fun _ => (quote G cxt.lvl v true).pretty 0 cxt.names
    pure (t1, n)
  let mut done := false
  while !done do
    IO.sleep 2000
    let ms := (← IO.monoMsNow) - t0
    err.putStrLn s!"[{ms / 1000} s, {← residentMB} MB] {(← Stats.read).pretty}"
    err.flush
    done ← IO.hasFinished task
  let (t1, n) ← IO.ofExcept task.get
  let t2 ← IO.monoMsNow
  let s ← Stats.read
  let shown := if n.length > 200 then String.ofList (n.toList.take 200) ++ "…" else n
  logInfoAt tk m!"eval {t1 - t0} ms, quote {t2 - t1} ms\n  {s.pretty}\n  {shown}"

private def showFaces {α : Type} (sys : List (Face × α)) : String :=
  "[" ++ ", ".intercalate (sys.map fun (α, _) =>
    if α.isEmpty then "⊤" else " ∧ ".intercalate (α.map fun (l, d) => s!"v{l}={if d then 1 else 0}")) ++ "]"

/-- The head constructor of a value with the faces of its systems, without
quoting the components. -/
private partial def headInfo (v : Val) (depth : Nat := 3) : String :=
  match v.whnf with
  | .hcomp _ sys u => s!"hcomp {showFaces sys} ({if depth == 0 then "…" else headInfo u (depth - 1)})"
  | .hcompU _ sys => s!"hcompU {showFaces sys}"
  | .glueU tySys us a => s!"glueU {showFaces tySys} {showFaces us} ({if depth == 0 then "…" else headInfo a (depth - 1)})"
  | .unglueU b sys => s!"unglueU {showFaces sys} ({if depth == 0 then "…" else headInfo b (depth - 1)})"
  | .glueTy _ sys => s!"Glue {showFaces sys}"
  | .glue tySys sys a => s!"glue {showFaces tySys} {showFaces sys} ({if depth == 0 then "…" else headInfo a (depth - 1)})"
  | .unglue b sys => s!"unglue {showFaces sys} ({if depth == 0 then "…" else headInfo b (depth - 1)})"
  | .transp _ r u => s!"transp {repr r} ({if depth == 0 then "…" else headInfo u (depth - 1)})"
  | .split _ _ _ x => s!"split ({if depth == 0 then "…" else headInfo x (depth - 1)})"
  | .prim n args => s!"{n}/{args.length}"
  | .pair .. => "pair"
  | .fst t => s!"fst ({if depth == 0 then "…" else headInfo t (depth - 1)})"
  | .snd t => s!"snd ({if depth == 0 then "…" else headInfo t (depth - 1)})"
  | .app .. => "app"
  | .papp .. => "papp"
  | .lam .. | .ilam .. | .line .. => "λ"
  | .pi .. => "Π"
  | .sigma .. => "Σ"
  | .pathP .. => "PathP"
  | .univ => "Type"
  | .interval => "I"
  | .i r => s!"{repr r}"
  | .var l => s!"var {l}"
  | .flex m _ => s!"?{m}"
  | .glued n sp _ => s!"{n}/{sp.length}"
  | .sub .. | .lazy .. | .cached .. => "unforced"

/-- The elaborated core term of `e`, with its type. -/
elab tk:"#kterm " e:kexpr : command => do
  let (cxt, G) ← currentCxt
  let r : Except String (String × String) := do
    let ((t, a), G) ← (do infer cxt (← toRaw e) : ElabM (Tm × Val)).run G
    pure ((← zonk G cxt.env cxt.lvl t).pretty 0 cxt.names, cxt.showVal G a)
  let (t, ty) ← orThrowAt e r
  logInfoAt tk m!"{t}\n  : {ty}"

/-- The head of `e` after instantiating `k` interval binders at fresh
variables, with the faces of its systems. -/
elab tk:"#khead " k:num e:kexpr : command => do
  let (cxt, G) ← currentCxt
  let r : Except String (Tm × Globals) := do
    let ((t, _), G) ← (do infer cxt (← toRaw e) : ElabM (Tm × Val)).run G
    pure (t, G)
  let (t, G) ← orThrowAt e r
  let k := k.getNat
  let v := (List.range k).foldl (fun v n => lineApp G (cxt.lvl + n + 1) [] v (.var (cxt.lvl + n))) (eval G cxt.lvl [] cxt.env t)
  let s ← IO.lazyPure fun _ => headInfo v
  logInfoAt tk s!"levels {cxt.lvl}..{cxt.lvl + k}: {s}"

/-- The system invariant on an `hcomp` value: after instantiating `k`
interval binders at fresh variables, every two sides must agree on their
common face and every side at `0` must agree with the base on its face,
by normal form. -/
elab tk:"#koverlaps " k:num e:kexpr : command => do
  let (cxt, G) ← currentCxt
  let r : Except String (Tm × Globals) := do
    let ((t, _), G) ← (do infer cxt (← toRaw e) : ElabM (Tm × Val)).run G
    pure (t, G)
  let (t, G) ← orThrowAt e r
  let k := k.getNat
  let L := cxt.lvl + k
  let names := (List.range k).foldl (fun ns n => s!"v{n}" :: ns) cxt.names
  let v := (List.range k).foldl (fun v n => lineApp G (cxt.lvl + n + 1) [] v (.var (cxt.lvl + n))) (eval G cxt.lvl [] cxt.env t)
  let head (s : String) : String := if s.length > 300 then String.ofList (s.toList.take 300) ++ "…" else s
  match v.whnf with
  | .hcomp _ sys u =>
    let mut report := s!"{showFaces sys}\n"
    -- Sides at the fresh level `L` against each other on common faces.
    let sides := (sys.map fun (α, s) => (α, s, lineApp G (L + 1) [] s (.var L))).toArray
    for hx : x in [0:sides.size] do
      let (α, s, sv) := sides[x]
      let gen ← IO.lazyPure fun _ => (face G (L + 1) [] α sv).headStr 3
      let lid ← IO.lazyPure fun _ => (face G L [] α (lineApp G L [] s .one)).headStr 3
      report := report ++ s!"side {showFaces [(α, ())]}: {gen}\n  at 1: {lid}\n"
      for hy : y in [x + 1:sides.size] do
        let (β, _, sv') := sides[y]
        if let some γ := α.meet β then
          let a ← IO.lazyPure fun _ => (quote G (L + 1) (face G (L + 1) [] γ sv)).pretty 0 ("l" :: names)
          let b ← IO.lazyPure fun _ => (quote G (L + 1) (face G (L + 1) [] γ sv')).pretty 0 ("l" :: names)
          if a != b then
            report := report ++ s!"DISAGREE on {showFaces [(γ, ())]}:\n  {head a}\n  {head b}\n"
      let a ← IO.lazyPure fun _ => (quote G L (face G L [] α (lineApp G L [] s .zero))).pretty 0 names
      let b ← IO.lazyPure fun _ => (quote G L (face G L [] α u)).pretty 0 names
      if a != b then
        report := report ++ s!"side {showFaces [(α, ())]} at 0 ≠ base:\n  {head a}\n  {head b}\n"
    logInfoAt tk report
  | w => logInfoAt tk s!"not an hcomp: {headInfo w}"

/-- Stability of evaluation under substitution: after instantiating `k`
interval binders of `e` at fresh variables, the next binder is instantiated
at a fresh variable with the endpoints then substituted, and directly at
each endpoint; the normal forms must agree. -/
elab tk:"#kstable " k:num e:kexpr : command => do
  let (cxt, G) ← currentCxt
  let r : Except String (Tm × Globals) := do
    let ((t, _), G) ← (do infer cxt (← toRaw e) : ElabM (Tm × Val)).run G
    pure (t, G)
  let (t, G) ← orThrowAt e r
  let k := k.getNat
  let L := cxt.lvl + k
  let names := (List.range k).foldl (fun ns n => s!"v{n}" :: ns) cxt.names
  let v := (List.range k).foldl (fun v n => lineApp G (cxt.lvl + n + 1) [] v (.var (cxt.lvl + n))) (eval G cxt.lvl [] cxt.env t)
  let generic := lineApp G (L + 1) [] v (.var L)
  let show_ (w : Val) : String := (quote G L w).pretty 0 names
  let head (s : String) : String := if s.length > 300 then String.ofList (s.toList.take 300) ++ "…" else s
  let gen ← IO.lazyPure fun _ => headInfo generic
  let mut report := s!"generic: {gen}\n"
  for (r, name) in [(IExpr.zero, "0"), (IExpr.one, "1")] do
    let viaSub ← IO.lazyPure fun _ => show_ (act G L [] [(L, r)] generic)
    let direct ← IO.lazyPure fun _ => show_ (lineApp G L [] v r)
    if viaSub == direct then report := report ++ s!"at {name}: stable\n  {head direct}\n"
    else report := report ++ s!"at {name}: UNSTABLE\n  substituted: {head viaSub}\n  direct:      {head direct}\n"
  logInfoAt tk report

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
    unify cxt.lvl (eval G cxt.lvl [] cxt.env ta) (eval G cxt.lvl [] cxt.env tb)
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
