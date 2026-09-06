import Kleenextt.Syntax
import Kleenextt.Symbols
import Kleenextt.Cache
import Kleenextt.Core.Check

/-! From `kcmd` syntax to the elaborator: a `.ktt` file is a sequence of
commands run against a `KState`, whose imports are other `.ktt` files. -/

namespace Kleenextt.Frontend

open Lean Core

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

private partial def spine (stx : TSyntax `kexpr) : TSyntax `kexpr × List (TSyntax `kexpr) :=
  match stx with
  | `(kexpr| $t $u) =>
    let (hd, args) := spine t
    (hd, args ++ [u])
  | _ => (stx, [])

/-- Primitives that take systems or bind variables; further arguments are
ordinary applications. -/
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
  -- Cartesian `coe`/`hcom` by connections: `r → r'` is
  -- `l ↦ (¬l ∧ r) ∨ (l ∧ r') ∨ (r ∧ r')`, constant when `r = r'`. The face
  -- `(r = r')` needs a constant endpoint, so `hcom k k` does not reduce.
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
    pure (bs.flatten.foldr (fun (x, k, a?) acc =>
      match a? with
      | some a => .ann (.lam x k acc) (.pi x .expl a .hole)
      | none => .lam x k acc) t)
  | `(kexpr| let $x:ident : $a := $t; $u) => do
    pure (.letE x.getId.toString (← toRaw a) (← toRaw t) (← toRaw u))
  | stx => throw s!"unsupported syntax: {stx.raw.getKind}"

/-- Zonked core terms in the context of the preceding definitions. -/
structure KDef where
  name : String
  ty : Tm
  tm : Tm

/-- A checked file's own definitions, in order; `path` is real. -/
structure KModule where
  path : String
  defs : Array KDef
  datas : Array DataInfo
  /-- Errors reported while checking this file, its imports aside. -/
  errors : Nat
  /-- The names its commands define, in order. -/
  symbols : Array Symbols.Symbol

/-- Imports first, in dependency order, then the file's own definitions. -/
structure KState where
  imports : Array KModule := #[]
  defs : Array KDef := #[]
  datas : Array DataInfo := #[]

namespace KState

def allDefs (st : KState) : Array KDef :=
  st.imports.foldl (fun acc m => acc ++ m.defs) #[] ++ st.defs

def allDatas (st : KState) : Array DataInfo :=
  st.imports.foldl (fun acc m => acc ++ m.datas) #[] ++ st.datas

/-- Every definition so far, evaluated in order, in an empty context. -/
def cxt (st : KState) : Cxt × Globals :=
  let G := st.allDefs.foldl (init := { datas := st.allDatas.toList.reverse : Globals }) fun G d =>
    let v := Thunk.mk fun _ => eval G 0 [] [] d.tm
    { G with defs := (d.name, v, eval G 0 [] [] d.ty) :: G.defs }
  ({}, G)

/-- Add an import's closure, skipping modules already present. -/
def addImports (st : KState) (closure : Array KModule) : KState :=
  closure.foldl (init := st) fun st m =>
    if st.imports.any (·.path == m.path) then st else { st with imports := st.imports.push m }

def toModule (st : KState) (path : String) (errors : Nat) (symbols : Array Symbols.Symbol) : KModule :=
  { path, defs := st.defs, datas := st.datas, errors, symbols }

end KState

private def liftE : Except String α → IO α
  | .error msg => throw (IO.userError msg)
  | .ok a => pure a

private def infoOf (cxt : Cxt) (G : Globals) (e : TSyntax `kexpr) : IO (Tm × Val × Globals) := do
  liftE do
    let ((t, a), G) ← (do infer cxt (← toRaw e) : ElabM (Tm × Val)).run G
    pure (t, a, G)

private def elabData (st : KState) (x : Ident) (cons : Array (TSyntax `kcon)) : IO KState := do
  let (_, G) := st.cxt
  let name := x.getId.toString
  let mut d : DataInfo := { name, cons := [] }
  for con in cons do
    let (cname, binders, boundary) ← match con with
      | `(kcon| $c:ident $bs:kpibinder* $[[$es,*]]?) => do
        let bs ← liftE (bs.toList.mapM (piBinderToRaw toRaw))
        let es := match es with
          | some es => es.getElems.toList
          | none => []
        let es ← liftE (entriesToRaw toRaw es)
        pure (c.getId.toString, bs.flatten, es)
      | _ => throw (IO.userError "unsupported constructor")
    let isI : Raw → Bool
      | .var "I" => true
      | _ => false
    let fields := binders.takeWhile fun (_, _, a) => !isI a
    let ivars := binders.drop fields.length
    unless ivars.all (fun (_, _, a) => isI a) do
      throw (IO.userError "interval binders must come after the fields")
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
    let con ← liftE r
    d := { d with cons := d.cons ++ [con] }
  pure { st with datas := st.datas.push d }

private def elabDef (st : KState) (x : Ident) (a : TSyntax `kexpr) (t : Raw) : IO KState := do
  let (cxt, G) := st.cxt
  let r : Unit → Except String (Tm × Tm) := fun _ => do
    let ((ty, tm), G) ← (do
        let ty ← checkType cxt (← toRaw a)
        let G ← get
        let tm ← check cxt t (eval G cxt.lvl [] cxt.env ty)
        pure (ty, tm) : ElabM (Tm × Tm)).run G
    pure (← zonk G cxt.env cxt.lvl ty, ← zonk G cxt.env cxt.lvl tm)
  -- `KDEF_TRACE`: as `#trace`; `KDEF_TIME`: one line per definition, on
  -- the elaborating thread.
  let r ← if (← IO.getEnv "KDEF_TRACE").isSome then do
    let err ← IO.FS.Handle.mk ((← IO.getEnv "KTRACE_LOG").getD "/dev/stderr") .append
    Stats.reset
    let t0 ← IO.monoMsNow
    let task ← IO.asTask (prio := .dedicated) (IO.lazyPure fun _ => r ())
    let mut done := false
    while !done do
      IO.sleep 2000
      let ms := (← IO.monoMsNow) - t0
      err.putStrLn s!"[{x.getId} {ms / 1000} s, {← residentMB} MB] {(← Stats.read).pretty}"
      err.flush
      done ← IO.hasFinished task
    IO.ofExcept task.get
  else if (← IO.getEnv "KDEF_TIME").isSome then do
    let err ← IO.FS.Handle.mk ((← IO.getEnv "KTRACE_LOG").getD "/dev/stderr") .append
    Stats.reset
    let t0 ← IO.monoMsNow
    let r ← IO.lazyPure fun _ => r ()
    let ms := (← IO.monoMsNow) - t0
    err.putStrLn s!"[{x.getId} {ms} ms, {← residentMB} MB] {(← Stats.read).pretty}"
    err.flush
    pure r
  else pure (r ())
  let (ty, tm) ← liftE r
  pure { st with defs := st.defs.push { name := x.getId.toString, ty, tm } }

private def showFaces {α : Type} (sys : List (Face × α)) : String :=
  "[" ++ ", ".intercalate (sys.map fun (α, _) =>
    if α.isEmpty then "⊤" else " ∧ ".intercalate (α.map fun (l, d) => s!"v{l}={if d then 1 else 0}")) ++ "]"

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

private def truncate (n : Nat) (s : String) : String :=
  if s.length > n then String.ofList (s.toList.take n) ++ "…" else s

/-- The normal form of `e` and its type, as `#nf`. -/
def normalize (st : KState) (e : TSyntax `kexpr) : IO String := do
  let (cxt, G) := st.cxt
  let (t, a, G) ← infoOf cxt G e
  pure s!"{(nf G cxt.env t).pretty 0 cxt.names}\n  : {cxt.showVal G a}"

/-- Timings, counters, and the start of the normal form. -/
private def time (st : KState) (e : TSyntax `kexpr) : IO String := do
  let (cxt, G) := st.cxt
  let (t, _, G) ← infoOf cxt G e
  Stats.reset
  let t0 ← IO.monoMsNow
  let v ← IO.lazyPure fun _ => eval G cxt.lvl [] cxt.env t
  let t1 ← IO.monoMsNow
  let n ← IO.lazyPure fun _ => (quote G cxt.lvl v true).pretty 0 cxt.names
  let t2 ← IO.monoMsNow
  let s ← Stats.read
  pure s!"eval {t1 - t0} ms, quote {t2 - t1} ms\n  {s.pretty}\n  {truncate 200 n}"

/-- `#trace`: `#time`, sampling counters and resident size every two seconds
through a fresh stderr handle (or `KTRACE_LOG`), since the elaborator
captures the standard streams. -/
private def trace (st : KState) (e : TSyntax `kexpr) : IO String := do
  let (cxt, G) := st.cxt
  let (t, _, G) ← infoOf cxt G e
  let err ← IO.FS.Handle.mk ((← IO.getEnv "KTRACE_LOG").getD "/dev/stderr") .append
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
  pure s!"eval {t1 - t0} ms, quote {t2 - t1} ms\n  {s.pretty}\n  {truncate 200 n}"

private def term (st : KState) (e : TSyntax `kexpr) : IO String := do
  let (cxt, G) := st.cxt
  let (t, a, G) ← infoOf cxt G e
  let t ← liftE (zonk G cxt.env cxt.lvl t)
  pure s!"{t.pretty 0 cxt.names}\n  : {cxt.showVal G a}"

private def type (st : KState) (e : TSyntax `kexpr) : IO String := do
  let (cxt, G) := st.cxt
  let (_, a, G) ← infoOf cxt G e
  pure (cxt.showVal G a)

/-- `e` applied to `k` fresh interval variables. -/
private def atFresh (st : KState) (k : Nat) (e : TSyntax `kexpr) : IO (Cxt × Globals × Val × List String) := do
  let (cxt, G) := st.cxt
  let (t, _, G) ← infoOf cxt G e
  let names := (List.range k).foldl (fun ns n => s!"v{n}" :: ns) cxt.names
  let v := (List.range k).foldl (fun v n => lineApp G (cxt.lvl + n + 1) [] v (.var (cxt.lvl + n))) (eval G cxt.lvl [] cxt.env t)
  pure (cxt, G, v, names)

/-- The head after `k` fresh interval binders, with its system faces. -/
private def head (st : KState) (k : Nat) (e : TSyntax `kexpr) : IO String := do
  let (cxt, _, v, _) ← atFresh st k e
  let s ← IO.lazyPure fun _ => headInfo v
  pure s!"levels {cxt.lvl}..{cxt.lvl + k}: {s}"

/-- After `k` fresh binders: the sides of an `hcomp` must agree on common
faces, and at `0` with the base. -/
private def overlaps (st : KState) (k : Nat) (e : TSyntax `kexpr) : IO String := do
  let (cxt, G, v, names) ← atFresh st k e
  let L := cxt.lvl + k
  match v.whnf with
  | .hcomp _ sys u =>
    let mut report := s!"{showFaces sys}\n"
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
            report := report ++ s!"DISAGREE on {showFaces [(γ, ())]}:\n  {truncate 300 a}\n  {truncate 300 b}\n"
      let a ← IO.lazyPure fun _ => (quote G L (face G L [] α (lineApp G L [] s .zero))).pretty 0 names
      let b ← IO.lazyPure fun _ => (quote G L (face G L [] α u)).pretty 0 names
      if a != b then
        report := report ++ s!"side {showFaces [(α, ())]} at 0 ≠ base:\n  {truncate 300 a}\n  {truncate 300 b}\n"
    pure report
  | w => pure s!"not an hcomp: {headInfo w}"

/-- After `k` fresh binders: the next one at a fresh variable then
substituted, against directly at each endpoint. -/
private def stable (st : KState) (k : Nat) (e : TSyntax `kexpr) : IO String := do
  let (cxt, G, v, names) ← atFresh st k e
  let L := cxt.lvl + k
  let generic := lineApp G (L + 1) [] v (.var L)
  let show_ (w : Val) : String := (quote G L w).pretty 0 names
  let gen ← IO.lazyPure fun _ => headInfo generic
  let mut report := s!"generic: {gen}\n"
  for (r, name) in [(IExpr.zero, "0"), (IExpr.one, "1")] do
    let viaSub ← IO.lazyPure fun _ => show_ (act G L [] [(L, r)] generic)
    let direct ← IO.lazyPure fun _ => show_ (lineApp G L [] v r)
    if viaSub == direct then report := report ++ s!"at {name}: stable\n  {truncate 300 direct}\n"
    else report := report ++ s!"at {name}: UNSTABLE\n  substituted: {truncate 300 viaSub}\n  direct:      {truncate 300 direct}\n"
  pure report

/-- Infer the left, check the right against its type, unify; on failure both
normal forms. -/
private def convSides (st : KState) (a b : TSyntax `kexpr) : IO (Option (String × String)) := do
  let (cxt, G) := st.cxt
  liftE <| (·.1) <$> (do
    let (ta, tya) ← infer cxt (← toRaw a)
    let tb ← check cxt (← toRaw b) tya
    let G ← get
    try
      unify cxt.lvl (eval G cxt.lvl [] cxt.env ta) (eval G cxt.lvl [] cxt.env tb)
      pure none
    catch _ =>
      let G ← get
      pure (some ((nf G cxt.env ta).pretty 0 cxt.names, (nf G cxt.env tb).pretty 0 cxt.names))
    : ElabM (Option (String × String))).run G

/-- Fails to elaborate, or leaves metavariables unsolved. -/
private def fails (st : KState) (e : TSyntax `kexpr) : IO Bool := do
  let (cxt, G) := st.cxt
  let r : Except String (Tm × Tm) := do
    let ((t, a), G) ← (do infer cxt (← toRaw e) : ElabM (Tm × Val)).run G
    pure (← zonk G cxt.env cxt.lvl t, ← zonk G cxt.env cxt.lvl (quote G cxt.lvl a))
  pure (match r with | .error _ => true | .ok _ => false)

/-- Whether a command defines something; the others are diagnostics. -/
def isDecl : Syntax → Bool
  | `(kcmd| def $_ : $_ := $_) | `(kcmd| data $_ := $_|*) => true
  | _ => false

def isDef : Syntax → Bool
  | `(kcmd| def $_ : $_ := $_) => true
  | _ => false

/-- Run a definition or diagnostic; `import` is the loader's. Returns the
new state and the diagnostic's report, if any. With `bodyAsSorry`, a
definition is checked at its type only. -/
def runCmd (st : KState) (cmd : Syntax) (bodyAsSorry := false) : IO (KState × Option String) := do
  match cmd with
  | `(kcmd| def $x:ident : $a := $t) =>
    let body ← if bodyAsSorry then pure Raw.sorry else liftE (toRaw t)
    pure (← elabDef st x a body, none)
  | `(kcmd| data $x:ident := $cons|*) => pure (← elabData st x cons.getElems, none)
  | `(kcmd| #nf $e) => pure (st, some (← normalize st e))
  | `(kcmd| #time $e) => pure (st, some (← time st e))
  | `(kcmd| #trace $e) => pure (st, some (← trace st e))
  | `(kcmd| #term $e) => pure (st, some (← term st e))
  | `(kcmd| #type $e) => pure (st, some (← type st e))
  | `(kcmd| #head $k:num $e) => pure (st, some (← head st k.getNat e))
  | `(kcmd| #overlaps $k:num $e) => pure (st, some (← overlaps st k.getNat e))
  | `(kcmd| #stable $k:num $e) => pure (st, some (← stable st k.getNat e))
  | `(kcmd| #conv $a = $b) =>
    match ← convSides st a b with
    | none => pure (st, none)
    | some (na, nb) => throw (IO.userError s!"not convertible:\n  {na}\n  {nb}")
  | `(kcmd| #differ $a = $b) =>
    match ← convSides st a b with
    | some _ => pure (st, none)
    | none => throw (IO.userError "expected the sides to differ, but they are convertible")
  | `(kcmd| #fail $e) =>
    if ← fails st e then pure (st, none)
    else throw (IO.userError "expected an elaboration error, but the term elaborated")
  | _ => throw (IO.userError s!"unsupported command: {cmd.getKind}")

/-- The commands of a file, up to the first parse error, which comes with
its position. -/
partial def parseCmds (env : Environment) (input : String) (fileName : String) :
    Array Syntax × Option (String.Pos.Raw × String) :=
  let ictx := Parser.mkInputContext input fileName
  let tokens := Parser.getTokenTable env
  let pmctx : Parser.ParserModuleContext := { env, options := {} }
  let rec go (s : Parser.ParserState) (acc : Array Syntax) :=
    let s := Parser.whitespace.run ictx pmctx tokens s
    if ictx.atEnd s.pos then (acc, none)
    else
      let s := (Parser.categoryParser `kcmd 0).fn.run ictx pmctx tokens s
      match s.allErrors[0]? with
      | some (pos, _, err) => (acc, some (pos, toString err))
      | none => go s (acc.push s.stxStack.back)
  go (Parser.mkParserState input) #[]

def parseExpr (env : Environment) (input : String) : Except String (TSyntax `kexpr) :=
  (⟨·⟩) <$> Parser.runParserCategory env `kexpr input

inductive Severity
  | error
  | warning
  | info
  deriving BEq

/-- A message about a file, at UTF-8 offsets into it. -/
structure Diagnostic where
  pos : String.Pos.Raw
  endPos : String.Pos.Raw
  severity : Severity
  msg : String

def Diagnostic.format (ictx : Parser.InputContext) (d : Diagnostic) : String :=
  let pos := ictx.fileMap.toPosition d.pos
  let severity := match d.severity with
    | .error => "error"
    | .warning => "warning"
    | .info => "info"
  s!"{ictx.fileName}:{pos.line}:{pos.column}: {severity}: {d.msg}"

/-- Shifted by `delta` bytes. -/
def Diagnostic.shift (d : Diagnostic) (delta : Int) : Diagnostic :=
  { d with pos := ⟨(d.pos.byteIdx + delta).toNat⟩, endPos := ⟨(d.endPos.byteIdx + delta).toNat⟩ }

/-- Errors to stderr, the rest to stdout. -/
def printDiagnostic (ictx : Parser.InputContext) (d : Diagnostic) : IO Unit := do
  let out ← if d.severity == .error then IO.getStderr else IO.getStdout
  out.putStrLn (d.format ictx)

/-- What a command added to the state. -/
inductive Delta
  | defn (d : KDef)
  | data (d : DataInfo)
  | nothing

def KState.apply (st : KState) : Delta → KState
  | .defn d => { st with defs := st.defs.push d }
  | .data d => { st with datas := st.datas.push d }
  | .nothing => st

def KState.delta (before after : KState) : Delta :=
  if after.defs.size > before.defs.size then (after.defs.back?.map .defn).getD .nothing
  else if after.datas.size > before.datas.size then (after.datas.back?.map .data).getD .nothing
  else .nothing

/-- A checked command on disk; diagnostics are relative to its start. -/
structure Cached where
  delta : Delta
  diags : Array Diagnostic
  errors : Nat

/-- A command's source text. -/
def cmdText (ictx : Parser.InputContext) (cmd : Syntax) : String :=
  let pos := cmd.getPos?.getD 0
  String.Pos.Raw.extract ictx.fileMap.source pos (cmd.getTailPos?.getD pos)

/-- A checked command of the requested file, reusable while the commands
before it and the imports are unchanged: `chain` hashes the command's text
onto its predecessor's chain and the imports' sources. Diagnostics are
relative to the command's start. -/
structure Snapshot where
  chain : UInt64
  state : KState
  diags : Array Diagnostic
  errors : Nat
  skipped : Bool

/-- Files are loaded once per run, by real path. -/
structure Loader where
  env : Environment
  loaded : Std.HashMap String (Array KModule) := {}
  /-- The content each loaded file had, by real path. -/
  sources : Std.HashMap String String := {}
  loading : List String := []
  errors : Nat := 0
  emit : Parser.InputContext → Diagnostic → IO Unit := printDiagnostic
  /-- Each command of the requested file before it runs, then `none` when the
  file is done. -/
  progress : Parser.InputContext → Option Syntax → IO Unit := fun _ _ => pure ()
  /-- Whether to skip a command of the requested file: a definition is then
  checked at its type only, anything else not at all. -/
  skip : Parser.InputContext → Syntax → Bool := fun _ _ => false
  /-- The requested file's commands as last checked, by chain. -/
  snapshots : Std.HashMap UInt64 Snapshot := {}
  /-- Those reused or made by this check. -/
  snapshotsOut : Std.HashMap UInt64 Snapshot := {}
  /-- Checked commands on disk, of any file, by chain. -/
  cacheDir : Option System.FilePath := none
  /-- The start of every chain. -/
  seed : UInt64 := 7

abbrev LoaderM := StateT Loader IO

/-- Check a file; with `diagnostics`, run its `#…` commands and report
progress too. `source?` stands in for the file's content on disk, and the
result is then not cached. Returns its import closure, dependencies first,
ending with the file itself. Stops between commands once the current task is
cancelled; the result is then partial and not cached. -/
partial def loadFile (path : System.FilePath) (diagnostics : Bool) (source? : Option String := none) :
    LoaderM (Array KModule) := do
  let real : System.FilePath ← try IO.FS.realPath path catch _ => pure path
  let real := real.toString
  if source?.isNone then
    if let some closure := (← get).loaded[real]? then return closure
  if (← get).loading.contains real then
    throw (IO.userError s!"{path}: import cycle")
  modify fun l => { l with loading := real :: l.loading }
  let input ← match source? with
    | some s => pure s
    | none => IO.FS.readFile path
  let ictx := Parser.mkInputContext input path.toString
  let (cmds, parseError) := parseCmds (← get).env input path.toString
  let mut st : KState := {}
  let mut errors := 0
  let mut cancelled := false
  let mut chain : UInt64 := (← get).seed
  for cmd in cmds do
    if ← IO.checkCanceled then
      cancelled := true
      break
    let l ← get
    let pos := cmd.getPos?.getD 0
    let here (severity : Severity) (msg : String) : Diagnostic :=
      { pos, endPos := cmd.getTailPos?.getD pos, severity, msg }
    match cmd with
    | `(kcmd| import $m:ident) =>
      if !st.defs.isEmpty || !st.datas.isEmpty then
        l.emit ictx (here .error "imports must come before definitions")
        errors := errors + 1
      else
        let file := path.parent.getD "." / (m.getId.toString.replace "." "/" ++ ".ktt")
        let closure ← loadFile file false
        st := st.addImports closure
        let bad := closure.filter (·.errors > 0)
        unless bad.isEmpty do
          l.emit ictx (here .error s!"errors in imported {", ".intercalate (bad.toList.map (·.path))}")
        let sources := (← get).sources
        for m in closure do
          chain := mixHash chain (hash (sources[m.path]?.getD ""))
    | _ =>
      if cmd.getKind == ``Syntax.Cmd.moduleDoc then pure ()
      else if diagnostics || isDecl cmd then
        let skip := diagnostics && l.skip ictx cmd
        chain := mixHash chain (hash (cmdText ictx cmd))
        if diagnostics then
          if let some s := l.snapshots[chain]? then
            if !s.skipped || skip then
              for d in s.diags do l.emit ictx (d.shift pos.byteIdx)
              st := s.state
              errors := errors + s.errors
              modify fun l => { l with snapshotsOut := l.snapshotsOut.insert chain s }
              continue
        let cacheable := cmd.getKind != ``Syntax.Cmd.time && cmd.getKind != ``Syntax.Cmd.trace
        if cacheable then
          if let some dir := l.cacheDir then
            if let some c ← Cache.read Cached dir chain then
              for d in c.diags do l.emit ictx (d.shift pos.byteIdx)
              st := st.apply c.delta
              errors := errors + c.errors
              if diagnostics then
                let snapshot : Snapshot :=
                  { chain, state := st, diags := c.diags, errors := c.errors, skipped := false }
                modify fun l => { l with snapshotsOut := l.snapshotsOut.insert chain snapshot }
              continue
        if diagnostics then l.progress ictx (some cmd)
        let before := st
        let mut diags : Array Diagnostic := #[]
        let mut errs := 0
        if skip && !isDef cmd then
          diags := diags.push (here .warning "not checked: past the time budget; checking to here runs it")
        else
          try
            let (st', info?) ← runCmd st cmd (bodyAsSorry := skip)
            st := st'
            if skip then
              diags := diags.push (here .warning "body not checked: past the time budget; checking to here runs it")
            if let some info := info? then diags := diags.push (here .info info)
          catch e =>
            diags := diags.push (here .error (toString e))
            errs := 1
        for d in diags do l.emit ictx d
        errors := errors + errs
        let relative := diags.map (·.shift (-(pos.byteIdx : Int)))
        if diagnostics then
          let snapshot : Snapshot := { chain, state := st, diags := relative, errors := errs, skipped := skip }
          modify fun l => { l with snapshotsOut := l.snapshotsOut.insert chain snapshot }
        if cacheable && !skip then
          if let some dir := l.cacheDir then
            Cache.write dir chain { delta := before.delta st, diags := relative, errors := errs : Cached }
  if !cancelled then
    if let some (pos, msg) := parseError then
      (← get).emit ictx { pos, endPos := pos, severity := .error, msg }
      errors := errors + 1
    if diagnostics then (← get).progress ictx none
  let closure := st.imports.push (st.toModule real errors (cmds.flatMap Symbols.ofCmd))
  modify fun l => { l with
    errors := l.errors + errors
    loading := l.loading.drop 1
    loaded := if cancelled || source?.isSome then l.loaded else l.loaded.insert real closure
    sources := if cancelled || source?.isSome then l.sources else l.sources.insert real input }
  pure closure

/-- The state of a checked file: its imports and its own definitions. -/
def stateOf (closure : Array KModule) : KState :=
  match closure.back? with
  | some own => { imports := closure.pop, defs := own.defs, datas := own.datas }
  | none => {}

end Kleenextt.Frontend
