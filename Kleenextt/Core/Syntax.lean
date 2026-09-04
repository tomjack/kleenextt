import Kleenextt.Core.Interval

namespace Kleenextt.Core

inductive Icit where
  | expl
  | impl
  deriving Repr, DecidableEq, Inhabited

/-- How a surface-syntax argument or binder is given: `f u`, `f {u}`, `f {x := u}`. -/
inductive ArgKind where
  | expl
  | impl
  | named (x : String)
  deriving Repr, Inhabited

/-- Surface syntax: names, no indices. Produced by the `kexpr` frontend.
Systems `[φ ↦ t, …]` are lists of (cofibration, term) pairs and only occur as
arguments of the cubical special forms; binder names of those forms are
recorded next to the terms they scope over. -/
inductive Raw where
  | var (x : String)
  | lam (x : String) (k : ArgKind) (t : Raw)
  | app (t u : Raw) (k : ArgKind)
  | univ
  | pi (x : String) (i : Icit) (a b : Raw)
  | sigma (x : String) (a b : Raw)
  | pair (t u : Raw)
  | fst (t : Raw)
  | snd (t : Raw)
  | letE (x : String) (a t u : Raw)
  | ann (t a : Raw)
  | hole
  | i0
  | i1
  | ineg (r : Raw)
  | imeet (r s : Raw)
  | ijoin (r s : Raw)
  | system (sys : List (Raw × Raw))
  | transp (a r u : Raw)
  | hcomp (general : Bool) (a : Raw) (j : String) (sys : List (Raw × Raw)) (u : Raw)
  | hfill (a : Raw) (j : String) (sys : List (Raw × Raw)) (u r : Raw)
  | comp (i : String) (a : Raw) (j : String) (sys : List (Raw × Raw)) (u : Raw)
  | glueTy (a : Raw) (sys : List (Raw × Raw))
  | glue (sys : List (Raw × Raw)) (a : Raw)
  | unglue (b : Raw)
  /-- An element of a composition in the universe, `glueU [φ ↦ t] a`. -/
  | glueU (sys : List (Raw × Raw)) (a : Raw)
  | split (x P : Raw) (cases : List (String × List String × Raw))
  /-- `hlevel n h`: the cube the enclosing path binders ask for, filled by
  the h-level `n` proof `h` of its type. -/
  | hlevel (n : Nat) (h : Raw)
  | sorry
  deriving Repr, Inhabited

/-- Whether a context entry is a bound variable or a `let`-definition; an
inserted metavariable is applied to the bound ones. -/
inductive BD where
  | bound
  | defined
  deriving Repr, DecidableEq, Inhabited

/-- Core syntax: de Bruijn indices, binder names kept for printing. Interval
expressions are `IExpr`s over indices. In `hcomp`/`hfill`/`comp` systems and
in `comp`'s type, index 0 is the bound interval variable. `papp` records the
endpoints of the path so that application at `0`/`1` can reduce. -/
inductive Tm where
  | var (i : Nat)
  | lam (x : String) (i : Icit) (t : Tm)
  | ilam (x : String) (t : Tm)
  | app (t u : Tm) (i : Icit)
  | univ
  | pi (x : String) (i : Icit) (a b : Tm)
  | sigma (x : String) (a b : Tm)
  | pair (t u : Tm)
  | fst (t : Tm)
  | snd (t : Tm)
  | letE (x : String) (a t u : Tm)
  | mvar (m : Nat)
  | insertedMeta (m : Nat) (bds : List BD)
  | interval
  | i (r : IExpr)
  | papp (p : Tm) (r : IExpr) (x y : Tm)
  | transp (a : Tm) (r : IExpr) (u : Tm)
  | hcomp (general : Bool) (a : Tm) (sys : List (IExpr × Tm)) (u : Tm)
  | hfill (a : Tm) (sys : List (IExpr × Tm)) (u : Tm) (r : IExpr)
  | comp (a : Tm) (sys : List (IExpr × Tm)) (u : Tm)
  | glueTy (a : Tm) (sys : List (IExpr × Tm))
  | glue (tySys sys : List (IExpr × Tm)) (a : Tm)
  | unglue (b : Tm) (sys : List (IExpr × Tm))
  /-- Elements of a composition in the universe `hcomp Type [φ ↦ E] A`:
  `glueU [φ ↦ E] [φ ↦ t] a` with `t : E 1` and `a : A` transporting to `t`
  backwards along `E`; only produced by evaluation. -/
  | glueU (tySys us : List (IExpr × Tm)) (a : Tm)
  | unglueU (b : Tm) (sys : List (IExpr × Tm))
  | prim (name : String)
  /-- A top-level definition. -/
  | top (name : String)
  /-- Dependent case analysis: each case body binds the constructor's fields
  and interval variables, last one at index 0. -/
  | split (P : Tm) (cases : List (String × List String × Tm)) (x : Tm)
  /-- The cube over the interval variables `vars` (indices, outermost
  first) in the type `a`, with the boundary `sys` on their faces, filled
  by the h-level `n` proof `h`. -/
  | extend (n : Nat) (a h : Tm) (sys : List (IExpr × Tm)) (vars : List Nat)
  deriving Repr, Inhabited

namespace Tm

private partial def freshen (ns : List String) (x : String) : String :=
  if x == "_" then x
  else if ns.contains x then freshen ns (x ++ "'")
  else x

private def par (p p' : Nat) (s : String) : String :=
  if p' < p then s!"({s})" else s

private def iname (ns : List String) (i : Nat) : String :=
  ns.getD i s!"!{i}"

/-- Precedences: 0 let/λ, 1 pi, 2 app, 3 atoms. -/
partial def pretty (p : Nat) (ns : List String) : Tm → String
  | var n => iname ns n
  | app t u .expl => par p 2 s!"{pretty 2 ns t} {pretty 3 ns u}"
  | app t u .impl => par p 2 s!"{pretty 2 ns t} \{{pretty 0 ns u}}"
  | lam x ic t =>
    let x := freshen ns x
    let b := match ic with | .expl => x | .impl => s!"\{{x}}"
    par p 0 s!"λ {b} => {pretty 0 (x :: ns) t}"
  | ilam x t =>
    let x := freshen ns x
    par p 0 s!"λ {x} => {pretty 0 (x :: ns) t}"
  | univ => "Type"
  | pi "_" .expl a b => par p 1 s!"{pretty 2 ns a} → {pretty 1 ("_" :: ns) b}"
  | pi x ic a b =>
    let x := freshen ns x
    let dom := match ic with
      | .expl => s!"({x} : {pretty 0 ns a})"
      | .impl => s!"\{{x} : {pretty 0 ns a}}"
    par p 1 s!"{dom} → {pretty 1 (x :: ns) b}"
  | sigma "_" a b => par p 1 s!"{pretty 2 ns a} × {pretty 2 ("_" :: ns) b}"
  | sigma x a b =>
    let x := freshen ns x
    par p 1 s!"({x} : {pretty 0 ns a}) × {pretty 2 (x :: ns) b}"
  | pair t u => s!"({pretty 0 ns t}, {pretty 0 ns u})"
  | fst t => s!"{pretty 3 ns t}.1"
  | snd t => s!"{pretty 3 ns t}.2"
  | letE x a t u =>
    let x := freshen ns x
    par p 0 s!"let {x} : {pretty 0 ns a} := {pretty 0 ns t}; {pretty 0 (x :: ns) u}"
  | mvar m => s!"?{m}"
  | insertedMeta m _ => s!"?{m}"
  | interval => "I"
  | i r => r.pretty (iname ns) (if p ≥ 3 then 2 else 0) |> fun s => if p ≥ 3 && !(r matches .var _ | .zero | .one) then s!"({s})" else s
  | papp t r _ _ => par p 2 s!"{pretty 2 ns t} {(i r).pretty 3 ns}"
  | transp a r u => par p 2 s!"transp {pretty 3 ns a} {(i r).pretty 3 ns} {pretty 3 ns u}"
  | hcomp g a sys u =>
    let hd := if g then "ghcomp" else "hcomp"
    par p 2 s!"{hd} {pretty 3 ns a} {prettySys ns sys} {pretty 3 ns u}"
  | hfill a sys u r => par p 2 s!"hfill {pretty 3 ns a} {prettySys ns sys} {pretty 3 ns u} {(i r).pretty 3 ns}"
  | comp a sys u => par p 2 s!"comp (λ i => {pretty 0 ("i" :: ns) a}) {prettySys ns sys} {pretty 3 ns u}"
  | glueTy a sys => par p 2 s!"Glue {pretty 3 ns a} {prettySysFlat ns sys}"
  | glue _ sys a => par p 2 s!"glue {prettySysFlat ns sys} {pretty 3 ns a}"
  | unglue b _ => par p 2 s!"unglue {pretty 3 ns b}"
  | glueU _ us a => par p 2 s!"glueU {prettySysFlat ns us} {pretty 3 ns a}"
  | unglueU b _ => par p 2 s!"unglueU {pretty 3 ns b}"
  | prim name => name
  | top name => name
  | split P cases x =>
    let cs := cases.map fun (c, names, body) =>
      let names := names.map (freshen ns)
      s!"{" ".intercalate (c :: names)} ↦ {pretty 0 (names.reverse ++ ns) body}"
    par p 2 s!"case {pretty 3 ns x} {pretty 3 ns P} [{", ".intercalate cs}]"
  | extend n _ h sys _ => par p 2 s!"hlevel {n} {pretty 3 ns h} {prettySysFlat ns sys}"
where
  /-- A face as juxtaposed `(i = 0)`/`(i = 1)` atoms. -/
  prettyFace (ns : List String) : IExpr → String
    | .var n => s!"({iname ns n} = 1)"
    | .neg (.var n) => s!"({iname ns n} = 0)"
    | .meet r s => prettyFace ns r ++ prettyFace ns s
    | φ => s!"({(i φ).pretty 0 ns} = 1)"
  /-- A system whose components bind an interval variable. -/
  prettySys (ns : List String) (sys : List (IExpr × Tm)) : String :=
    let j := freshen ns "j"
    let entries := sys.map fun (φ, t) => s!"{prettyFace ns φ} ↦ {pretty 0 (j :: ns) t}"
    s!"(λ {j} => [{", ".intercalate entries}])"
  prettySysFlat (ns : List String) (sys : List (IExpr × Tm)) : String :=
    let entries := sys.map fun (φ, t) => s!"{prettyFace ns φ} ↦ {pretty 0 ns t}"
    s!"[{", ".intercalate entries}]"

end Tm

/-- Resolve names to indices without type checking; unbound names become
primitives. Used for the closed templates the kernel needs (equivalences,
fibers). -/
partial def Raw.toTm (ns : List String) : Raw → Except String Tm
  | .var x =>
    match ns.idxOf? x with
    | some i => pure (.var i)
    | none => pure (.prim x)
  | .lam x .expl t => do pure (.lam x .expl (← t.toTm (x :: ns)))
  | .lam x .impl t => do pure (.lam x .impl (← t.toTm (x :: ns)))
  | .app t u .expl => do pure (.app (← t.toTm ns) (← u.toTm ns) .expl)
  | .app t u .impl => do pure (.app (← t.toTm ns) (← u.toTm ns) .impl)
  | .univ => pure .univ
  | .pi x ic a b => do pure (.pi x ic (← a.toTm ns) (← b.toTm (x :: ns)))
  | .sigma x a b => do pure (.sigma x (← a.toTm ns) (← b.toTm (x :: ns)))
  | .pair t u => do pure (.pair (← t.toTm ns) (← u.toTm ns))
  | .fst t => do pure (.fst (← t.toTm ns))
  | .snd t => do pure (.snd (← t.toTm ns))
  | _ => throw "Raw.toTm: unsupported form in template"

end Kleenextt.Core
