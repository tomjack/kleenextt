namespace Kleenextt

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

/-- Surface syntax: names, no indices. Produced by the `kexpr` frontend. -/
inductive Raw where
  | var (x : String)
  | lam (x : String) (k : ArgKind) (t : Raw)
  | app (t u : Raw) (k : ArgKind)
  | univ
  | pi (x : String) (i : Icit) (a b : Raw)
  | letE (x : String) (a t u : Raw)
  | hole
  deriving Repr, Inhabited

/-- Whether a context entry is a bound variable or a `let`-definition; an
inserted metavariable is applied to the bound ones. -/
inductive BD where
  | bound
  | defined
  deriving Repr, DecidableEq, Inhabited

/-- Core syntax: de Bruijn indices, binder names kept for printing. -/
inductive Tm where
  | var (i : Nat)
  | lam (x : String) (i : Icit) (t : Tm)
  | app (t u : Tm) (i : Icit)
  | univ
  | pi (x : String) (i : Icit) (a b : Tm)
  | letE (x : String) (a t u : Tm)
  | mvar (m : Nat)
  | insertedMeta (m : Nat) (bds : List BD)
  deriving Repr, Inhabited

namespace Tm

private partial def freshen (ns : List String) (x : String) : String :=
  if x == "_" then x
  else if ns.contains x then freshen ns (x ++ "'")
  else x

private def par (p p' : Nat) (s : String) : String :=
  if p' < p then s!"({s})" else s

/-- Precedences: 0 let/λ, 1 pi, 2 app, 3 atoms. -/
partial def pretty (p : Nat) (ns : List String) : Tm → String
  | var i => ns.getD i s!"!{i}"
  | app t u .expl => par p 2 s!"{pretty 2 ns t} {pretty 3 ns u}"
  | app t u .impl => par p 2 s!"{pretty 2 ns t} \{{pretty 0 ns u}}"
  | lam x i t =>
    let x := freshen ns x
    let b := match i with | .expl => x | .impl => s!"\{{x}}"
    par p 0 s!"λ {b} => {pretty 0 (x :: ns) t}"
  | univ => "Type"
  | pi "_" .expl a b => par p 1 s!"{pretty 2 ns a} → {pretty 1 ("_" :: ns) b}"
  | pi x i a b =>
    let x := freshen ns x
    let dom := match i with
      | .expl => s!"({x} : {pretty 0 ns a})"
      | .impl => s!"\{{x} : {pretty 0 ns a}}"
    par p 1 s!"{dom} → {pretty 1 (x :: ns) b}"
  | letE x a t u =>
    let x := freshen ns x
    par p 0 s!"let {x} : {pretty 0 ns a} := {pretty 0 ns t}; {pretty 0 (x :: ns) u}"
  | mvar m => s!"?{m}"
  | insertedMeta m _ => s!"?{m}"

end Tm

end Kleenextt
