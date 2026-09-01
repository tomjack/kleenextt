namespace Kleenextt

/-- Surface syntax: names, no indices. Produced by the `kexpr` frontend. -/
inductive Raw where
  | var (x : String)
  | lam (x : String) (t : Raw)
  | app (t u : Raw)
  | univ
  | pi (x : String) (a b : Raw)
  | letE (x : String) (a t u : Raw)
  deriving Repr, Inhabited

/-- Core syntax: de Bruijn indices, binder names kept for printing. -/
inductive Tm where
  | var (i : Nat)
  | lam (x : String) (t : Tm)
  | app (t u : Tm)
  | univ
  | pi (x : String) (a b : Tm)
  | letE (x : String) (a t u : Tm)
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
  | app t u => par p 2 s!"{pretty 2 ns t} {pretty 3 ns u}"
  | lam x t =>
    let x := freshen ns x
    par p 0 s!"λ {x} => {pretty 0 (x :: ns) t}"
  | univ => "Type"
  | pi "_" a b => par p 1 s!"{pretty 2 ns a} → {pretty 1 ("_" :: ns) b}"
  | pi x a b =>
    let x := freshen ns x
    par p 1 s!"({x} : {pretty 0 ns a}) → {pretty 1 (x :: ns) b}"
  | letE x a t u =>
    let x := freshen ns x
    par p 0 s!"let {x} : {pretty 0 ns a} := {pretty 0 ns t}; {pretty 0 (x :: ns) u}"

end Tm

end Kleenextt
