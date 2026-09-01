import Kleenextt.Syntax

namespace Kleenextt

mutual
  /-- Semantic values. Neutrals are `var`/`app` spines headed by a de Bruijn level. -/
  inductive Val where
    | var (l : Nat)
    | app (t u : Val)
    | lam (x : String) (c : Closure)
    | pi (x : String) (a : Val) (c : Closure)
    | univ

  inductive Closure where
    | mk (env : List Val) (t : Tm)
end

instance : Inhabited Val := ⟨.univ⟩

abbrev Env := List Val

mutual
  partial def Closure.apply : Closure → Val → Val
    | .mk env t, u => eval (u :: env) t

  partial def eval (env : Env) : Tm → Val
    | .var i => env.getD i default
    | .app t u =>
      match eval env t, eval env u with
      | .lam _ c, u => c.apply u
      | t, u => .app t u
    | .lam x t => .lam x (.mk env t)
    | .pi x a b => .pi x (eval env a) (.mk env b)
    | .letE _ _ t u => eval (eval env t :: env) u
    | .univ => .univ
end

/-- Read a value back into core syntax; `l` fresh-variable supply (levels → indices). -/
partial def quote (l : Nat) : Val → Tm
  | .var x => .var (l - x - 1)
  | .app t u => .app (quote l t) (quote l u)
  | .lam x c => .lam x (quote (l + 1) (c.apply (.var l)))
  | .pi x a c => .pi x (quote l a) (quote (l + 1) (c.apply (.var l)))
  | .univ => .univ

def nf (env : Env) (t : Tm) : Tm :=
  quote env.length (eval env t)

/-- Beta-eta conversion. Precondition: both values have the same type. -/
partial def conv (l : Nat) : Val → Val → Bool
  | .univ, .univ => true
  | .pi _ a c, .pi _ a' c' =>
    conv l a a' && conv (l + 1) (c.apply (.var l)) (c'.apply (.var l))
  | .lam _ c, .lam _ c' =>
    conv (l + 1) (c.apply (.var l)) (c'.apply (.var l))
  | .lam _ c, u =>
    conv (l + 1) (c.apply (.var l)) (.app u (.var l))
  | u, .lam _ c =>
    conv (l + 1) (.app u (.var l)) (c.apply (.var l))
  | .var x, .var x' => x == x'
  | .app t u, .app t' u' => conv l t t' && conv l u u'
  | _, _ => false

end Kleenextt
