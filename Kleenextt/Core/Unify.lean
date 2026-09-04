import Kleenextt.Core.Eval

/-! Pattern unification, after elaboration-zoo 04. A metavariable applied to
distinct bound variables (ordinary or interval) is solved by inverting the
spine into a partial renaming and reading the other side back under it. -/

namespace Kleenextt.Core

abbrev UnifyM := StateT Globals (Except String)

/-- Invert a spine of distinct bound variables. Also returns, for each spine
entry (last argument first), its implicitness and whether it is an interval
variable. -/
def invert (G : Globals) (gamma : Nat) (sp : Spine) :
    Except String (PRen × List (Icit × Bool)) := do
  let rec go : Spine → Except String (Nat × List (Nat × Nat) × List (Icit × Bool))
    | [] => pure (0, [], [])
    | (t, i) :: sp => do
      let (dom, ren, sorts) ← go sp
      let (x, isI) ← match force G gamma t with
        | .var x => pure (x, false)
        | .i (.var x) => pure (x, true)
        | _ => throw "unify: spine argument is not a variable"
      if ren.any (·.1 == x) then throw "unify: non-linear spine"
      pure (dom + 1, (x, dom) :: ren, (i, isI) :: sorts)
  let (dom, ren, sorts) ← go sp
  pure ({ dom, cod := gamma, ren := fun x => (ren.find? (·.1 == x)).map (·.2) }, sorts)

/-- Wrap a term in lambdas matching the spine, outermost first. -/
private def lams (sorts : List (Icit × Bool)) (t : Tm) : Tm :=
  let rec go (n : Nat) : List (Icit × Bool) → Tm
    | [] => t
    | (i, isI) :: rest =>
      let x := s!"x{n + 1}"
      if isI then .ilam x (go (n + 1) rest) else .lam x i (go (n + 1) rest)
  go 0 sorts

def solve (gamma : Nat) (m : Nat) (sp : Spine) (rhs : Val) : UnifyM Unit := do
  let G ← get
  let (pren, sorts) ← invert G gamma sp
  let rhs ← readback G pren (some m) false rhs
  let solution := eval G 0 [] [] (lams sorts.reverse rhs)
  set { G with metas := G.metas.set! m (.solved solution) }

private def ieqOr (r s : IExpr) : UnifyM Unit :=
  if ieq r s then pure () else throw "unify: interval expressions differ"

private unsafe def ptrEqImpl {α : Type} (a b : α) : Bool := ptrEq a b

/-- Physical equality, as a shortcut: the same object is convertible to
itself, and the same closure code over convertible environments gives
convertible values. -/
@[implemented_by ptrEqImpl] private def ptrEqSafe {α : Type} (_ _ : α) : Bool := false

mutual
  partial def unifySp (l : Nat) : Spine → Spine → UnifyM Unit
    | [], [] => pure ()
    | (t, _) :: sp, (t', _) :: sp' => do unifySp l sp sp'; unify l t t'
    | _, _ => throw "unify: spine length mismatch"

  /-- Unify two systems with the same faces; `lines` if the components bind
  an interval variable. -/
  partial def unifySys (l : Nat) (lines : Bool) (sys sys' : System Val) : UnifyM Unit := do
    unless sys.length == sys'.length do throw "unify: system shapes differ"
    for (α, s) in sys do
      match sys'.find? (·.1 == α) with
      | none => throw "unify: system shapes differ"
      | some (_, s') =>
        let G ← get
        if lines then
          unify (l + 1) (face G (l + 1) [] α (lineApp G (l + 1) [] s (.var l)))
            (face G (l + 1) [] α (lineApp G (l + 1) [] s' (.var l)))
        else unify l (face G l [] α s) (face G l [] α s')

  /-- The same closure code over convertible environments, else the bodies
  at a fresh variable. -/
  partial def unifyClo (l : Nat) (c c' : Closure) (fresh : Val) : UnifyM Unit := do
    let G ← get
    let bodies := unify (l + 1) (c.apply G (l + 1) [] fresh) (c'.apply G (l + 1) [] fresh)
    match c, c' with
    | .mk env t, .mk env' t' =>
      if ptrEqSafe t t' && env.length == env'.length then
        try for (u, u') in env.zip env' do unify l u u'
        catch _ => bodies
      else bodies

  partial def unifyCases (l : Nat) (env : Env) (cs : List (String × List String × Tm))
      (env' : Env) (cs' : List (String × List String × Tm)) : UnifyM Unit := do
    for (c, _, b) in cs do
      match cs'.find? (·.1 == c) with
      | none => throw "unify: case shapes differ"
      | some (_, _, b') =>
        let G ← get
        let (v, p) := instCase G l env c b
        let (v', _) := instCase G l env' c b'
        unify p.cod v v'

  partial def unify (l : Nat) (t u : Val) : UnifyM Unit := do
    if ptrEqSafe t u then return
    let G ← get
    let t := forceG G l t
    let u := forceG G l u
    if ptrEqSafe t u then return
    match t, u with
    | .flex m sp, .flex m' sp' =>
      if m == m' then unifySp l sp sp' else solve l m sp (.flex m' sp')
    | .flex m sp, t' => solve l m sp t'
    | t, .flex m' sp' => solve l m' sp' t
    | .glued n sp v, .glued n' sp' v' =>
      if n == n' && sp.length == sp'.length then
        try unifySp l sp sp' catch _ => unify l v.get v'.get
      else unify l v.get v'.get
    | .glued _ _ v, t' => unify l v.get t'
    | t, .glued _ _ v' => unify l t v'.get
    | .ilam _ c, .ilam _ c' => unifyClo l c c' (.i (.var l))
    | .ilam _ c, t' => unify (l + 1) (c.apply G (l + 1) [] (.i (.var l))) (lineApp G (l + 1) [] t' (.var l))
    | t, .ilam _ c' => unify (l + 1) (lineApp G (l + 1) [] t (.var l)) (c'.apply G (l + 1) [] (.i (.var l)))
    | t, t'@(.line ..) | t@(.line ..), t' =>
      unify (l + 1) (lineApp G (l + 1) [] t (.var l)) (lineApp G (l + 1) [] t' (.var l))
    | .lam _ _ c, .lam _ _ c' => unifyClo l c c' (.var l)
    | .lam _ i c, t' => unify (l + 1) (c.apply G (l + 1) [] (.var l)) (vApp G (l + 1) [] t' (.var l) i)
    | t, .lam _ i c' => unify (l + 1) (vApp G (l + 1) [] t (.var l) i) (c'.apply G (l + 1) [] (.var l))
    | .univ, .univ => pure ()
    | .interval, .interval => pure ()
    | .i r, .i s => ieqOr r s
    | .pi _ i a c, .pi _ i' a' c' =>
      if i != i' then throw "unify: implicitness mismatch"
      unify l a a'
      let G ← get
      let fresh := match a with
        | .interval => Val.i (.var l)
        | _ => .var l
      unifyClo l c c' fresh
    | .sigma _ a c, .sigma _ a' c' =>
      unify l a a'
      unifyClo l c c' (.var l)
    | .pair u w, .pair u' w' => do unify l u u'; unify l w w'
    | .pair u w, t' => do unify l u (vFst G l [] t'); unify l w (vSnd G l [] t')
    | t, .pair u' w' => do unify l (vFst G l [] t) u'; unify l (vSnd G l [] t) w'
    | .fst t, .fst t' => unify l t t'
    | .snd t, .snd t' => unify l t t'
    | .var x, .var x' => if x == x' then pure () else throw "unify: rigid mismatch"
    | .app t u _, .app t' u' _ => do unify l t t'; unify l u u'
    | .papp p r _ _, .papp p' r' _ _ => do unify l p p'; ieqOr r r'
    | .papp p r _ _, .app p' (.i r') _ => do unify l p p'; ieqOr r r'
    | .app p (.i r) _, .papp p' r' _ _ => do unify l p p'; ieqOr r r'
    | .pathP a x y, .pathP a' x' y' => do unify l a a'; unify l x x'; unify l y y'
    | .transp a r u, .transp a' r' u' => do unify l a a'; ieqOr r r'; unify l u u'
    | .hcomp a sys u, .hcomp a' sys' u' => do unify l a a'; unifySys l true sys sys'; unify l u u'
    | .glueTy a sys, .glueTy a' sys' => do unify l a a'; unifySys l false sys sys'
    | .glue _ sys a, .glue _ sys' a' => do unifySys l false sys sys'; unify l a a'
    | .glue tySys sys a, t' => glueEta l tySys sys a t'
    | t, .glue tySys sys' a' => glueEta l tySys sys' a' t
    | .unglue b _, .unglue b' _ => unify l b b'
    | .hcompU a sys, .hcompU a' sys' => do unify l a a'; unifySys l true sys sys'
    | .glueU _ us a, .glueU _ us' a' => do unifySys l false us us'; unify l a a'
    | .glueU tySys us a, t' => glueUEta l tySys us a t'
    | t, .glueU tySys us' a' => glueUEta l tySys us' a' t
    | .unglueU b _, .unglueU b' _ => unify l b b'
    | .prim n args, .prim n' args' =>
      if n == n' && args.length == args'.length then
        for (a, a') in args.zip args' do unify l a a'
      else throw "unify: rigid mismatch"
    | .split P env cs x, .split P' env' cs' x' =>
      unify l P P'
      unify l x x'
      if ptrEqSafe cs cs' && env.length == env'.length then
        try for (u, u') in env.zip env' do unify l u u'
        catch _ => unifyCases l env cs env' cs'
      else unifyCases l env cs env' cs'
    | _, _ => throw "unify: rigid mismatch"

  /-- `b = glue [φ ↦ b] (unglue b)`. -/
  partial def glueEta (l : Nat) (tySys sys : System Val) (a t : Val) : UnifyM Unit := do
    let G ← get
    unify l a (unglue' G l [] t tySys)
    for (α, s) in sys do
      let G ← get
      unify l s (face G l [] α t)

  partial def glueUEta (l : Nat) (tySys us : System Val) (a t : Val) : UnifyM Unit := do
    let G ← get
    unify l a (unglueU' G l [] t tySys)
    for (α, s) in us do
      let G ← get
      unify l s (face G l [] α t)
end

end Kleenextt.Core
