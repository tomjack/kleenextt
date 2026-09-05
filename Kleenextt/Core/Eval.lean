import Kleenextt.Core.Syntax
import Kleenextt.Core.Defun
import Kleenextt.Core.Stats

/-! Cubical NbE after cubicaltt, on de Bruijn levels; `hcomp` in the
universe is cubicaltt's `VCompU`, its equivalence backward transport with
`lemEq` for the fibers.

A value in a context of size `L` mentions only levels below `L`, interval
variables included. A `line`'s body is memoised at a fresh variable and its
support comes from the captures of its derived closure; substitution
(`act`) is skipped outside the support and otherwise deferred (`sub`),
pushed one layer by `whnf`. Components a total face may discard are `lazy`;
definitions stay `glued` heads compared by spine first.

Every operation takes `L`, the fresh-level supply, and the cofibration `κ`
in scope: heads are inspected under `κ` (`frc`), a face `γ` works under
`κ ∧ γ`, and faces are kept relative to `κ`. -/

namespace Kleenextt.Core

/-- Components indexed by maximal faces, relative to the cofibration the
system was built under. -/
abbrev System (α : Type) := List (Face × α)

/-- Under `κ`: drop inconsistent faces, strip `κ`'s equations, keep the
maximal faces; duplicates agree by typing. -/
def mkSystem (κ : Face) (entries : System α) : System α :=
  let entries := if κ.isEmpty then entries else
    entries.filterMap fun (γ, u) => (κ.meet γ).map fun _ => (γ.minus κ, u)
  (maximalFaces (entries.map (·.1))).filterMap fun α => entries.find? (·.1 == α)

/-- The cofibration a system covers. -/
def System.cof (sys : System α) : IExpr :=
  sys.foldr (fun (α, _) acc => .join α.toIExpr acc) .zero

def System.total? (sys : System α) : Option α :=
  (sys.find? (·.1.isEmpty)).map (·.2)

/-- A system built under a weaker cofibration, seen under `κ`. -/
def System.restrict (κ : Face) (sys : System α) : System α :=
  if κ.isEmpty then sys else mkSystem κ sys

/-- Each face with its cofibration `κ ∧ α`; inconsistent faces dropped. -/
def System.under (κ : Face) (sys : System α) : List (Face × Face × α) :=
  if κ.isEmpty then sys.map fun (α, u) => (α, α, u)
  else sys.filterMap fun (α, u) => (κ.meet α).map fun κα => (α, κα, u)

/-- `κ ∧ δ` for a face `δ` produced under `κ`, which mentions none of `κ`'s
generators. -/
def Face.conj (κ δ : Face) : Face :=
  (κ.meet δ).getD κ

/-- In a support bitmask, level `l` is bit `l + 1`; bit 0 is `openBit`. -/
def levelBit (l : Nat) : Nat := 1 <<< (l + 1)

def hasLevel (vs l : Nat) : Bool := vs.testBit (l + 1)

/-- A substitution of interval expressions for levels. -/
abbrev Subst := List (Nat × IExpr)

namespace Subst

def get (σ : Subst) (l : Nat) : Option IExpr :=
  (σ.find? (·.1 == l)).map (·.2)

def apply (σ : Subst) (r : IExpr) : IExpr :=
  (r.mapVars fun l => (σ.get l).getD (.var l)).norm

/-- Restrict the images by a face. -/
def under (σ : Subst) (α : Face) : Subst :=
  σ.map fun (l, r) => (l, α.apply r)

/-- `σ ∘ τ`: apply `τ`, then `σ`. -/
def comp (σ τ : Subst) : Subst :=
  τ.map (fun (l, r) => (l, σ.apply r)) ++ σ.filter fun (l, _) => (τ.get l).isNone

/-- The levels substituted, as a bitmask. -/
def domain (σ : Subst) : Nat :=
  σ.foldl (fun acc (l, _) => acc ||| levelBit l) 0

end Subst

def Face.toSubst (α : Face) : Subst :=
  α.map fun (l, d) => (l, .ofBool d)

/-- The equations on the levels of a support. -/
def Face.toSubstOn (α : Face) (vs : Nat) : Subst :=
  α.filterMap fun (l, d) => if hasLevel vs l then some (l, .ofBool d) else none

/-! ## Support: the levels a value may mention, as a bitmask -/

class Vars (α : Type) where
  vars : α → Nat

def levelSet (ls : List Nat) : Nat :=
  ls.foldl (· ||| levelBit ·) 0

def clearLevel (vs l : Nat) : Nat :=
  if hasLevel vs l then vs - levelBit l else vs

/-- Set in the support of a value mentioning a fibrant variable or a
metavariable. Without it a value is closed in cctt's sense (free interval
variables allowed), so canonicity applies to it. -/
def openBit : Nat := 1

/-- The levels a value with support `vs` may mention after `σ`. -/
def Subst.varsUnder (σ : Subst) (vs : Nat) : Nat :=
  σ.foldl (init := σ.foldl (fun acc (l, _) => clearLevel acc l) vs) fun acc (l, r) =>
    if hasLevel vs l then acc ||| levelSet r.vars else acc

/-- For terms, names, indices, and context sizes. -/
abbrev Vars.none : Vars α := ⟨fun _ => 0⟩

instance : Vars IExpr := ⟨fun r => levelSet r.vars⟩
/-- A captured face is a cofibration in scope, not support; system faces
are counted by the pair instance below. -/
instance : Vars Face := .none
instance [Vars α] [Vars β] : Vars (α × β) := ⟨fun (a, b) => Vars.vars a ||| Vars.vars b⟩
instance [Vars α] : Vars (List α) := ⟨fun xs => xs.foldl (· ||| Vars.vars ·) 0⟩
instance : Vars Tm := .none
instance : Vars String := .none
instance : Vars Nat := .none
instance : Vars Icit := .none

/-- A captured cofibration restricted to the levels of a support: its other
equations concern variables nothing in the closure mentions. Faces paired
with components are a system's, kept. -/
class Prune (α : Type) where
  prune : Nat → α → α

abbrev Prune.id : Prune α := ⟨fun _ a => a⟩

instance : Prune Face := ⟨fun vs κ => κ.filter fun (l, _) => hasLevel vs l⟩
instance [Prune α] [Prune β] : Prune (α × β) := ⟨fun vs (a, b) => (Prune.prune vs a, Prune.prune vs b)⟩
instance [Prune β] : Prune (Face × β) := ⟨fun vs (α, b) => (α, Prune.prune vs b)⟩
instance [Prune α] : Prune (List α) := ⟨fun vs xs => xs.map (Prune.prune vs)⟩
instance : Prune IExpr := .id
instance : Prune Tm := .id
instance : Prune String := .id
instance : Prune Nat := .id
instance : Prune Bool := .id
instance : Prune Icit := .id

/-! ## Templates: closed definitions the rules unfold -/

private def template (r : Raw) : Tm :=
  match r.toTm [] with
  | .ok t => t
  | .error e => panic! e

private def v (x : String) : Raw := .var x
private def ap (f : Raw) (args : List Raw) : Raw := args.foldl (fun t u => .app t u .expl) f
private def lams (xs : List String) (t : Raw) : Raw := xs.foldr (fun x acc => .lam x .expl acc) t

/-- `isContr A = (x : A) × ((y : A) → Path A x y)` -/
private def isContrTm : Tm := template <| lams ["A"] <|
  .sigma "x" (v "A") (.pi "y" .expl (v "A") (ap (v "Path") [v "A", v "x", v "y"]))

/-- `fiber {A B} f y = (x : A) × Path B y (f x)` -/
private def fiberTm : Tm := template <| lams ["A", "B", "f", "y"] <|
  .sigma "x" (v "A") (ap (v "Path") [v "B", v "y", ap (v "f") [v "x"]])

/-- `isEquiv {A B} f = (y : B) → isContr (fiber f y)` -/
private def isEquivTm : Tm := template <| lams ["A", "B", "f"] <|
  .pi "y" .expl (v "B") (ap (v "isContr") [ap (v "fiber") [v "A", v "B", v "f", v "y"]])

/-- `Equiv A B = (f : A → B) × isEquiv f` -/
private def equivTm : Tm := template <| lams ["A", "B"] <|
  .sigma "f" (.pi "_" .expl (v "A") (v "B")) (ap (v "isEquiv") [v "A", v "B", v "f"])

/-- `isOfHLevel n`: `isContr`, then `(x y : A) → isOfHLevel (n-1) (Path A x y)`
with `isProp` at `1`, as in Cubical Agda. -/
def isOfHLevelTm (n : Nat) : Tm := template <| lams ["A"] <| go n (v "A")
where
  go : Nat → Raw → Raw
    | 0, a => ap (v "isContr") [a]
    | n + 1, a =>
      let x := s!"x{n}"
      let y := s!"y{n}"
      let path := ap (v "Path") [a, v x, v y]
      .pi x .expl a (.pi y .expl a (if n == 0 then path else go n path))

/-- `isOfHLevelSuc n A h : isOfHLevel (n+1) A` from `h : isOfHLevel n A`. -/
def isOfHLevelSucTm (n : Nat) : Tm := template <| lams ["A", "h"] <| go n (v "A") (v "h")
where
  go : Nat → Raw → Raw → Raw
    | 0, a, h => ap (v "contrToProp") [a, h]
    | 1, a, h => ap (v "propToSet") [a, h]
    | n + 2, a, h =>
      let x := s!"x{n}"
      let y := s!"y{n}"
      lams [x, y] (go (n + 1) (ap (v "Path") [a, v x, v y]) (ap h [v x, v y]))

/-- `isContrToProp A h x y = λ i. hcomp A [(i = 0) ↦ h.2 x, (i = 1) ↦ h.2 y] h.1`;
core syntax, for the `papp` endpoints. -/
private def isContrToPropTm : Tm :=
  .lam "A" .expl <| .lam "h" .expl <| .lam "x" .expl <| .lam "y" .expl <| .ilam "i" <|
    .hcomp false (.var 4)
      [(.neg (.var 0), .papp (.app (.snd (.var 4)) (.var 3) .expl) (.var 0) (.fst (.var 4)) (.var 3)),
       (.var 0, .papp (.app (.snd (.var 4)) (.var 2) .expl) (.var 0) (.fst (.var 4)) (.var 2))]
      (.fst (.var 3))

/-- `isPropToSet A h a b p q = λ j i. hcomp A [(i = 0) ↦ h a a, (i = 1) ↦ h a b,
(j = 0) ↦ h a (p i), (j = 1) ↦ h a (q i)] a`, cctt's `isProp-isSet`. -/
private def isPropToSetTm : Tm :=
  let h (x y : Tm) : Tm := .app (.app (.var 7) x .expl) y .expl
  let a : Tm := .var 6
  let b : Tm := .var 5
  let pI : Tm := .papp (.var 4) (.var 1) a b
  let qI : Tm := .papp (.var 3) (.var 1) a b
  .lam "A" .expl <| .lam "h" .expl <| .lam "a" .expl <| .lam "b" .expl <| .lam "p" .expl <| .lam "q" .expl <|
    .ilam "j" <| .ilam "i" <|
    .hcomp false (.var 7)
      [(.neg (.var 0), .papp (h a a) (.var 0) a a),
       (.var 0, .papp (h a b) (.var 0) a b),
       (.neg (.var 1), .papp (h a pI) (.var 0) a pI),
       (.var 1, .papp (h a qI) (.var 0) a qI)]
      (.var 5)

/-- Primitives defined by unfolding: arity and closed definition. -/
private def primDef : String → Option (Nat × Tm)
  | "contrToProp" => some (2, isContrToPropTm)
  | "propToSet" => some (2, isPropToSetTm)
  | "isContr" => some (1, isContrTm)
  | "fiber" => some (4, fiberTm)
  | "isEquiv" => some (3, isEquivTm)
  | "Equiv" => some (2, equivTm)
  | _ => none

/-- A telescope of fields, then interval binders, then a boundary over the
interval binders in the context of both. -/
structure ConInfo where
  name : String
  fields : List (String × Tm)
  ivars : List String
  boundary : List (IExpr × Tm)

def ConInfo.arity (c : ConInfo) : Nat :=
  c.fields.length + c.ivars.length

/-- Parameterless; a HIT if a constructor binds interval variables. -/
structure DataInfo where
  name : String
  cons : List ConInfo

def DataInfo.hit (d : DataInfo) : Bool :=
  d.cons.any (!·.ivars.isEmpty)

/-! ## The domain and the computation rules -/

defun Line (L : Nat) (i : IExpr) : Val
  deriving vars : Nat folding (· ||| ·) 0 via Vars.vars := Val.vars
  deriving prune (vs : Nat) via Prune.prune := fun _ v => v
in

mutual
  inductive Val where
    | var (l : Nat)
    | flex (m : Nat) (sp : List (Val × Icit))
    | lam (x : String) (i : Icit) (c : Closure)
    | ilam (x : String) (c : Closure)
    /-- Body memoised at fresh level `l`; support from the derived closure. -/
    | line (l : Nat) (body : Thunk Val) (vars : Nat)
    /-- Deferred substitution with its support; `head` pushes it one layer. -/
    | sub (L : Nat) (σ : Subst) (v : Val) (vars : Nat) (head : Thunk Val)
    | lazy (vars : Nat) (body : Thunk Val)
    /-- The support of a compound value, without walking it. -/
    | cached (vars : Nat) (v : Val)
    /-- A definition applied to a spine (latest first), unfolded
    transparently but compared by spine first. -/
    | glued (name : String) (sp : List (Val × Icit)) (v : Thunk Val)
    | app (t u : Val) (i : Icit)
    | papp (p : Val) (r : IExpr) (x y : Val)
    | univ
    | interval
    | i (r : IExpr)
    | pi (x : String) (i : Icit) (a : Val) (c : Closure)
    | sigma (x : String) (a : Val) (c : Closure)
    | pair (u v : Val)
    | fst (t : Val)
    | snd (t : Val)
    | pathP (a x y : Val)
    | transp (a : Val) (r : IExpr) (u : Val)
    | hcomp (a : Val) (sys : List (Face × Val)) (u : Val)
    | glueTy (a : Val) (sys : List (Face × Val))
    | glue (tySys sys : List (Face × Val)) (a : Val)
    | unglue (b : Val) (sys : List (Face × Val))
    /-- `hcomp Type [φ ↦ E] A` as a type former; its elements are `glueU`. -/
    | hcompU (a : Val) (sys : List (Face × Val))
    | glueU (tySys us : List (Face × Val)) (a : Val)
    | unglueU (b : Val) (sys : List (Face × Val))
    | prim (name : String) (args : List Val)
    | split (P : Val) (env : List Val) (cases : List (String × List String × Tm)) (x : Val)

  inductive Closure where
    | mk (env : List Val) (t : Tm)
end

instance : Inhabited Val := ⟨.univ⟩

abbrev Env := List Val
abbrev Spine := List (Val × Icit)

inductive MetaEntry where
  | unsolved
  | solved (v : Val)

structure Globals where
  metas : Array MetaEntry := #[]
  datas : List DataInfo := []
  /-- Name, value, type. Closed, kept out of environments so substitution
  never traverses them. -/
  defs : List (String × Thunk Val × Val) := []

def Globals.lookupMeta (G : Globals) (m : Nat) : MetaEntry :=
  G.metas.getD m .unsolved

def Globals.def? (G : Globals) (n : String) : Option (Thunk Val × Val) :=
  (G.defs.find? (·.1 == n)).map (·.2)

def Globals.data? (G : Globals) (n : String) : Option DataInfo :=
  G.datas.find? (·.name == n)

def Globals.con? (G : Globals) (c : String) : Option (DataInfo × ConInfo) :=
  G.datas.findSome? fun d => (d.cons.find? (·.name == c)).map (d, ·)

instance [Vars Val] : Vars Closure := ⟨fun c => match c with | .mk env _ => Vars.vars env⟩
instance : Prune Closure := .id

/-- In a system, the face's generators count. -/
instance [Vars Val] : Vars (Face × Val) := ⟨fun (α, u) => levelSet (α.map (·.1)) ||| Vars.vars u⟩

/-- The head, short of unfolding a definition. -/
partial def Val.whnfG : Val → Val
  | .sub _ _ _ _ head => head.get.whnfG
  | .lazy _ body => body.get.whnfG
  | .cached _ v => v.whnfG
  | v => v

/-- The head, unfolding definitions. -/
partial def Val.whnf (v : Val) : Val :=
  match v.whnfG with
  | .glued _ _ u => u.get.whnf
  | v => v

/-- The head of a value with the faces of its systems, for diagnostics. -/
partial def Val.headStr (v : Val) (depth : Nat := 3) : String :=
  let faces (sys : System Val) : String :=
    "[" ++ ", ".intercalate (sys.map fun (α, _) =>
      if α.isEmpty then "⊤" else " ∧ ".intercalate (α.map fun (l, d) => s!"v{l}={if d then 1 else 0}")) ++ "]"
  let sub (w : Val) : String := if depth == 0 then "…" else w.headStr (depth - 1)
  match v.whnf with
  | .hcomp _ sys u => s!"hcomp {faces sys} ({sub u})"
  | .hcompU _ sys => s!"hcompU {faces sys}"
  | .glueU tySys us a => s!"glueU {faces tySys} {faces us} ({sub a})"
  | .unglueU b sys => s!"unglueU {faces sys} ({sub b})"
  | .glueTy _ sys => s!"Glue {faces sys}"
  | .glue tySys sys a => s!"glue {faces tySys} {faces sys} ({sub a})"
  | .unglue b sys => s!"unglue {faces sys} ({sub b})"
  | .transp _ r u => s!"transp {repr r} ({sub u})"
  | .split _ _ cases x => s!"case {cases.map (·.1)} ({sub x})"
  | .prim n args => s!"{n}/{args.length}"
  | .pair .. => "pair"
  | .fst t => s!"fst ({sub t})"
  | .snd t => s!"snd ({sub t})"
  | .app t _ _ => s!"app ({sub t})"
  | .papp p .. => s!"papp ({sub p})"
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

/-- A face becomes the faces on which `σ` makes it hold, with the component
under each. -/
def System.act (actVal : Subst → Val → Val) (κ : Face) (σ : Subst) (sys : System Val) : System Val :=
  mkSystem κ <| sys.flatMap fun (α, u) =>
    let β : Face := α.filter fun (l, _) => (σ.get l).isNone
    let ψ := β.apply <| α.foldr (init := .one) fun (l, d) acc =>
      match σ.get l with
      | some r => .meet (if d then r else .neg r) acc
      | none => acc
    (invFormula (κ.apply ψ) true).filterMap fun δ =>
      (δ.meet β).map fun key => (key, actVal (σ.under key) u)

/-- Evaluate an interval expression over indices in an environment. -/
def evalI (env : Env) (r : IExpr) : IExpr :=
  (r.mapVars fun idx =>
    match (env.getD idx default).whnf with
    | .i s => s
    | _ => panic! "evalI: not an interval variable").norm

section
variable (G : Globals)
include G

mutual
  partial def Val.vars (v : Val) : Nat :=
    let go := Val.vars
    let goI (r : IExpr) : Nat := levelSet r.vars
    let goClo : Closure → Nat
      | .mk env _ => env.foldl (· ||| go ·) 0
    let goSys (sys : System Val) : Nat := sys.foldl (fun acc (α, u) => acc ||| levelSet (α.map (·.1)) ||| go u) 0
    match v with
    | .univ | .interval => 0
    | .var _ => openBit
    | .flex _ sp => sp.foldl (· ||| go ·.1) openBit
    | .lam _ _ c | .ilam _ c => goClo c
    | .line _ _ vs | .sub _ _ _ vs _ | .lazy vs _ | .cached vs _ => vs
    | .glued _ sp _ => sp.foldl (· ||| go ·.1) 0
    | .app t u _ | .pair t u => go t ||| go u
    | .papp p r x y => go p ||| goI r ||| go x ||| go y
    | .i r => goI r
    | .pi _ _ a c | .sigma _ a c => go a ||| goClo c
    | .fst t | .snd t => go t
    | .pathP a x y => go a ||| go x ||| go y
    | .transp a r u => go a ||| goI r ||| go u
    | .hcomp a sys u => go a ||| goSys sys ||| go u
    | .glueTy a sys => go a ||| goSys sys
    | .glue tySys sys a => goSys tySys ||| goSys sys ||| go a
    | .unglue b sys => go b ||| goSys sys
    | .hcompU a sys => go a ||| goSys sys
    | .glueU tySys us a => goSys tySys ||| goSys us ||| go a
    | .unglueU b sys => go b ||| goSys sys
    | .prim _ args => args.foldl (· ||| go ·) 0
    | .split P env _ x => go P ||| env.foldl (· ||| go ·) 0 ||| go x

  partial def Closure.apply (L : Nat) (κ : Face) : Closure → Val → Val
    | .mk env t, u => eval L κ (u :: env) t

  /-- The head under `κ`, applied at the head only; free when `v` mentions
  none of `κ`'s generators. -/
  partial def frc (L : Nat) (κ : Face) (v : Val) : Val :=
    if κ.isEmpty then v.whnf else gauge .maxFace κ.length <| (act L κ (κ.toSubstOn v.vars) v).whnf

  /-- `frc` short of unfolding a definition. -/
  partial def frcG (L : Nat) (κ : Face) (v : Val) : Val :=
    if κ.isEmpty then v.whnfG else (act L κ (κ.toSubstOn v.vars) v).whnfG

  partial def lineApp (L : Nat) (κ : Face) (f : Val) (r : IExpr) : Val :=
    match frcG L κ f with
    | .glued n sp v => .glued n ((.i r, .expl) :: sp) (Thunk.mk fun _ => lineApp L κ v.get r)
    | f =>
    match f.whnf with
    | .ilam _ c => c.apply L κ (.i r)
    | .lam _ _ c => c.apply L κ (.i r)
    | .line l body _ => tick .insts <| act L κ [(l, r)] body.get
    | f => vApp L κ f (.i r) .expl

  partial def vApp (L : Nat) (κ : Face) (t u : Val) (i : Icit) : Val :=
    match frcG L κ t with
    | .glued n sp v => .glued n ((u, i) :: sp) (Thunk.mk fun _ => vApp L κ v.get u i)
    | t =>
    match t.whnf with
    | .lam _ _ c => c.apply L κ u
    | .ilam _ c => c.apply L κ u
    | t@(.line ..) =>
      match frc L κ u with
      | .i r => lineApp L κ t r
      | _ => panic! "vApp: line applied to a non-interval"
    | .flex m sp => .flex m ((u, i) :: sp)
    | .transp a r f => transpApp L κ a r f u i
    | .hcomp a sys f => hcompApp L κ a sys f u i
    | .prim n args => prim' L κ n (args ++ [u])
    | t => cache (.app t u i)

  partial def vAppSp (L : Nat) (κ : Face) (t : Val) : Spine → Val
    | [] => t
    | (u, i) :: sp => vApp L κ (vAppSp L κ t sp) u i

  partial def vFst (L : Nat) (κ : Face) (t : Val) : Val :=
    match frc L κ t with
    | .pair u _ => u
    | t => cache (.fst t)

  partial def vSnd (L : Nat) (κ : Face) (t : Val) : Val :=
    match frc L κ t with
    | .pair _ w => w
    | t => cache (.snd t)

  partial def papp' (L : Nat) (κ : Face) (p : Val) (r : IExpr) (x y : Val) : Val :=
    let rκ := κ.apply r
    if rκ.isZero then x
    else if rκ.isOne then y
    else match frcG L κ p with
    | .glued n sp v => .glued n ((.i r, .expl) :: sp) (Thunk.mk fun _ => papp' L κ v.get r x y)
    | p =>
    match p.whnf with
    | .ilam _ c => c.apply L κ (.i r)
    | .lam _ _ c => c.apply L κ (.i r)
    | .line .. => lineApp L κ p r
    | .flex m sp => .flex m ((.i r, .expl) :: sp)
    | p => cache (.papp p r x y)

  partial def vMeta (m : Nat) : Val :=
    match G.lookupMeta m with
    | .solved v => v
    | .unsolved => .flex m []

  /-- Apply a meta to the bound variables of the environment it was created in. -/
  partial def vAppBDs (L : Nat) (κ : Face) (env : Env) (v : Val) (bds : List BD) : Val :=
    match env, bds with
    | [], [] => v
    | t :: env, .bound :: bds => vApp L κ (vAppBDs L κ env v bds) t .expl
    | _ :: env, .defined :: bds => vAppBDs L κ env v bds
    | _, _ => panic! "vAppBDs: environment and binder list disagree"

  partial def eval (L : Nat) (κ : Face) (env : Env) : Tm → Val
    | .var i => env.getD i default
    | .lam x i t => cache (.lam x i (.mk env t))
    | .ilam x t => cache (.ilam x (.mk env t))
    | .app t u i => vApp L κ (eval L κ env t) (eval L κ env u) i
    | .univ => .univ
    | .pi x i a b => cache (.pi x i (eval L κ env a) (.mk env b))
    | .sigma x a b => cache (.sigma x (eval L κ env a) (.mk env b))
    | .pair t u => cache (.pair (eval L κ env t) (eval L κ env u))
    | .fst t => vFst L κ (eval L κ env t)
    | .snd t => vSnd L κ (eval L κ env t)
    | .letE _ _ t u => eval L κ (eval L κ env t :: env) u
    | .mvar m => vMeta m
    | .insertedMeta m bds => vAppBDs L κ env (vMeta m) bds
    | .interval => .interval
    | .i r => .i (evalI env r)
    | .papp p r x y => papp' L κ (eval L κ env p) (evalI env r) (eval L κ env x) (eval L κ env y)
    | .transp a r u => transp' L κ (eval L κ env a) (evalI env r) (eval L κ env u)
    | .hcomp g a sys u =>
      let comp := if g then ghcomp' else hcomp'
      comp L κ (eval L κ env a) (evalSys L κ env sys) (eval L κ env u)
    | .hfill a sys u r => lineApp L κ (hfill' L κ (eval L κ env a) (evalSys L κ env sys) (eval L κ env u)) (evalI env r)
    | .comp a sys u => comp' L κ (.ilam "i" (.mk env a)) (evalSys L κ env sys) (eval L κ env u) false
    | .glueTy a sys => glueTy' L κ (eval L κ env a) (evalSysFlat L κ env sys)
    | .glue tySys sys a => glue' κ (evalSysFlat L κ env tySys) (evalSysFlat L κ env sys) (eval L κ env a)
    | .unglue b sys => unglue' L κ (eval L κ env b) (evalSysFlat L κ env sys)
    | .glueU tySys us a => glueU' κ (evalSys L κ env tySys) (evalSysFlat L κ env us) (eval L κ env a)
    | .unglueU b sys => unglueU' L κ (eval L κ env b) (evalSys L κ env sys)
    | .prim n => prim' L κ n []
    | .top n =>
      match G.def? n with
      | some (v, _) => .glued n [] v
      | none => panic! s!"eval: unknown definition {n}"
    | .split P cases x => splitApp L κ (eval L κ env P) env cases (eval L κ env x)
    | .extend n a h sys vars =>
      -- Built at fresh levels and then substituted, so the result is stable
      -- under connections.
      let m := vars.length
      let ks := (List.range m).zip vars
      let σ : Subst := ks.map fun (k, idx) => (L + k, evalI env (.var idx))
      let env' := ks.foldl (fun e (k, idx) => e.set idx (.i (.var (L + k)))) env
      let L' := L + m
      act L κ σ (extend' L' κ n (eval L' κ env' a) (eval L' κ env' h) (evalSysFlat L' κ env' sys))

  /-- Components binding an interval variable become lines, each in the
  environment restricted to its face. -/
  partial def evalSys (L : Nat) (κ : Face) (env : Env) (sys : List (IExpr × Tm)) : System Val :=
    mkSystem κ <| sys.flatMap fun (φ, t) =>
      (invFormula (κ.apply (evalI env φ)) true).map fun δ =>
        (δ, .ilam "j" (.mk (env.map (act L κ δ.toSubst)) t))

  partial def evalSysFlat (L : Nat) (κ : Face) (env : Env) (sys : List (IExpr × Tm)) : System Val :=
    mkSystem κ <| sys.flatMap fun (φ, t) =>
      (invFormula (κ.apply (evalI env φ)) true).map fun δ =>
        (δ, eval L (κ.conj δ) (env.map (act L κ δ.toSubst)) t)

  /-- Skipped outside the support of `σ`; interval values and lines at once;
  anything else deferred, composing with a pending substitution. -/
  partial def act (L : Nat) (κ : Face) (σ : Subst) (v : Val) : Val :=
    if σ.isEmpty then v else
    tick .act <|
    match v with
    | .i r => .i (σ.apply r)
    | .sub L' τ w _ _ => act (max L L') κ (σ.comp τ) w
    | v =>
      let vs := v.vars
      if vs &&& σ.domain == 0 then v else
      match v with
      | .line l body _ =>
        .line L (Thunk.mk fun _ => act (L + 1) κ ((l, .var L) :: σ) body.get) (σ.varsUnder vs)
      | v => tick .subs <| .sub L σ v (σ.varsUnder vs) (Thunk.mk fun _ => push L κ σ v)

  /-- One layer of a substitution known to touch `v`: children deferred,
  rules re-run on the head. -/
  partial def push (L : Nat) (κ : Face) (σ : Subst) (v : Val) : Val :=
    let actClo : Closure → Closure
      | .mk env t => .mk (env.map (act L κ σ)) t
    tick .actNodes <|
    match v with
    | .var l => .var l
    | .flex m sp => .flex m (sp.map fun (u, i) => (act L κ σ u, i))
    | .lam x i c => .lam x i (actClo c)
    | .ilam x c => .ilam x (actClo c)
    | .line .. | .sub .. => act L κ σ v
    | .lazy _ body => act L κ σ body.get
    | .cached _ v => push L κ σ v
    | .glued n sp v =>
      .glued n (sp.map fun (u, i) => (act L κ σ u, i)) (Thunk.mk fun _ => act L κ σ v.get)
    | .app t u i => vApp L κ (act L κ σ t) (act L κ σ u) i
    | .papp p r x y => papp' L κ (act L κ σ p) (σ.apply r) (act L κ σ x) (act L κ σ y)
    | .univ => .univ
    | .interval => .interval
    | .i r => .i (σ.apply r)
    | .pi x i a c => .pi x i (act L κ σ a) (actClo c)
    | .sigma x a c => .sigma x (act L κ σ a) (actClo c)
    | .pair u w => .pair (act L κ σ u) (act L κ σ w)
    | .fst t => vFst L κ (act L κ σ t)
    | .snd t => vSnd L κ (act L κ σ t)
    | .pathP a x y => .pathP (act L κ σ a) (act L κ σ x) (act L κ σ y)
    | .transp a r u => transp' L κ (act L κ σ a) (σ.apply r) (act L κ σ u)
    | .hcomp a sys u => hcomp' L κ (act L κ σ a) (actSys L κ σ sys) (act L κ σ u)
    | .glueTy a sys => glueTy' L κ (act L κ σ a) (actSys L κ σ sys)
    | .glue tySys sys a => glue' κ (actSys L κ σ tySys) (actSys L κ σ sys) (act L κ σ a)
    | .unglue b sys => unglue' L κ (act L κ σ b) (actSys L κ σ sys)
    | .hcompU a sys => hcompU' L κ (act L κ σ a) (actSys L κ σ sys)
    | .glueU tySys us a => glueU' κ (actSys L κ σ tySys) (actSys L κ σ us) (act L κ σ a)
    | .unglueU b sys => unglueU' L κ (act L κ σ b) (actSys L κ σ sys)
    | .prim n args => prim' L κ n (args.map (act L κ σ))
    | .split P env cases x => splitApp L κ (act L κ σ P) (env.map (act L κ σ)) cases (act L κ σ x)

  partial def actSys (L : Nat) (κ : Face) (σ : Subst) (sys : System Val) : System Val :=
    System.act (act L κ) κ σ sys

  /-- Substitute the endpoints `α` assigns: for a peeked variable, and to
  pre-restrict a face scope's captures once. Only `κ` guarantees the
  restriction. -/
  partial def face (L : Nat) (κ : Face) (α : Face) (v : Val) : Val :=
    act L κ α.toSubst v

  partial def faceSys (L : Nat) (κ : Face) (α : Face) (sys : System Val) : System Val :=
    actSys L κ α.toSubst sys

  /-- Each face `α` with `κ ∧ α` and its component pre-restricted along `α`. -/
  partial def sysUnder (L : Nat) (κ : Face) (sys : System Val) : List (Face × Face × Val) :=
    System.under κ sys |>.map fun (α, κα, s) => (α, κα, face L κ α s)

  /-- Body memoised at the fresh level `L`; the closure carries the
  cofibration it runs under. -/
  partial def mkLine (L : Nat) (c : Line) : Val :=
    let vs := Line.vars c
    let c := Line.prune vs c
    tick .lines <| .line L (Thunk.mk fun _ => tick .bodies <| gauge .maxLevel (L + 1) <| c.apply (L + 1) (.var L)) vs

  /-- A line from a body mentioning the fresh level `L`. -/
  partial def mkBind (L : Nat) (body : Val) : Val :=
    .line L (Thunk.pure body) (clearLevel body.vars L)

  /-- A deferred computation with the support of its captures. -/
  partial def mkLazy (L : Nat) (c : Line) : Val :=
    let vs := Line.vars c
    let c := Line.prune vs c
    tick .lazies <| .lazy vs (Thunk.mk fun _ => tick .lazyBodies <| c.apply L .zero)

  partial def cache (v : Val) : Val :=
    tick .cacheds <| .cached v.vars v

  partial def lazyFst (L : Nat) (κ : Face) (v : Val) : Val :=
    mkLazy L (closure% fun L1 _ => vFst L1 κ v)

  partial def lazySnd (L : Nat) (κ : Face) (v : Val) : Val :=
    mkLazy L (closure% fun L1 _ => vSnd L1 κ v)

  partial def constLine (L : Nat) (v : Val) : Val :=
    mkLine L (closure% fun _ _ => v)

  /-- The reversed line `j ↦ s (¬ j)`. -/
  partial def revLine (L : Nat) (κ : Face) (s : Val) : Val :=
    mkLine L (closure% fun L1 j => lineApp L1 κ s (.neg j))

  partial def prim' (L : Nat) (κ : Face) (name : String) (args : List Val) : Val :=
    match name, args with
    | "I", [] => .interval
    | "PathP", [a, x, y] => cache (.pathP a x y)
    | "Path", [a, x, y] => cache (.pathP (.ilam "_" (.mk [a] (.var 1))) x y)
    | _, _ =>
      match G.con? name with
      | some (_, con) =>
        if args.length == con.arity then
          let env := args.reverse
          match con.boundary.find? (fun (φ, _) => (κ.apply (evalI env φ)).isOne) with
          | some (_, e) => eval L κ env e
          | none => cache (.prim name args)
        else .prim name args
      | none =>
        match primDef name with
        | some (arity, body) =>
          if args.length == arity then args.foldl (fun f a => vApp L κ f a .expl) (eval L κ [] body)
          else .prim name args
        | none => cache (.prim name args)

  /-- Reduces on a saturated constructor and, at a HIT, on `hcomp` by the
  CHM rule. -/
  partial def splitApp (L : Nat) (κ : Face) (P : Val) (env : Env) (cases : List (String × List String × Tm)) (x : Val) : Val :=
    match frc L κ x with
    | .prim c args =>
      match cases.find? (·.1 == c), G.con? c with
      | some (_, _, body), some (_, con) =>
        if args.length == con.arity then eval L κ (args.reverse ++ env) body
        else .split P env cases x
      | _, _ => cache (.split P env cases x)
    | .hcomp (.prim D []) sys u =>
      match G.data? D with
      | some d =>
        if d.hit then
          tick .splitHcomp <|
          let fill := hfill' L κ (.prim D []) sys u
          let pline := mkLine L (closure% fun L1 j => vApp L1 κ P (lineApp L1 κ fill j) .expl)
          let sides := sysUnder L κ sys |>.map fun (α, κα, s) =>
            let P := face L κ α P
            let env := env.map (face L κ α)
            (α, mkLine L (closure% fun L1 j => splitApp L1 κα P env cases (lineApp L1 κα s j)))
          comp' L κ pline (mkSystem κ sides) (splitApp L κ P env cases u) false
        else .split P env cases x
      | none => cache (.split P env cases x)
    | .glueU .. | .glue .. =>
      panic! s!"split: case {cases.map (·.1)} on {x.headStr 4}, motive {P.headStr 1}"
    | .hcomp A .. =>
      match A with
      | .hcompU .. | .glueTy .. =>
        panic! s!"split: case {cases.map (·.1)} on {x.headStr 4} at type {A.headStr 2}"
      | _ => cache (.split P env cases x)
    | _ => cache (.split P env cases x)

  /-- Constructor-wise when the base and every side share a constructor.
  Closed, the sides share the base's constructor by canonicity and are not
  forced here: each field projects them lazily (cctt's closed `hcom`). -/
  partial def hcompData (L : Nat) (κ : Face) (A : Val) (sys : System Val) (u : Val) : Val :=
    match frc L κ u with
    | .prim c args =>
      match G.con? c with
      | some (_, con) =>
        let closed := (sys.foldl (fun acc (_, s) => acc ||| s.vars) u.vars) &&& openBit == 0
        let sameCon := closed || (System.under κ sys |>.all fun (_, κα, s) =>
          match frc (L + 1) κα (lineApp (L + 1) κα s (.var L)) with
          | .prim c' args' => c' == c && args'.length == args.length
          | _ => false)
        if args.length != con.fields.length || !sameCon then .hcomp A sys u
        else (if closed then tick .hcompDataClosed else id) <|
          cache (.prim c (hcompFields L κ 0 con.fields [] sys args))
      | none => cache (.hcomp A sys u)
    | _ => cache (.hcomp A sys u)

  /-- `fills`: the fillers of the previous fields, most recent first. -/
  partial def hcompFields (L : Nat) (κ : Face) (k : Nat) (fields : List (String × Tm)) (fills : List Val)
      (sys : System Val) (args : List Val) : List Val :=
    match fields with
    | [] => []
    | (_, T) :: rest =>
      let tline := mkLine L (closure% fun L1 j => eval L1 κ (fills.map fun f => lineApp L1 κ f j) T)
      let sysk := sysUnder L κ sys |>.map fun (α, κα, s) => (α, mkLine L (closure% fun L1 j =>
        match frc L1 κα (lineApp L1 κα s j) with
        | .prim _ as => as.getD k default
        | _ => panic! "hcomp: side is not a constructor"))
      let uk := args.getD k default
      let vk := mkLazy L (closure% fun L1 _ => comp' L1 κ tline sysk uk false)
      let fk := compFill' L κ tline sysk uk
      vk :: hcompFields L κ (k + 1) rest (fk :: fills) sys args

  /-- The filler of a heterogeneous composition, as a line. -/
  partial def compFill' (L : Nat) (κ : Face) (a : Val) (sys : System Val) (u0 : Val) : Val :=
    mkLine L (closure% fun L1 j =>
      let sides := sysUnder L1 κ sys |>.map fun (α, κα, s) =>
        (α, mkLine L1 (closure% fun L2 k => lineApp L2 κα s (.meet j k)))
      let start := (invFormula (κ.apply (.neg j)) true).map fun δ => (δ, constLine L1 u0)
      comp' L1 κ (mkLine L1 (closure% fun L2 k => lineApp L2 κ a (.meet j k))) (mkSystem κ (sides ++ start)) u0 false)

  /-- The components of a line of path types at a point. -/
  partial def pathPAt (L : Nat) (κ : Face) (a : Val) (i : IExpr) : Val × Val × Val :=
    match frc L κ (lineApp L κ a i) with
    | .pathP A x y => (A, x, y)
    | _ => panic! "transp: line is not constantly a path type"

  /-- `transp^i A r u`, with `A` a line; identity when `r = 1`. -/
  partial def transp' (L : Nat) (κ : Face) (a : Val) (r : IExpr) (u : Val) : Val :=
    if (κ.apply r).isOne then u else
    tick .transp <|
    match frc (L + 1) κ (lineApp (L + 1) κ a (.var L)) with
    | .pi .. => tick .transpStuck <| cache (.transp a r u)
    | .sigma .. =>
      tick .transpSigma <|
      let aline := mkLine L (closure% fun L1 i =>
        match frc L1 κ (lineApp L1 κ a i) with
        | .sigma _ A _ => A
        | _ => panic! "transp: line is not constantly a pair type")
      let v1 := mkLazy L (closure% fun L1 _ => transp' L1 κ aline r (vFst L1 κ u))
      let fill := transpFill L κ aline r (vFst L κ u)
      let bline := mkLine L (closure% fun L1 i =>
        match frc L1 κ (lineApp L1 κ a i) with
        | .sigma _ _ c => c.apply L1 κ (lineApp L1 κ fill i)
        | _ => panic! "transp: line is not constantly a pair type")
      .pair v1 (mkLazy L (closure% fun L1 _ => transp' L1 κ bline r (vSnd L1 κ u)))
    | .pathP .. =>
      tick .transpPath <|
      let (_, x0, y0) := pathPAt L κ a .zero
      mkLine L (closure% fun L1 k =>
        let aline := mkLine L1 (closure% fun L2 i => lineApp L2 κ (pathPAt L2 κ a i).1 k)
        let base := papp' L1 κ u k x0 y0
        let sides := (invFormula (κ.apply r) true).map (fun δ => (δ, constLine L1 base))
          ++ (invFormula (κ.apply (.neg k)) true).map (fun δ =>
            let κδ := κ.conj δ
            (δ, mkLine L1 (closure% fun L2 i => (pathPAt L2 κδ a i).2.1)))
          ++ (invFormula (κ.apply k) true).map (fun δ =>
            let κδ := κ.conj δ
            (δ, mkLine L1 (closure% fun L2 i => (pathPAt L2 κδ a i).2.2)))
        comp' L1 κ aline (mkSystem κ sides) base false)
    | .univ => u
    | .prim n [] => if (G.data? n).isSome then u else .transp a r u
    | .glueTy A sysG => transpGlue L κ r u A sysG
    | .hcompU A sysE => transpHU L κ r u A sysE
    | w =>
      let neutral : Val → Bool
        | .var .. | .app .. | .flex .. | .papp .. | .fst .. | .snd ..
        | .unglue .. | .unglueU .. | .transp .. | .hcomp .. => true
        | _ => false
      match w with
      | .split _ _ _ x =>
        if neutral x.whnf then tick .transpStuck <| cache (.transp a r u)
        else panic! s!"transp stuck at L={L} on type {w.headStr 4}, element {u.headStr 2}"
      | w =>
        if neutral w then tick .transpStuck <| cache (.transp a r u)
        else panic! s!"transp stuck at L={L} on type {w.headStr 4}, element {u.headStr 2}"

  /-- The codomain of a line of function types at a point, at an argument. -/
  partial def piCod (L : Nat) (κ : Face) (a : Val) (i : IExpr) (x : Val) : Val :=
    match frc L κ (lineApp L κ a i) with
    | .pi _ _ _ c => c.apply L κ x
    | _ => panic! "transp: line is not constantly a function type"

  /-- `transp` at a function type, applied: `(transp^i ((x : A) → B) r f) v`. -/
  partial def transpApp (L : Nat) (κ : Face) (a : Val) (r : IExpr) (f u : Val) (i : Icit) : Val :=
    match frc (L + 1) κ (lineApp (L + 1) κ a (.var L)) with
    | .pi _ _ .interval _ =>
      transp' L κ (mkLine L (closure% fun L1 i' => piCod L1 κ a i' u)) r (vApp L κ f u i)
    | .pi .. =>
      let domNeg := mkLine L (closure% fun L1 i' =>
        match frc L1 κ (lineApp L1 κ a (.neg i')) with
        | .pi _ _ dom _ => dom
        | _ => panic! "transp: line is not constantly a function type")
      let w := transpFill L κ domNeg r u
      let vline := revLine L κ w
      let v0 := lineApp L κ vline .zero
      transp' L κ (mkLine L (closure% fun L1 i' => piCod L1 κ a i' (lineApp L1 κ vline i'))) r (vApp L κ f v0 i)
    | _ => cache (.app (cache (.transp a r f)) u i)

  /-- The filler `Transp^i A r u`: a line from `u` to `transp^i A r u`. -/
  partial def transpFill (L : Nat) (κ : Face) (a : Val) (r : IExpr) (u : Val) : Val :=
    mkLine L (closure% fun L1 i =>
      transp' L1 κ (mkLine L1 (closure% fun L2 k => lineApp L2 κ a (.meet i k))) (.join r (.neg i)) u)

  /-- Transport from `A r` to `A 1`; the identity when `r = 1`. -/
  partial def forward (L : Nat) (κ : Face) (a : Val) (r : IExpr) (u : Val) : Val :=
    transp' L κ (mkLine L (closure% fun L1 i => lineApp L1 κ a (.join i r))) r u

  /-- `comp^i A [φ ↦ u] u₀ = hcomp^i (A 1) [φ ↦ forward A i (u i)] (forward A 0 u₀)`;
  `ghcomp` when `general`. -/
  partial def comp' (L : Nat) (κ : Face) (a : Val) (sys : System Val) (u0 : Val) (general : Bool) : Val :=
    let sides := sysUnder L κ sys |>.map fun (α, κα, s) =>
      let a := face L κ α a
      (α, mkLine L (closure% fun L1 i => forward L1 κα a i (lineApp L1 κα s i)))
    let base := forward L κ a .zero u0
    if general then ghcomp' L κ (lineApp L κ a .one) (mkSystem κ sides) base
    else hcomp' L κ (lineApp L κ a .one) (mkSystem κ sides) base

  /-- `ghcomp A [φ ↦ u] u₀ = hcomp A [φ ↦ u, ¬φ ↦ u₀] u₀`. -/
  partial def ghcomp' (L : Nat) (κ : Face) (A : Val) (sys : System Val) (u : Val) : Val :=
    let extra := (invFormula (κ.apply sys.cof) false).map fun β => (β, constLine L (face L κ β u))
    hcomp' L κ A (mkSystem κ (sys ++ extra)) u

  partial def hfill' (L : Nat) (κ : Face) (A : Val) (sys : System Val) (u : Val) : Val :=
    mkLine L (closure% fun L1 j =>
      let sides := sysUnder L1 κ sys |>.map fun (α, κα, s) =>
        (α, mkLine L1 (closure% fun L2 k => lineApp L2 κα s (.meet j k)))
      let start := (invFormula (κ.apply (.neg j)) true).map fun δ => (δ, constLine L1 u)
      hcomp' L1 κ A (mkSystem κ (sides ++ start)) u)

  /-- The filler of `ghcomp`: `hfill` with the `¬φ ↦ u` sides. -/
  partial def ghfill' (L : Nat) (κ : Face) (A : Val) (sys : System Val) (u : Val) : Val :=
    let extra := (invFormula (κ.apply sys.cof) false).map fun β => (β, constLine L (face L κ β u))
    hfill' L κ A (mkSystem κ (sys ++ extra)) u

  partial def hcomp' (L : Nat) (κ : Face) (A : Val) (sys : System Val) (u : Val) : Val :=
    let sys := System.restrict κ sys
    match sys.total? with
    | some s => lineApp L κ s .one
    | none =>
    tick .hcomp <|
    let A := frc L κ A
    match A with
    | .pi .. => tick .hcompStuck <| cache (.hcomp A sys u)
    | .sigma _ a c =>
      tick .hcompSigma <|
      let sys1 := sysUnder L κ sys |>.map fun (α, κα, s) =>
        (α, mkLine L (closure% fun L1 j => vFst L1 κα (lineApp L1 κα s j)))
      let sys2 := sysUnder L κ sys |>.map fun (α, κα, s) =>
        (α, mkLine L (closure% fun L1 j => vSnd L1 κα (lineApp L1 κα s j)))
      let u1 := vFst L κ u
      let v1 := mkLazy L (closure% fun L1 _ => hcomp' L1 κ a sys1 u1)
      let fill1 := hfill' L κ a sys1 u1
      let bline := mkLine L (closure% fun L1 j => c.apply L1 κ (lineApp L1 κ fill1 j))
      .pair v1 (mkLazy L (closure% fun L1 _ => comp' L1 κ bline sys2 (vSnd L1 κ u) false))
    | .pathP a x y =>
      tick .hcompPath <|
      mkLine L (closure% fun L1 k =>
        let sides := (sysUnder L1 κ sys |>.map fun (α, κα, s) =>
            (α, mkLine L1 (closure% fun L2 j => papp' L2 κα (lineApp L2 κα s j) k x y)))
          ++ (invFormula (κ.apply (.neg k)) true).map (fun δ => (δ, constLine L1 x))
          ++ (invFormula (κ.apply k) true).map (fun δ => (δ, constLine L1 y))
        hcomp' L1 κ (lineApp L1 κ a k) (mkSystem κ sides) (papp' L1 κ u k x y))
    | .univ => tick .hcompU <| hcompU' L κ u sys
    | .glueTy B sysG => tick .hcompGlue <| hcompGlue L κ B sysG sys u
    | .hcompU B sysE => tick .hcompHU <| hcompHU L κ B sysE sys u
    | .prim n [] =>
      match G.data? n with
      | some d => if d.hit then tick .hcompHIT <| .hcomp A sys u else tick .hcompData <| hcompData L κ A sys u
      | none => tick .hcompStuck <| cache (.hcomp A sys u)
    | _ => tick .hcompStuck <| cache (.hcomp A sys u)

  /-- `hcomp` at a function type, applied. -/
  partial def hcompApp (L : Nat) (κ : Face) (A : Val) (sys : System Val) (f u : Val) (i : Icit) : Val :=
    match frc L κ A with
    | .pi _ _ _ c =>
      let sides := sysUnder L κ sys |>.map fun (α, κα, s) =>
        let u := face L κ α u
        (α, mkLine L (closure% fun L1 j => vApp L1 κα (lineApp L1 κα s j) u i))
      hcomp' L κ (c.apply L κ u) (mkSystem κ sides) (vApp L κ f u i)
    | _ => cache (.app (cache (.hcomp A sys f)) u i)

  partial def hcompU' (L : Nat) (κ : Face) (A : Val) (sys : System Val) : Val :=
    let sys := System.restrict κ sys
    match sys.total? with
    | some E => lineApp L κ E .one
    | none => cache (.hcompU A sys)

  partial def glueU' (κ : Face) (tySys us : System Val) (a : Val) : Val :=
    let us := System.restrict κ us
    match us.total? with
    | some t => t
    | none => cache (.glueU (System.restrict κ tySys) us a)

  /-- `E 1 → E 0`. -/
  partial def eqFun (L : Nat) (κ : Face) (E t : Val) : Val :=
    transp' L κ (revLine L κ E) .zero t

  partial def unglueU' (L : Nat) (κ : Face) (b : Val) (sys : System Val) : Val :=
    let sys := System.restrict κ sys
    match sys.total? with
    | some E => eqFun L κ E b
    | none =>
      match frc L κ b with
      | .glueU _ _ a => a
      | .prim .. | .pair .. =>
        panic! s!"unglueU of {b.headStr 2} at {(Val.hcompU .univ sys).headStr}"
      | b => cache (.unglueU b sys)

  /-- As `hcompGlue`, with `eqFun` as the equivalence. -/
  partial def hcompHU (L : Nat) (κ : Face) (A : Val) (sysE sys : System Val) (u : Val) : Val :=
    let comps := sysUnder L κ sysE |>.map fun (γ, κγ, E) =>
      let T := lineApp L κγ E .one
      let sysγ := faceSys L κ γ sys
      let uγ := face L κ γ u
      (γ, κγ, E, mkLazy L (closure% fun L1 _ => hcomp' L1 κγ T sysγ uγ), hfill' L κγ T sysγ uγ)
    let sidesA := (sysUnder L κ sys |>.map fun (α, κα, s) =>
        let sysE := faceSys L κ α sysE
        (α, mkLine L (closure% fun L1 j => unglueU' L1 κα (lineApp L1 κα s j) sysE)))
      ++ comps.map (fun (γ, κγ, E, _, fill) =>
        (γ, mkLine L (closure% fun L1 j => eqFun L1 κγ E (lineApp L1 κγ fill j))))
    let a := mkLazy L (closure% fun L1 _ => hcomp' L1 κ A (mkSystem κ sidesA) (unglueU' L1 κ u sysE))
    glueU' κ sysE (comps.map fun (γ, _, _, t, _) => (γ, t)) a

  /-- A line from `eqFun E u` to `u`. -/
  partial def transpFillNeg (L : Nat) (κ : Face) (E u : Val) : Val :=
    revLine L κ (transpFill L κ (revLine L κ E) .zero u)

  /-- Per face of `lemEq`, at `i`: the composite from `p i` up to `E 1`, and
  its filler. -/
  partial def lemEqItem (L : Nat) (κ : Face) (E b : Val) (i : IExpr) (ap : Val) : Val × Val :=
    let aa := vFst L κ ap
    let pa := vSnd L κ ap
    let base := papp' L κ pa i b (eqFun L κ E aa)
    let sides := mkSystem κ <|
      (invFormula (κ.apply (.neg i)) true).map (fun δ => (δ, transpFill L (κ.conj δ) E .zero b))
      ++ (invFormula (κ.apply i) true).map (fun δ => (δ, transpFillNeg L (κ.conj δ) E aa))
    (comp' L κ E sides base false, compFill' L κ E sides base)

  /-- cubicaltt's `lemEq`: a total fiber `(a : E 1, p : Path (E 0) b (eqFun E a))`
  extending a partial one. -/
  partial def lemEq (L : Nat) (κ : Face) (E b : Val) (aps : System Val) : Val × Val :=
    tick .lemEq <|
    let ta := lineApp L κ E .one
    let faces := sysUnder L κ aps |>.map fun (α, κα, ap) => (α, κα, face L κ α E, face L κ α b, ap)
    let p1s := mkSystem κ (faces.map fun (α, κα, E, b, ap) =>
      (α, mkLine L (closure% fun L1 i => (lemEqItem L1 κα E b i ap).1)))
    let tb := mkLazy L (closure% fun L1 _ => transp' L1 κ E .zero b)
    let a := mkLazy L (closure% fun L1 _ => ghcomp' L1 κ ta p1s tb)
    let p1 := ghfill' L κ ta p1s tb
    let p := mkLine L (closure% fun L1 i =>
      let sides := (invFormula (κ.apply (.neg i)) true).map (fun δ =>
          let κδ := κ.conj δ
          (δ, revLine L1 κδ (transpFill L1 κδ E .zero b)))
        ++ (invFormula (κ.apply i) true).map (fun δ =>
          let κδ := κ.conj δ
          (δ, revLine L1 κδ (transpFillNeg L1 κδ E a)))
        ++ (faces.map fun (α, κα, E, b, ap) => (α, revLine L1 κα (lemEqItem L1 κα E b i ap).2))
      comp' L1 κ (revLine L1 κ E) (mkSystem κ sides) (lineApp L1 κ p1 i) false)
    (a, p)

  /-- `transpGlue` with `eqFun` as the equivalence and `lemEq` for the fibers. -/
  partial def transpHU (L : Nat) (κ : Face) (r : IExpr) (b0 A : Val) (sysE : System Val) : Val :=
    tick .transpHU <|
    let A1 := face L κ [(L, true)] A
    let sysE0 := faceSys L κ [(L, false)] sysE
    let sysE1 := faceSys L κ [(L, true)] sysE
    let Aline := mkBind L A
    let a0 := unglueU' L κ b0 sysE0
    let rFaces := invFormula (κ.apply r) true
    let δs := sysE.filter fun (γ, _) => !γ.mentions L
    let tfills := System.under κ δs |>.map fun (γ, κγ, E) =>
      let E := face L κ γ (mkBind L E)
      (γ, κγ, E, transpFill L κγ (mkLine L (closure% fun L1 i' => lineApp L1 κγ (lineApp L1 κγ E i') .one)) r (face L κ γ b0))
    let sidesA := rFaces.map (fun δ => (δ, constLine L (face L κ δ a0)))
      ++ tfills.map (fun (γ, κγ, E, tf) =>
        (γ, mkLine L (closure% fun L1 i' => eqFun L1 κγ (lineApp L1 κγ E i') (lineApp L1 κγ tf i'))))
    let a1 := mkLazy L (closure% fun L1 _ => comp' L1 κ Aline (mkSystem κ sidesA) a0 true)
    let fibs := sysUnder L κ sysE1 |>.map fun (γ1, κ1, E1) =>
      let a1γ := face L κ γ1 a1
      let b0γ := face L κ γ1 b0
      let θ := (invFormula (κ1.apply r) true).map (fun δ =>
          (δ, Val.pair (face L κ1 δ b0γ) (constLine L (face L κ1 δ a1γ))))
        ++ tfills.filterMap (fun (γ, _, _, tf) => (γ.meet γ1).map fun key =>
          let key := key.minus γ1
          let κk := κ1.conj key
          let tf := face L κ key (face L κ γ1 tf)
          (key, Val.pair (mkLazy L (closure% fun L1 _ => lineApp L1 κk tf .one)) (constLine L (face L κ1 key a1γ))))
      let fib := mkLazy L (closure% fun L1 _ =>
        let (t1, α) := lemEq L1 κ1 E1 a1γ (mkSystem κ1 θ)
        Val.pair t1 α)
      (γ1, κ1, E1, lazyFst L κ1 fib, lazySnd L κ1 fib, a1γ)
    let sidesA1 := fibs.map (fun (γ1, κ1, E1, t1, α, a1γ) =>
        (γ1, mkLine L (closure% fun L1 i' => papp' L1 κ1 α i' a1γ (eqFun L1 κ1 E1 t1))))
      ++ rFaces.map (fun δ => (δ, constLine L (face L κ δ a1)))
    let a1' := mkLazy L (closure% fun L1 _ => ghcomp' L1 κ A1 (mkSystem κ sidesA1) a1)
    glueU' κ sysE1 (fibs.map fun (γ1, _, _, t1, _, _) => (γ1, t1)) a1'

  partial def hcompGlue (L : Nat) (κ : Face) (B : Val) (sysG sys : System Val) (u : Val) : Val :=
    let comps := sysUnder L κ sysG |>.map fun (γ, κγ, Te) =>
      let T := vFst L κγ Te
      let f := vFst L κγ (vSnd L κγ Te)
      let sysγ := faceSys L κ γ sys
      let uγ := face L κ γ u
      (γ, κγ, f, mkLazy L (closure% fun L1 _ => hcomp' L1 κγ T sysγ uγ), hfill' L κγ T sysγ uγ)
    let sidesB := (sysUnder L κ sys |>.map fun (α, κα, s) =>
        let sysG := faceSys L κ α sysG
        (α, mkLine L (closure% fun L1 j => unglue' L1 κα (lineApp L1 κα s j) sysG)))
      ++ comps.map (fun (γ, κγ, f, _, fill) =>
        (γ, mkLine L (closure% fun L1 j => vApp L1 κγ f (lineApp L1 κγ fill j) .expl)))
    let a := mkLazy L (closure% fun L1 _ => hcomp' L1 κ B (mkSystem κ sidesB) (unglue' L1 κ u sysG))
    glue' κ sysG (comps.map fun (γ, _, _, t, _) => (γ, t)) a

  /-- `ext (c, p) [θ ↦ v] = hcomp [θ ↦ p v j, ¬θ ↦ c] c`. -/
  partial def ext (L : Nat) (κ : Face) (X contr : Val) (θ : System Val) : Val :=
    let c := vFst L κ contr
    let p := vSnd L κ contr
    let sides := (sysUnder L κ θ |>.map fun (α, κα, w) =>
        let p := face L κ α p
        let c := face L κ α c
        (α, mkLine L (closure% fun L1 j => papp' L1 κα (vApp L1 κα p w .expl) j c w)))
      ++ (invFormula (κ.apply θ.cof) false).map (fun β => (β, constLine L (face L κ β c)))
    hcomp' L κ X (mkSystem κ sides) c

  /-- kangrongji's `extend`: peel the last cube variable and fill an
  `(n-1)`-cube in the path type between its two faces; a proposition fills
  by `h x₀ x₁`, a contractible type by `ext`. -/
  partial def extend' (L : Nat) (κ : Face) (n : Nat) (A h : Val) (sys : System Val) : Val :=
    let sys := System.restrict κ sys
    match sys.total? with
    | some v => v
    | none =>
    let ls := (sys.map fun (α, _) => α.map (·.1)).flatten.eraseDups
    match ls.max?, n with
    | none, 0 => vFst L κ h
    | none, _ => panic! "hlevel: no cube variables at a positive level"
    | some _, 0 => ext L κ A h sys
    | some l, 1 =>
      let x0 := (sys.find? (·.1 == [(l, false)])).map (·.2) |>.getD (panic! "hlevel: missing face")
      if ls.length > 1 then
        -- Above the level: one composition from a corner.
        let c := act L κ (ls.map fun l' => (l', IExpr.zero)) x0
        let sides := sysUnder L κ sys |>.map fun (α, κα, w) =>
          let hα := face L κ α h
          (α, mkLine L (closure% fun L1 j => papp' L1 κα (vApp L1 κα (vApp L1 κα hα c .expl) w .expl) j c w))
        hcomp' L κ A (mkSystem κ sides) c
      else
      let x1 := (sys.find? (·.1 == [(l, true)])).map (·.2) |>.getD (panic! "hlevel: missing face")
      -- Over a family: the endpoints transported to the point, which at the
      -- ends is a transport with `r = 1`, so no correction is needed.
      if hasLevel (Val.vars A) l then
        let Al := Val.line l (Thunk.pure A) (clearLevel (Val.vars A) l)
        let f0 := lineApp L κ (transpFill L κ Al .zero x0) (.var l)
        let f1 := lineApp L κ (transpFill L κ (revLine L κ Al) .zero x1) (.neg (.var l))
        papp' L κ (vApp L κ (vApp L κ h f0 .expl) f1 .expl) (.var l) f0 f1
      else papp' L κ (vApp L κ (vApp L κ h x0 .expl) x1 .expl) (.var l) x0 x1
    | some l, n + 2 =>
      let x0 := (sys.find? (·.1 == [(l, false)])).map (·.2) |>.getD (panic! "hlevel: missing face")
      let x1 := (sys.find? (·.1 == [(l, true)])).map (·.2) |>.getD (panic! "hlevel: missing face")
      let sys' := sys.filterMap fun (α, w) =>
        if α.mentions l then none else some (α, Val.line l (Thunk.pure w) (clearLevel (Val.vars w) l))
      let (P, h') :=
        if hasLevel (Val.vars A) l then
          -- The h-level of `PathP (λ l. A) x₀ x₁` is that of
          -- `Path (A 1) (transp A x₀) x₁`, transported back along
          -- `t ↦ PathP (λ j. A (t ∨ j)) (transpFill A x₀ t) x₁`.
          let Al := Val.line l (Thunk.pure A) (clearLevel (Val.vars A) l)
          let fill := transpFill L κ Al .zero x0
          let hx := vApp L κ (vApp L κ (face L κ [(l, true)] h) (lineApp L κ fill .one) .expl) x1 .expl
          let lvl := eval L κ [] (isOfHLevelTm (n + 1))
          let T := mkLine L (closure% fun L1 t =>
            let Aline := mkLine L1 (closure% fun L2 j => lineApp L2 κ Al (.join t j))
            vApp L1 κ lvl (prim' L1 κ "PathP" [Aline, lineApp L1 κ fill t, x1]) .expl)
          (prim' L κ "PathP" [Al, x0, x1], transp' L κ (revLine L κ T) .zero hx)
        else (prim' L κ "Path" [A, x0, x1], vApp L κ (vApp L κ h x0 .expl) x1 .expl)
      papp' L κ (extend' L κ (n + 1) P h' sys') (.var l) x0 x1

  /-- After Cubical Agda / Huber, the `∀i.φ` correction folded into a
  `ghcomp` so no empty systems arise. `A` and `sysG` are peeked at
  `i = var L` and rebound by `mkBind`. -/
  partial def transpGlue (L : Nat) (κ : Face) (r : IExpr) (b0 A : Val) (sysG : System Val) : Val :=
    tick .transpGlue <|
    let A1 := face L κ [(L, true)] A
    let sysG0 := faceSys L κ [(L, false)] sysG
    let sysG1 := faceSys L κ [(L, true)] sysG
    let Aline := mkBind L A
    let a0 := unglue' L κ b0 sysG0
    let rFaces := invFormula (κ.apply r) true
    let δs := sysG.filter fun (γ, _) => !γ.mentions L
    let tfills := System.under κ δs |>.map fun (γ, κγ, Te) =>
      let Te := face L κ γ (mkBind L Te)
      (γ, κγ, Te, transpFill L κγ (mkLine L (closure% fun L1 i' => vFst L1 κγ (lineApp L1 κγ Te i'))) r (face L κ γ b0))
    let sidesA := rFaces.map (fun δ => (δ, constLine L (face L κ δ a0)))
      ++ tfills.map (fun (γ, κγ, Te, tf) =>
        (γ, mkLine L (closure% fun L1 i' =>
          vApp L1 κγ (vFst L1 κγ (vSnd L1 κγ (lineApp L1 κγ Te i'))) (lineApp L1 κγ tf i') .expl)))
    let a1 := mkLazy L (closure% fun L1 _ => comp' L1 κ Aline (mkSystem κ sidesA) a0 true)
    let fibs := sysUnder L κ sysG1 |>.map fun (γ1, κ1, Te1) =>
      let T1 := vFst L κ1 Te1
      let e1 := vSnd L κ1 Te1
      let f1 := vFst L κ1 e1
      let a1γ := face L κ γ1 a1
      let b0γ := face L κ γ1 b0
      let A1γ := face L κ γ1 A1
      let θ := (invFormula (κ1.apply r) true).map (fun δ =>
          (δ, Val.pair (face L κ1 δ b0γ) (constLine L (face L κ1 δ a1γ))))
        ++ tfills.filterMap (fun (γ, _, _, tf) => (γ.meet γ1).map fun key =>
          let key := key.minus γ1
          let κk := κ1.conj key
          let tf := face L κ key (face L κ γ1 tf)
          (key, Val.pair (mkLazy L (closure% fun L1 _ => lineApp L1 κk tf .one)) (constLine L (face L κ1 key a1γ))))
      let fib := mkLazy L (closure% fun L1 _ =>
        let fibTy := prim' L1 κ1 "fiber" [T1, A1γ, f1, a1γ]
        let contr := vApp L1 κ1 (vSnd L1 κ1 e1) a1γ .expl
        ext L1 κ1 fibTy contr (mkSystem κ1 θ))
      (γ1, κ1, lazyFst L κ1 fib, lazySnd L κ1 fib, f1, a1γ)
    let sidesA1 := fibs.map (fun (γ1, κ1, t1, α, f1, a1γ) =>
        (γ1, mkLine L (closure% fun L1 i' => papp' L1 κ1 α i' a1γ (vApp L1 κ1 f1 t1 .expl))))
      ++ rFaces.map (fun δ => (δ, constLine L (face L κ δ a1)))
    let a1' := mkLazy L (closure% fun L1 _ => ghcomp' L1 κ A1 (mkSystem κ sidesA1) a1)
    glue' κ sysG1 (fibs.map fun (γ1, _, t1, _, _, _) => (γ1, t1)) a1'

  partial def glueTy' (L : Nat) (κ : Face) (A : Val) (sys : System Val) : Val :=
    let sys := System.restrict κ sys
    match sys.total? with
    | some Te => vFst L κ Te
    | none => cache (.glueTy A sys)

  partial def glue' (κ : Face) (tySys sys : System Val) (a : Val) : Val :=
    let sys := System.restrict κ sys
    match sys.total? with
    | some t => t
    | none => cache (.glue (System.restrict κ tySys) sys a)

  partial def unglue' (L : Nat) (κ : Face) (b : Val) (sys : System Val) : Val :=
    let sys := System.restrict κ sys
    match sys.total? with
    | some Te => vApp L κ (vFst L κ (vSnd L κ Te)) b .expl
    | none =>
      match frc L κ b with
      | .glue _ _ a => a
      | b => cache (.unglue b sys)
end

end

end defun

section
variable (G : Globals)
include G

/-- `whnfG`, also through solved metavariables. -/
partial def forceG (L : Nat) (v : Val) : Val :=
  match v.whnfG with
  | .flex m sp =>
    match G.lookupMeta m with
    | .solved t => forceG L (vAppSp G L [] t sp)
    | .unsolved => .flex m sp
  | v => v

/-- `forceG`, unfolding definitions. -/
partial def force (L : Nat) (v : Val) : Val :=
  match forceG G L v with
  | .glued _ _ u => force L u.get
  | v => v

/-- A partial renaming from size `dom` to size `cod`, by levels of the
codomain; the identity for quotation, the inverse of a spine for
unification. -/
structure PRen where
  dom : Nat
  cod : Nat
  ren : Nat → Option Nat

namespace PRen

def id (l : Nat) : PRen :=
  { dom := l, cod := l, ren := fun x => if x < l then some x else none }

/-- Lift over an extra bound variable. -/
def lift (p : PRen) : PRen :=
  { dom := p.dom + 1, cod := p.cod + 1, ren := fun x => if x == p.cod then some p.dom else p.ren x }

end PRen

/-- A case body at fresh variables from level `l`, with the renaming lifted
over them. -/
def instCase (l : Nat) (env : Env) (c : String) (body : Tm) : Val × PRen :=
  let (nf, ni) := match G.con? c with
    | some (_, con) => (con.fields.length, con.ivars.length)
    | none => (0, 0)
  let args := (List.range nf).map (fun k => Val.var (l + k))
    ++ (List.range ni).map (fun k => Val.i (.var (l + nf + k)))
  let p := (List.range (nf + ni)).foldl (fun q _ => q.lift) (PRen.id l)
  (eval G (l + nf + ni) [] (args.reverse ++ env) body, p)

/-- Fails on a variable outside the renaming or an occurrence of `occ`. A
definition reads back by name and spine unless `unfold` or that fails. -/
partial def readback (p : PRen) (occ : Option Nat) (unfold : Bool) (v : Val) : Except String Tm := do
  let lvl (x : Nat) : Except String Nat :=
    match p.ren x with
    | some x' => pure (p.dom - x' - 1)
    | none => throw "unify: variable escapes its scope"
  let rbI (r : IExpr) : Except String IExpr := r.mapVarsM fun x => do pure (.var (← lvl x))
  let rbFace (α : Face) : Except String IExpr := rbI α.toIExpr
  let under (f : Val → Val) : Except String Tm := readback p.lift occ unfold (f (.var p.cod))
  let underI (f : IExpr → Val) : Except String Tm := readback p.lift occ unfold (f (.var p.cod))
  let rb := readback p occ unfold
  let rbSys (sys : System Val) : Except String (List (IExpr × Tm)) :=
    sys.mapM fun (α, s) => do pure (← rbFace α, ← underI fun j => lineApp G (p.cod + 1) [] s j)
  let rbSysFlat (sys : System Val) : Except String (List (IExpr × Tm)) :=
    sys.mapM fun (α, t) => do pure (← rbFace α, ← rb t)
  let rbArgs (hd : Tm) (args : List Val) : Except String Tm :=
    args.foldlM (fun t u => do pure (.app t (← rb u) .expl)) hd
  match forceG G p.cod v with
  | .glued n sp u =>
    if unfold then rb u.get else
    try sp.reverse.foldlM (fun t (u, i) => do pure (.app t (← rb u) i)) (.top n)
    catch _ => rb u.get
  | .var x => pure (.var (← lvl x))
  | .flex m sp =>
    if occ == some m then throw "unify: occurs check"
    sp.reverse.foldlM (fun t (u, i) => do pure (.app t (← rb u) i)) (.mvar m)
  | .lam x i c => pure (.lam x i (← under fun u => c.apply G (p.cod + 1) [] u))
  | .ilam x c => pure (.ilam x (← underI fun r => c.apply G (p.cod + 1) [] (.i r)))
  | .line l body _ => pure (.ilam "i" (← underI fun r => act G (p.cod + 1) [] [(l, r)] body.get))
  | .sub .. | .lazy .. | .cached .. => panic! "readback: unforced value"
  | .app t u i => pure (.app (← rb t) (← rb u) i)
  | .papp q r x y => pure (.papp (← rb q) (← rbI r) (← rb x) (← rb y))
  | .univ => pure .univ
  | .interval => pure .interval
  | .i r => pure (.i (← rbI r))
  | .pi x i a c =>
    let b ← match a with
      | .interval => underI fun r => c.apply G (p.cod + 1) [] (.i r)
      | _ => under fun u => c.apply G (p.cod + 1) [] u
    pure (.pi x i (← rb a) b)
  | .sigma x a c => pure (.sigma x (← rb a) (← under fun u => c.apply G (p.cod + 1) [] u))
  | .pair u w => pure (.pair (← rb u) (← rb w))
  | .fst t => pure (.fst (← rb t))
  | .snd t => pure (.snd (← rb t))
  | .pathP a x y => rbArgs (.prim "PathP") [a, x, y]
  | .transp a r u => pure (.transp (← rb a) (← rbI r) (← rb u))
  | .hcomp a sys u => pure (.hcomp false (← rb a) (← rbSys sys) (← rb u))
  | .glueTy a sys => pure (.glueTy (← rb a) (← rbSysFlat sys))
  | .glue tySys sys a => pure (.glue (← rbSysFlat tySys) (← rbSysFlat sys) (← rb a))
  | .unglue b sys => pure (.unglue (← rb b) (← rbSysFlat sys))
  | .hcompU a sys => pure (.hcomp false .univ (← rbSys sys) (← rb a))
  | .glueU tySys us a => pure (.glueU (← rbSys tySys) (← rbSysFlat us) (← rb a))
  | .unglueU b sys => pure (.unglueU (← rb b) (← rbSys sys))
  | .prim n args => rbArgs (.prim n) args
  | .split P env cases x =>
    let cases' ← cases.mapM fun (c, names, body) => do
      let (v, p') := instCase G p.cod env c body
      pure (c, names, ← readback p' occ unfold v)
    pure (.split (← rb P) cases' (← rb x))

def quote (l : Nat) (v : Val) (unfold : Bool := false) : Tm :=
  match readback G (PRen.id l) none unfold v with
  | .ok t => t
  | .error e => panic! s!"quote: {e}"

/-- The normal form, with definitions unfolded. -/
def nf (env : Env) (t : Tm) : Tm :=
  quote G env.length (eval G env.length [] env t) true

end

end Kleenextt.Core
