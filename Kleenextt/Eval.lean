import Kleenextt.Syntax
import Kleenextt.Defun
import Kleenextt.Stats

/-! Cubical NbE in the style of cubicaltt, on de Bruijn levels.

Interval variables share the level space with ordinary variables. A value
lives in a context of some size `L`, mentions only levels below `L`, and may
be used in any larger context. Semantic interval binders (`line`) are
written at their use sites as closures derived by `Defun.lean`, which give
the line its body, computed at most once at a fresh variable, and its
support, from the captured values. Interval substitution (`act`) is
skipped outside the support and otherwise deferred (`sub`), as in cctt:
exposing the head of a value (`whnf`) pushes a pending substitution one
layer, re-running the computation rules on a neutral head, since
substitution can unblock them, and deferring the children.

Every semantic operation takes the current context size `L`, which is the
fresh-level supply. -/

namespace Kleenextt

/-- A system: components indexed by maximal, incomparable faces. A component
under face `α` does not mention the levels `α` fixes. -/
abbrev System (α : Type) := List (Face × α)

/-- Build a system from components, keeping only the maximal faces; the
first component for a face wins (overlapping components agree by typing). -/
def mkSystem (entries : System α) : System α :=
  (maximalFaces (entries.map (·.1))).filterMap fun α => entries.find? (·.1 == α)

/-- The cofibration a system covers. -/
def System.cof (sys : System α) : IExpr :=
  sys.foldr (fun (α, _) acc => .join α.toIExpr acc) .zero

def System.total? (sys : System α) : Option α :=
  (sys.find? (·.1.isEmpty)).map (·.2)

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
  σ.foldl (fun acc (l, _) => acc ||| 1 <<< l) 0

end Subst

def Face.toSubst (α : Face) : Subst :=
  α.map fun (l, d) => (l, .ofBool d)

/-! ## Support

The levels a value may mention as interval variables, as a bitmask; derived
over the captures of a line's closure. -/

class Vars (α : Type) where
  vars : α → Nat

def levelSet (ls : List Nat) : Nat :=
  ls.foldl (· ||| 1 <<< ·) 0

def clearLevel (vs l : Nat) : Nat :=
  if vs.testBit l then vs - (1 <<< l) else vs

/-- The levels a value with support `vs` may mention after `σ`. -/
def Subst.varsUnder (σ : Subst) (vs : Nat) : Nat :=
  σ.foldl (init := σ.foldl (fun acc (l, _) => clearLevel acc l) vs) fun acc (l, r) =>
    if vs.testBit l then acc ||| levelSet r.vars else acc

/-- For terms, names, indices, and context sizes. -/
abbrev Vars.none : Vars α := ⟨fun _ => 0⟩

instance : Vars IExpr := ⟨fun r => levelSet r.vars⟩
instance : Vars Face := ⟨fun α => levelSet (α.map (·.1))⟩
instance [Vars α] [Vars β] : Vars (α × β) := ⟨fun (a, b) => Vars.vars a ||| Vars.vars b⟩
instance [Vars α] : Vars (List α) := ⟨fun xs => xs.foldl (· ||| Vars.vars ·) 0⟩
instance : Vars Tm := .none
instance : Vars String := .none
instance : Vars Nat := .none
instance : Vars Icit := .none

/-! ## Templates

Closed object-level definitions the computation rules unfold. -/

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

/-- Primitives defined by unfolding: arity and closed definition. -/
private def primDef : String → Option (Nat × Tm)
  | "isContr" => some (1, isContrTm)
  | "fiber" => some (4, fiberTm)
  | "isEquiv" => some (3, isEquivTm)
  | "Equiv" => some (2, equivTm)
  | _ => none

/-- A constructor of a user-declared inductive type: a telescope of fields
(each type in the context of the previous fields, closed otherwise), then
interval binders, then a boundary system over the interval binders whose
terms live in the context of the fields and interval binders. -/
structure ConInfo where
  name : String
  fields : List (String × Tm)
  ivars : List String
  boundary : List (IExpr × Tm)

def ConInfo.arity (c : ConInfo) : Nat :=
  c.fields.length + c.ivars.length

/-- A parameterless inductive type; a HIT if some constructor binds
interval variables. Values of the type are `prim` applications of its
constructors, plus `hcomp`s for HITs. -/
structure DataInfo where
  name : String
  cons : List ConInfo

def DataInfo.hit (d : DataInfo) : Bool :=
  d.cons.any (!·.ivars.isEmpty)

/-! ## The domain and the computation rules -/

defun Line (L : Nat) (i : IExpr) : Val
  deriving vars : Nat folding (· ||| ·) 0 via Vars.vars := Val.vars
in

mutual
  inductive Val where
    | var (l : Nat)
    | flex (m : Nat) (sp : List (Val × Icit))
    | lam (x : String) (i : Icit) (c : Closure)
    | ilam (x : String) (c : Closure)
    /-- A semantic line: its body at a fresh variable of level `l`, computed
    at most once, which instantiation substitutes into and substitution
    renames, and its support, from the derived closure it was built from. -/
    | line (l : Nat) (body : Thunk Val) (vars : Nat)
    /-- A deferred substitution, `σ` on `v` in context `L`, with its
    support; `head` pushes it one layer, computed at most once. -/
    | sub (L : Nat) (σ : Subst) (v : Val) (vars : Nat) (head : Thunk Val)
    /-- A deferred computation with its support. -/
    | lazy (vars : Nat) (body : Thunk Val)
    /-- A value with its support, so that the support of a compound value
    is found without walking it. -/
    | cached (vars : Nat) (v : Val)
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
    /-- `hcomp Type [φ ↦ E] A`: a type former of its own, with elements
    `glueU`, so that transport along it never builds an equivalence. -/
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

/-- Metavariables (numbered densely in creation order), the declared
inductive types, and the top-level definitions. -/
structure Globals where
  metas : Array MetaEntry := #[]
  datas : List DataInfo := []
  /-- Top-level definitions: name, value, type. Closed values, kept out of
  environments so that substitution never traverses them, and computed only
  when first referenced. -/
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

/-- Expose the head: push deferred substitutions and force deferred
computations. -/
partial def Val.whnf : Val → Val
  | .sub _ _ _ _ head => head.get.whnf
  | .lazy _ body => body.get.whnf
  | .cached _ v => v.whnf
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
  | .sub .. | .lazy .. | .cached .. => "unforced"

/-- Substitute in a system: a face `α` becomes the faces on which `σ`
makes `α`'s equations hold, with the component under each. -/
def System.act (actVal : Nat → Subst → Val → Val) (L : Nat) (σ : Subst) (sys : System Val) : System Val :=
  mkSystem <| sys.flatMap fun (α, u) =>
    let β : Face := α.filter fun (l, _) => (σ.get l).isNone
    let ψ := β.apply <| α.foldr (init := .one) fun (l, d) acc =>
      match σ.get l with
      | some r => .meet (if d then r else .neg r) acc
      | none => acc
    (invFormula ψ true).filterMap fun δ =>
      (δ.meet β).map fun key => (key, actVal L (σ.under key) u)

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
  /-- The levels a value may mention as interval variables; lines and
  deferred values answer from their cached support. -/
  partial def Val.vars (v : Val) : Nat :=
    let go := Val.vars
    let goI (r : IExpr) : Nat := levelSet r.vars
    let goClo : Closure → Nat
      | .mk env _ => env.foldl (· ||| go ·) 0
    let goSys (sys : System Val) : Nat := sys.foldl (fun acc (α, u) => acc ||| Vars.vars α ||| go u) 0
    match v with
    | .var _ | .univ | .interval => 0
    | .flex _ sp => sp.foldl (· ||| go ·.1) 0
    | .lam _ _ c | .ilam _ c => goClo c
    | .line _ _ vs | .sub _ _ _ vs _ | .lazy vs _ | .cached vs _ => vs
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

  partial def Closure.apply (L : Nat) : Closure → Val → Val
    | .mk env t, u => eval L (u :: env) t

  /-- Apply a value of line type `(i : I) → A` to an interval expression. -/
  partial def lineApp (L : Nat) (f : Val) (r : IExpr) : Val :=
    match f.whnf with
    | .ilam _ c => c.apply L (.i r)
    | .lam _ _ c => c.apply L (.i r)
    | .line l body _ => tick .insts <| act L [(l, r)] body.get
    | f => vApp L f (.i r) .expl

  partial def vApp (L : Nat) (t u : Val) (i : Icit) : Val :=
    match t.whnf with
    | .lam _ _ c => c.apply L u
    | .ilam _ c => c.apply L u
    | t@(.line ..) =>
      match u.whnf with
      | .i r => lineApp L t r
      | _ => panic! "vApp: line applied to a non-interval"
    | .flex m sp => .flex m ((u, i) :: sp)
    | .transp a r f => transpApp L a r f u i
    | .hcomp a sys f => hcompApp L a sys f u i
    | .prim n args => prim' L n (args ++ [u])
    | t => cache (.app t u i)

  partial def vAppSp (L : Nat) (t : Val) : Spine → Val
    | [] => t
    | (u, i) :: sp => vApp L (vAppSp L t sp) u i

  partial def vFst (t : Val) : Val :=
    match t.whnf with
    | .pair u _ => u
    | t => cache (.fst t)

  partial def vSnd (t : Val) : Val :=
    match t.whnf with
    | .pair _ w => w
    | t => cache (.snd t)

  partial def papp' (L : Nat) (p : Val) (r : IExpr) (x y : Val) : Val :=
    if r.isZero then x
    else if r.isOne then y
    else match p.whnf with
    | .ilam _ c => c.apply L (.i r)
    | .lam _ _ c => c.apply L (.i r)
    | .line .. => lineApp L p r
    | .flex m sp => .flex m ((.i r, .expl) :: sp)
    | p => cache (.papp p r x y)

  partial def vMeta (m : Nat) : Val :=
    match G.lookupMeta m with
    | .solved v => v
    | .unsolved => .flex m []

  /-- Apply a meta to the bound variables of the environment it was created in. -/
  partial def vAppBDs (L : Nat) (env : Env) (v : Val) (bds : List BD) : Val :=
    match env, bds with
    | [], [] => v
    | t :: env, .bound :: bds => vApp L (vAppBDs L env v bds) t .expl
    | _ :: env, .defined :: bds => vAppBDs L env v bds
    | _, _ => panic! "vAppBDs: environment and binder list disagree"

  partial def eval (L : Nat) (env : Env) : Tm → Val
    | .var i => env.getD i default
    | .lam x i t => cache (.lam x i (.mk env t))
    | .ilam x t => cache (.ilam x (.mk env t))
    | .app t u i => vApp L (eval L env t) (eval L env u) i
    | .univ => .univ
    | .pi x i a b => cache (.pi x i (eval L env a) (.mk env b))
    | .sigma x a b => cache (.sigma x (eval L env a) (.mk env b))
    | .pair t u => cache (.pair (eval L env t) (eval L env u))
    | .fst t => vFst (eval L env t)
    | .snd t => vSnd (eval L env t)
    | .letE _ _ t u => eval L (eval L env t :: env) u
    | .mvar m => vMeta m
    | .insertedMeta m bds => vAppBDs L env (vMeta m) bds
    | .interval => .interval
    | .i r => .i (evalI env r)
    | .papp p r x y => papp' L (eval L env p) (evalI env r) (eval L env x) (eval L env y)
    | .transp a r u => transp' L (eval L env a) (evalI env r) (eval L env u)
    | .hcomp g a sys u =>
      let comp := if g then ghcomp' else hcomp'
      comp L (eval L env a) (evalSys L env sys) (eval L env u)
    | .hfill a sys u r => lineApp L (hfill' L (eval L env a) (evalSys L env sys) (eval L env u)) (evalI env r)
    | .comp a sys u => comp' L (.ilam "i" (.mk env a)) (evalSys L env sys) (eval L env u) false
    | .glueTy a sys => glueTy' (eval L env a) (evalSysFlat L env sys)
    | .glue tySys sys a => glue' (evalSysFlat L env tySys) (evalSysFlat L env sys) (eval L env a)
    | .unglue b sys => unglue' L (eval L env b) (evalSysFlat L env sys)
    | .glueU tySys us a => glueU' (evalSys L env tySys) (evalSysFlat L env us) (eval L env a)
    | .unglueU b sys => unglueU' L (eval L env b) (evalSys L env sys)
    | .prim n => prim' L n []
    | .top n =>
      match G.def? n with
      | some (v, _) => v.get
      | none => panic! s!"eval: unknown definition {n}"
    | .split P cases x => splitApp L (eval L env P) env cases (eval L env x)

  /-- Evaluate a system whose components bind an interval variable, giving
  components of line type, each in the environment restricted to its face. -/
  partial def evalSys (L : Nat) (env : Env) (sys : List (IExpr × Tm)) : System Val :=
    mkSystem <| sys.flatMap fun (φ, t) =>
      (invFormula (evalI env φ) true).map fun δ =>
        (δ, .ilam "j" (.mk (env.map (act L δ.toSubst)) t))

  partial def evalSysFlat (L : Nat) (env : Env) (sys : List (IExpr × Tm)) : System Val :=
    mkSystem <| sys.flatMap fun (φ, t) =>
      (invFormula (evalI env φ) true).map fun δ =>
        (δ, eval L (env.map (act L δ.toSubst)) t)

  /-- Interval substitution. `L` is the size of the target context. A value
  outside the support of `σ` is returned as is; interval values and lines
  are substituted at once, cheaply; anything else is deferred, composing
  with a substitution already pending. -/
  partial def act (L : Nat) (σ : Subst) (v : Val) : Val :=
    tick .act <|
    match v with
    | .i r => .i (σ.apply r)
    | .sub L' τ w _ _ => act (max L L') (σ.comp τ) w
    | v =>
      let vs := v.vars
      if vs &&& σ.domain == 0 then v else
      match v with
      | .line l body _ =>
        .line L (Thunk.mk fun _ => act (L + 1) ((l, .var L) :: σ) body.get) (σ.varsUnder vs)
      | v => tick .subs <| .sub L σ v (σ.varsUnder vs) (Thunk.mk fun _ => push L σ v)

  /-- One layer of a substitution known to touch `v`: the children are
  substituted lazily and the computation rules re-run on a neutral head. -/
  partial def push (L : Nat) (σ : Subst) (v : Val) : Val :=
    let actClo : Closure → Closure
      | .mk env t => .mk (env.map (act L σ)) t
    tick .actNodes <|
    match v with
    | .var l => .var l
    | .flex m sp => .flex m (sp.map fun (u, i) => (act L σ u, i))
    | .lam x i c => .lam x i (actClo c)
    | .ilam x c => .ilam x (actClo c)
    | .line .. | .sub .. => act L σ v
    | .lazy _ body => act L σ body.get
    | .cached _ v => push L σ v
    | .app t u i => vApp L (act L σ t) (act L σ u) i
    | .papp p r x y => papp' L (act L σ p) (σ.apply r) (act L σ x) (act L σ y)
    | .univ => .univ
    | .interval => .interval
    | .i r => .i (σ.apply r)
    | .pi x i a c => .pi x i (act L σ a) (actClo c)
    | .sigma x a c => .sigma x (act L σ a) (actClo c)
    | .pair u w => .pair (act L σ u) (act L σ w)
    | .fst t => vFst (act L σ t)
    | .snd t => vSnd (act L σ t)
    | .pathP a x y => .pathP (act L σ a) (act L σ x) (act L σ y)
    | .transp a r u => transp' L (act L σ a) (σ.apply r) (act L σ u)
    | .hcomp a sys u => hcomp' L (act L σ a) (actSys L σ sys) (act L σ u)
    | .glueTy a sys => glueTy' (act L σ a) (actSys L σ sys)
    | .glue tySys sys a => glue' (actSys L σ tySys) (actSys L σ sys) (act L σ a)
    | .unglue b sys => unglue' L (act L σ b) (actSys L σ sys)
    | .hcompU a sys => hcompU' L (act L σ a) (actSys L σ sys)
    | .glueU tySys us a => glueU' (actSys L σ tySys) (actSys L σ us) (act L σ a)
    | .unglueU b sys => unglueU' L (act L σ b) (actSys L σ sys)
    | .prim n args => prim' L n (args.map (act L σ))
    | .split P env cases x => splitApp L (act L σ P) (env.map (act L σ)) cases (act L σ x)

  partial def actSys (L : Nat) (σ : Subst) (sys : System Val) : System Val :=
    System.act act L σ sys

  partial def face (L : Nat) (α : Face) (v : Val) : Val :=
    act L α.toSubst v

  partial def faceSys (L : Nat) (α : Face) (sys : System Val) : System Val :=
    actSys L α.toSubst sys

  /-- A line in context `L` from its closure: the body memoised at the
  fresh level `L`, the support from the captures. -/
  partial def mkLine (L : Nat) (c : Line) : Val :=
    tick .lines <| .line L (Thunk.mk fun _ => tick .bodies <| gauge .maxLevel (L + 1) <| c.apply (L + 1) (.var L)) (Line.vars c)
  /-- A line in context `L` from a body mentioning the fresh level `L`. -/
  partial def mkBind (L : Nat) (body : Val) : Val :=
    .line L (Thunk.pure body) (clearLevel body.vars L)

  /-- A deferred computation from a closure ignoring its interval argument,
  with the support of the captures: for a component that a total face may
  discard. -/
  partial def mkLazy (L : Nat) (c : Line) : Val :=
    tick .lazies <| .lazy (Line.vars c) (Thunk.mk fun _ => tick .lazyBodies <| c.apply L .zero)

  /-- Record the support of a newly built compound value. -/
  partial def cache (v : Val) : Val :=
    tick .cacheds <| .cached v.vars v

  partial def lazyFst (L : Nat) (v : Val) : Val :=
    mkLazy L (closure% fun _ _ => vFst v)

  partial def lazySnd (L : Nat) (v : Val) : Val :=
    mkLazy L (closure% fun _ _ => vSnd v)

  partial def constLine (L : Nat) (v : Val) : Val :=
    mkLine L (closure% fun _ _ => v)

  /-- The reversed line `j ↦ s (¬ j)`. -/
  partial def revLine (L : Nat) (s : Val) : Val :=
    mkLine L (closure% fun L1 j => lineApp L1 s (.neg j))

  partial def prim' (L : Nat) (name : String) (args : List Val) : Val :=
    match name, args with
    | "I", [] => .interval
    | "PathP", [a, x, y] => cache (.pathP a x y)
    | "Path", [a, x, y] => cache (.pathP (.ilam "_" (.mk [a] (.var 1))) x y)
    | _, _ =>
      match G.con? name with
      | some (_, con) =>
        -- A saturated higher constructor reduces to its boundary on a face that holds.
        if args.length == con.arity then
          let env := args.reverse
          match con.boundary.find? (fun (φ, _) => (evalI env φ).isOne) with
          | some (_, e) => eval L env e
          | none => cache (.prim name args)
        else .prim name args
      | none =>
        match primDef name with
        | some (arity, body) =>
          if args.length == arity then args.foldl (fun f a => vApp L f a .expl) (eval L [] body)
          else .prim name args
        | none => cache (.prim name args)

  /-- Dependent case analysis: reduces on a saturated constructor and, for a
  HIT, on an `hcomp` (the CHM rule, composing over the filler). -/
  partial def splitApp (L : Nat) (P : Val) (env : Env) (cases : List (String × List String × Tm)) (x : Val) : Val :=
    match x.whnf with
    | .prim c args =>
      match cases.find? (·.1 == c), G.con? c with
      | some (_, _, body), some (_, con) =>
        if args.length == con.arity then eval L (args.reverse ++ env) body
        else .split P env cases x
      | _, _ => cache (.split P env cases x)
    | .hcomp (.prim D []) sys u =>
      match G.data? D with
      | some d =>
        if d.hit then
          tick .splitHcomp <|
          let fill := hfill' L (.prim D []) sys u
          let pline := mkLine L (closure% fun L1 j => vApp L1 P (lineApp L1 fill j) .expl)
          let sides := sys.map fun (α, s) =>
            (α, mkLine L (closure% fun L1 j =>
              splitApp L1 (face L1 α P) (env.map (face L1 α)) cases (lineApp L1 s j)))
          comp' L pline (mkSystem sides) (splitApp L P env cases u) false
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

  /-- `hcomp` at a strict inductive type: constructor-wise, along the field
  telescope, when the base and every side are the same constructor. -/
  partial def hcompData (L : Nat) (A : Val) (sys : System Val) (u : Val) : Val :=
    match u.whnf with
    | .prim c args =>
      match G.con? c with
      | some (_, con) =>
        let sameCon := sys.all fun (_, s) =>
          match (lineApp (L + 1) s (.var L)).whnf with
          | .prim c' args' => c' == c && args'.length == args.length
          | _ => false
        if args.length != con.fields.length || !sameCon then .hcomp A sys u
        else cache (.prim c (hcompFields L 0 con.fields [] sys args))
      | none => cache (.hcomp A sys u)
    | _ => cache (.hcomp A sys u)

  /-- The fields of a constructor-wise `hcomp`; `fills` are the fillers of
  the previous fields, most recent first, which the next field's type may
  depend on. -/
  partial def hcompFields (L : Nat) (k : Nat) (fields : List (String × Tm)) (fills : List Val)
      (sys : System Val) (args : List Val) : List Val :=
    match fields with
    | [] => []
    | (_, T) :: rest =>
      let tline := mkLine L (closure% fun L1 j => eval L1 (fills.map fun f => lineApp L1 f j) T)
      let sysk := sys.map fun (α, s) => (α, mkLine L (closure% fun L1 j =>
        match (lineApp L1 s j).whnf with
        | .prim _ as => as.getD k default
        | _ => panic! "hcomp: side is not a constructor"))
      let uk := args.getD k default
      let vk := mkLazy L (closure% fun L1 _ => comp' L1 tline sysk uk false)
      let fk := compFill' L tline sysk uk
      vk :: hcompFields L (k + 1) rest (fk :: fills) sys args

  /-- The filler of a heterogeneous composition, as a line. -/
  partial def compFill' (L : Nat) (a : Val) (sys : System Val) (u0 : Val) : Val :=
    mkLine L (closure% fun L1 j =>
      let sides := sys.map fun (α, s) => (α, mkLine L1 (closure% fun L2 k => lineApp L2 s (.meet j k)))
      let start := (invFormula (.neg j) true).map fun δ => (δ, mkLine L1 (closure% fun L2 _ => face L2 δ u0))
      comp' L1 (mkLine L1 (closure% fun L2 k => lineApp L2 a (.meet j k))) (mkSystem (sides ++ start)) u0 false)

  /-- The components of a line of path types at a point. -/
  partial def pathPAt (L : Nat) (a : Val) (i : IExpr) : Val × Val × Val :=
    match (lineApp L a i).whnf with
    | .pathP A x y => (A, x, y)
    | _ => panic! "transp: line is not constantly a path type"

  /-- `transp^i A r u`, with `A` a line; identity when `r = 1`. -/
  partial def transp' (L : Nat) (a : Val) (r : IExpr) (u : Val) : Val :=
    if r.isOne then u else
    tick .transp <|
    match (lineApp (L + 1) a (.var L)).whnf with
    | .pi .. => tick .transpStuck <| cache (.transp a r u)
    | .sigma .. =>
      tick .transpSigma <|
      let aline := mkLine L (closure% fun L1 i =>
        match (lineApp L1 a i).whnf with
        | .sigma _ A _ => A
        | _ => panic! "transp: line is not constantly a pair type")
      let v1 := mkLazy L (closure% fun L1 _ => transp' L1 aline r (vFst u))
      let fill := transpFill L aline r (vFst u)
      let bline := mkLine L (closure% fun L1 i =>
        match (lineApp L1 a i).whnf with
        | .sigma _ _ c => c.apply L1 (lineApp L1 fill i)
        | _ => panic! "transp: line is not constantly a pair type")
      .pair v1 (mkLazy L (closure% fun L1 _ => transp' L1 bline r (vSnd u)))
    | .pathP .. =>
      tick .transpPath <|
      let (_, x0, y0) := pathPAt L a .zero
      mkLine L (closure% fun L1 k =>
        let aline := mkLine L1 (closure% fun L2 i => lineApp L2 (pathPAt L2 a i).1 k)
        let base := papp' L1 u k x0 y0
        let sides := (invFormula r true).map (fun δ => (δ, mkLine L1 (closure% fun L2 _ => face L2 δ base)))
          ++ (invFormula (.neg k) true).map (fun δ =>
            (δ, mkLine L1 (closure% fun L2 i => face L2 δ (pathPAt L2 a i).2.1)))
          ++ (invFormula k true).map (fun δ =>
            (δ, mkLine L1 (closure% fun L2 i => face L2 δ (pathPAt L2 a i).2.2)))
        comp' L1 aline (mkSystem sides) base false)
    | .univ => u
    | .prim n [] => if (G.data? n).isSome then u else .transp a r u
    | .glueTy A sysG => transpGlue L r u A sysG
    | .hcompU A sysE => transpHU L r u A sysE
    | w =>
      let neutral : Val → Bool
        | .var .. | .app .. | .flex .. | .papp .. => true
        | _ => false
      match w with
      | .split _ _ _ x =>
        if neutral x.whnf then tick .transpStuck <| cache (.transp a r u)
        else panic! s!"transp stuck at L={L} on type {w.headStr 4}, element {u.headStr 2}"
      | w =>
        if neutral w then tick .transpStuck <| cache (.transp a r u)
        else panic! s!"transp stuck at L={L} on type {w.headStr 4}, element {u.headStr 2}"

  /-- The codomain of a line of function types at a point, at an argument. -/
  partial def piCod (L : Nat) (a : Val) (i : IExpr) (x : Val) : Val :=
    match (lineApp L a i).whnf with
    | .pi _ _ _ c => c.apply L x
    | _ => panic! "transp: line is not constantly a function type"

  /-- `transp` at a function type, applied: `(transp^i ((x : A) → B) r f) v`. -/
  partial def transpApp (L : Nat) (a : Val) (r : IExpr) (f u : Val) (i : Icit) : Val :=
    match (lineApp (L + 1) a (.var L)).whnf with
    | .pi _ _ .interval _ =>
      transp' L (mkLine L (closure% fun L1 i' => piCod L1 a i' u)) r (vApp L f u i)
    | .pi .. =>
      let domNeg := mkLine L (closure% fun L1 i' =>
        match (lineApp L1 a (.neg i')).whnf with
        | .pi _ _ dom _ => dom
        | _ => panic! "transp: line is not constantly a function type")
      let w := transpFill L domNeg r u
      let vline := revLine L w
      let v0 := lineApp L vline .zero
      transp' L (mkLine L (closure% fun L1 i' => piCod L1 a i' (lineApp L1 vline i'))) r (vApp L f v0 i)
    | _ => cache (.app (cache (.transp a r f)) u i)

  /-- The filler `Transp^i A r u`: a line from `u` to `transp^i A r u`. -/
  partial def transpFill (L : Nat) (a : Val) (r : IExpr) (u : Val) : Val :=
    mkLine L (closure% fun L1 i =>
      transp' L1 (mkLine L1 (closure% fun L2 k => lineApp L2 a (.meet i k))) (.join r (.neg i)) u)

  /-- Transport from `A r` to `A 1`; the identity when `r = 1`. -/
  partial def forward (L : Nat) (a : Val) (r : IExpr) (u : Val) : Val :=
    transp' L (mkLine L (closure% fun L1 i => lineApp L1 a (.join i r))) r u

  /-- Heterogeneous composition, derived: `comp^i A [φ ↦ u] u₀ =
  hcomp^i (A 1) [φ ↦ forward A i (u i)] (forward A 0 u₀)`, with `ghcomp`
  in place of `hcomp` when `general`. -/
  partial def comp' (L : Nat) (a : Val) (sys : System Val) (u0 : Val) (general : Bool) : Val :=
    let sides := sys.map fun (α, s) =>
      (α, mkLine L (closure% fun L1 i => forward L1 (face L1 α a) i (lineApp L1 s i)))
    let base := forward L a .zero u0
    if general then ghcomp' L (lineApp L a .one) (mkSystem sides) base
    else hcomp' L (lineApp L a .one) (mkSystem sides) base

  /-- `ghcomp A [φ ↦ u] u₀ = hcomp A [φ ↦ u, ¬φ ↦ u₀] u₀`. -/
  partial def ghcomp' (L : Nat) (A : Val) (sys : System Val) (u : Val) : Val :=
    let extra := (invFormula sys.cof false).map fun β => (β, mkLine L (closure% fun L1 _ => face L1 β u))
    hcomp' L A (mkSystem (sys ++ extra)) u

  partial def hfill' (L : Nat) (A : Val) (sys : System Val) (u : Val) : Val :=
    mkLine L (closure% fun L1 j =>
      let sides := sys.map fun (α, s) => (α, mkLine L1 (closure% fun L2 k => lineApp L2 s (.meet j k)))
      let start := (invFormula (.neg j) true).map fun δ => (δ, mkLine L1 (closure% fun L2 _ => face L2 δ u))
      hcomp' L1 A (mkSystem (sides ++ start)) u)

  /-- The filler of `ghcomp`: `hfill` with the `¬φ ↦ u` sides. -/
  partial def ghfill' (L : Nat) (A : Val) (sys : System Val) (u : Val) : Val :=
    let extra := (invFormula sys.cof false).map fun β => (β, mkLine L (closure% fun L1 _ => face L1 β u))
    hfill' L A (mkSystem (sys ++ extra)) u

  partial def hcomp' (L : Nat) (A : Val) (sys : System Val) (u : Val) : Val :=
    match sys.total? with
    | some s => lineApp L s .one
    | none =>
    tick .hcomp <|
    let A := A.whnf
    match A with
    | .pi .. => tick .hcompStuck <| cache (.hcomp A sys u)
    | .sigma _ a c =>
      tick .hcompSigma <|
      let sys1 := sys.map fun (α, s) => (α, mkLine L (closure% fun L1 j => vFst (lineApp L1 s j)))
      let sys2 := sys.map fun (α, s) => (α, mkLine L (closure% fun L1 j => vSnd (lineApp L1 s j)))
      let u1 := vFst u
      let v1 := mkLazy L (closure% fun L1 _ => hcomp' L1 a sys1 u1)
      let fill1 := hfill' L a sys1 u1
      let bline := mkLine L (closure% fun L1 j => c.apply L1 (lineApp L1 fill1 j))
      .pair v1 (mkLazy L (closure% fun L1 _ => comp' L1 bline sys2 (vSnd u) false))
    | .pathP a x y =>
      tick .hcompPath <|
      mkLine L (closure% fun L1 k =>
        let sides := sys.map (fun (α, s) =>
            (α, mkLine L1 (closure% fun L2 j => papp' L2 (lineApp L2 s j) k (face L2 α x) (face L2 α y))))
          ++ (invFormula (.neg k) true).map (fun δ => (δ, mkLine L1 (closure% fun L2 _ => face L2 δ x)))
          ++ (invFormula k true).map (fun δ => (δ, mkLine L1 (closure% fun L2 _ => face L2 δ y)))
        hcomp' L1 (lineApp L1 a k) (mkSystem sides) (papp' L1 u k x y))
    | .univ => tick .hcompU <| hcompU' L u sys
    | .glueTy B sysG => tick .hcompGlue <| hcompGlue L B sysG sys u
    | .hcompU B sysE => tick .hcompHU <| hcompHU L B sysE sys u
    | .prim n [] =>
      match G.data? n with
      | some d => if d.hit then tick .hcompHIT <| .hcomp A sys u else tick .hcompData <| hcompData L A sys u
      | none => tick .hcompStuck <| cache (.hcomp A sys u)
    | _ => tick .hcompStuck <| cache (.hcomp A sys u)

  /-- `hcomp` at a function type, applied. -/
  partial def hcompApp (L : Nat) (A : Val) (sys : System Val) (f u : Val) (i : Icit) : Val :=
    match A.whnf with
    | .pi _ _ _ c =>
      let sides := sys.map fun (α, s) =>
        (α, mkLine L (closure% fun L1 j => vApp L1 (lineApp L1 s j) (face L1 α u) i))
      hcomp' L (c.apply L u) (mkSystem sides) (vApp L f u i)
    | _ => cache (.app (cache (.hcomp A sys f)) u i)

  -- Composition in the universe: `hcomp Type [φ ↦ E] A` is a type former
  -- (cubicaltt's `VCompU`). Its elements are `glueU [φ ↦ E] [φ ↦ t] a` with
  -- `a : A` and `t : E 1` such that `a` is the transport of `t` backwards
  -- along `E`; that transport is the implicit equivalence `E 1 → A`, and
  -- `lemEq` provides the contractibility of its fibers semantically.

  partial def hcompU' (L : Nat) (A : Val) (sys : System Val) : Val :=
    match sys.total? with
    | some E => lineApp L E .one
    | none => cache (.hcompU A sys)

  partial def glueU' (tySys us : System Val) (a : Val) : Val :=
    match us.total? with
    | some t => t
    | none => cache (.glueU tySys us a)

  /-- Transport backwards along a line of types, `E 1 → E 0`. -/
  partial def eqFun (L : Nat) (E t : Val) : Val :=
    transp' L (revLine L E) .zero t

  partial def unglueU' (L : Nat) (b : Val) (sys : System Val) : Val :=
    match sys.total? with
    | some E => eqFun L E b
    | none =>
      match b.whnf with
      | .glueU _ _ a => a
      | .prim .. | .pair .. =>
        panic! s!"unglueU of {b.headStr 2} at {(Val.hcompU .univ sys).headStr}"
      | b => cache (.unglueU b sys)

  /-- `hcomp` at a composition in the universe: as at `Glue`, with the
  backward transport as the equivalence. A face's component is restricted
  to its face like the element it is applied to: off the face its type
  need not reduce, and an element built there is passed through unchanged
  by the rules that later see the type restricted. -/
  partial def hcompHU (L : Nat) (A : Val) (sysE sys : System Val) (u : Val) : Val :=
    let comps := sysE.map fun (γ, E) =>
      let E := face L γ E
      let T := lineApp L E .one
      let sysγ := faceSys L γ sys
      let uγ := face L γ u
      (γ, E, mkLazy L (closure% fun L1 _ => hcomp' L1 T sysγ uγ), hfill' L T sysγ uγ)
    let sidesA := sys.map (fun (α, s) =>
        (α, mkLine L (closure% fun L1 j => unglueU' L1 (lineApp L1 s j) (faceSys L1 α sysE))))
      ++ comps.map (fun (γ, E, _, fill) =>
        (γ, mkLine L (closure% fun L1 j => eqFun L1 E (lineApp L1 fill j))))
    let a := mkLazy L (closure% fun L1 _ => hcomp' L1 A (mkSystem sidesA) (unglueU' L1 u sysE))
    glueU' sysE (comps.map fun (γ, _, t, _) => (γ, t)) a

  /-- The filler of the backward transport: a line from `eqFun E u` (at 0)
  to `u` (at 1). -/
  partial def transpFillNeg (L : Nat) (E u : Val) : Val :=
    revLine L (transpFill L (revLine L E) .zero u)

  /-- Per face of `lemEq`, at `i`: the composite along `j` from `p i` up to
  `E 1`, and its filler. -/
  partial def lemEqItem (L : Nat) (E b : Val) (i : IExpr) (α : Face) (ap : Val) : Val × Val :=
    let aa := vFst ap
    let pa := vSnd ap
    let Eα := face L α E
    let bα := face L α b
    let base := papp' L pa i bα (eqFun L Eα aa)
    let sides := mkSystem <|
      (invFormula (.neg i) true).map (fun δ => (δ, transpFill L (face L δ Eα) .zero (face L δ bα)))
      ++ (invFormula i true).map (fun δ => (δ, transpFillNeg L (face L δ Eα) (face L δ aa)))
    (comp' L Eα sides base false, compFill' L Eα sides base)

  /-- cubicaltt's `lemEq`: given a line `E` with `b : E 0` and a partial
  fiber `[α ↦ (a, p)]` with `a : E 1` and `p : Path (E 0) b (eqFun E a)`,
  a total fiber `(a, p)` extending it. -/
  partial def lemEq (L : Nat) (E b : Val) (aps : System Val) : Val × Val :=
    tick .lemEq <|
    let ta := lineApp L E .one
    let p1s := mkSystem (aps.map fun (α, ap) =>
      (α, mkLine L (closure% fun L1 i => (lemEqItem L1 E b i α ap).1)))
    let tb := mkLazy L (closure% fun L1 _ => transp' L1 E .zero b)
    let a := mkLazy L (closure% fun L1 _ => ghcomp' L1 ta p1s tb)
    let p1 := ghfill' L ta p1s tb
    let p := mkLine L (closure% fun L1 i =>
      let sides := (invFormula (.neg i) true).map (fun δ =>
          (δ, revLine L1 (transpFill L1 (face L1 δ E) .zero (face L1 δ b))))
        ++ (invFormula i true).map (fun δ => (δ, revLine L1 (transpFillNeg L1 (face L1 δ E) (face L1 δ a))))
        ++ aps.map (fun (α, ap) => (α, revLine L1 (lemEqItem L1 E b i α ap).2))
      comp' L1 (revLine L1 E) (mkSystem sides) (lineApp L1 p1 i) false)
    (a, p)

  /-- Transport along a line of compositions in the universe: `transpGlue`
  with `eqFun` as the equivalence and `lemEq` for the fibers. `A` and
  `sysE` are the components peeked at `i = var L`, made lines again by
  binding `L`. -/
  partial def transpHU (L : Nat) (r : IExpr) (b0 A : Val) (sysE : System Val) : Val :=
    tick .transpHU <|
    let A1 := face L [(L, true)] A
    let sysE0 := faceSys L [(L, false)] sysE
    let sysE1 := faceSys L [(L, true)] sysE
    let Aline := mkBind L A
    let a0 := unglueU' L b0 sysE0
    let rFaces := invFormula r true
    let δs := sysE.filter fun (γ, _) => !γ.mentions L
    let tfills := δs.map fun (γ, E) =>
      let E := face L γ (mkBind L E)
      (γ, E, transpFill L (mkLine L (closure% fun L1 i' => lineApp L1 (lineApp L1 E i') .one)) (γ.apply r) (face L γ b0))
    let sidesA := rFaces.map (fun δ => (δ, mkLine L (closure% fun L1 _ => face L1 δ a0)))
      ++ tfills.map (fun (γ, E, tf) =>
        (γ, mkLine L (closure% fun L1 i' => eqFun L1 (lineApp L1 E i') (lineApp L1 tf i'))))
    let a1 := mkLazy L (closure% fun L1 _ => comp' L1 Aline (mkSystem sidesA) a0 true)
    let fibs := sysE1.map fun (γ1, E1) =>
      let E1 := face L γ1 E1
      let a1γ := face L γ1 a1
      let b0γ := face L γ1 b0
      let θ := (invFormula (γ1.apply r) true).map (fun δ =>
          (δ, Val.pair (face L δ b0γ) (constLine L (face L δ a1γ))))
        ++ tfills.filterMap (fun (γ, _, tf) => (γ.meet γ1).map fun key =>
          let key := key.minus γ1
          let t1' := mkLazy L (closure% fun L1 _ => face L1 key (face L1 γ1 (lineApp L1 tf .one)))
          (key, Val.pair t1' (constLine L (face L key a1γ))))
      let fib := mkLazy L (closure% fun L1 _ =>
        let (t1, α) := lemEq L1 E1 a1γ (mkSystem θ)
        Val.pair t1 α)
      (γ1, E1, lazyFst L fib, lazySnd L fib, a1γ)
    let sidesA1 := fibs.map (fun (γ1, E1, t1, α, a1γ) =>
        (γ1, mkLine L (closure% fun L1 i' => papp' L1 α i' a1γ (eqFun L1 E1 t1))))
      ++ rFaces.map (fun δ => (δ, mkLine L (closure% fun L1 _ => face L1 δ a1)))
    let a1' := mkLazy L (closure% fun L1 _ => ghcomp' L1 A1 (mkSystem sidesA1) a1)
    glueU' sysE1 (fibs.map fun (γ1, _, t1, _, _) => (γ1, t1)) a1'

  partial def hcompGlue (L : Nat) (B : Val) (sysG sys : System Val) (u : Val) : Val :=
    let comps := sysG.map fun (γ, Te) =>
      let Te := face L γ Te
      let T := vFst Te
      let f := vFst (vSnd Te)
      let sysγ := faceSys L γ sys
      let uγ := face L γ u
      (γ, f, mkLazy L (closure% fun L1 _ => hcomp' L1 T sysγ uγ), hfill' L T sysγ uγ)
    let sidesB := sys.map (fun (α, s) =>
        (α, mkLine L (closure% fun L1 j => unglue' L1 (lineApp L1 s j) (faceSys L1 α sysG))))
      ++ comps.map (fun (γ, f, _, fill) =>
        (γ, mkLine L (closure% fun L1 j => vApp L1 f (lineApp L1 fill j) .expl)))
    let a := mkLazy L (closure% fun L1 _ => hcomp' L1 B (mkSystem sidesB) (unglue' L1 u sysG))
    glue' sysG (comps.map fun (γ, _, t, _) => (γ, t)) a

  /-- Extend a partial element of a contractible type to a total one:
  `ext (c, p) [θ ↦ v] = hcomp [θ ↦ p v j, ¬θ ↦ c] c`. -/
  partial def ext (L : Nat) (X contr : Val) (θ : System Val) : Val :=
    let c := vFst contr
    let p := vSnd contr
    let sides := θ.map (fun (α, w) =>
        (α, mkLine L (closure% fun L1 j => papp' L1 (vApp L1 (face L1 α p) w .expl) j (face L1 α c) w)))
      ++ (invFormula θ.cof false).map (fun β => (β, mkLine L (closure% fun L1 _ => face L1 β c)))
    hcomp' L X (mkSystem sides) c

  /-- `transp^i (Glue [φ ↦ (T, e)] A) r b₀`, after Cubical Agda / Huber:
  the `∀i.φ` correction is folded into a `ghcomp`-based composition in `A`,
  so no empty systems arise. `A` and `sysG` are the components peeked at
  `i = var L`, made lines again by binding `L`. Each face's component is
  restricted to its face, as in `hcompHU`. -/
  partial def transpGlue (L : Nat) (r : IExpr) (b0 A : Val) (sysG : System Val) : Val :=
    tick .transpGlue <|
    let A1 := face L [(L, true)] A
    let sysG0 := faceSys L [(L, false)] sysG
    let sysG1 := faceSys L [(L, true)] sysG
    let Aline := mkBind L A
    let a0 := unglue' L b0 sysG0
    let rFaces := invFormula r true
    let δs := sysG.filter fun (γ, _) => !γ.mentions L
    let tfills := δs.map fun (γ, Te) =>
      let Te := face L γ (mkBind L Te)
      (γ, Te, transpFill L (mkLine L (closure% fun L1 i' => vFst (lineApp L1 Te i'))) (γ.apply r) (face L γ b0))
    let sidesA := rFaces.map (fun δ => (δ, mkLine L (closure% fun L1 _ => face L1 δ a0)))
      ++ tfills.map (fun (γ, Te, tf) =>
        (γ, mkLine L (closure% fun L1 i' =>
          vApp L1 (vFst (vSnd (lineApp L1 Te i'))) (lineApp L1 tf i') .expl)))
    let a1 := mkLazy L (closure% fun L1 _ => comp' L1 Aline (mkSystem sidesA) a0 true)
    let fibs := sysG1.map fun (γ1, Te1) =>
      let Te1 := face L γ1 Te1
      let T1 := vFst Te1
      let e1 := vSnd Te1
      let f1 := vFst e1
      let a1γ := face L γ1 a1
      let b0γ := face L γ1 b0
      let A1γ := face L γ1 A1
      let θ := (invFormula (γ1.apply r) true).map (fun δ =>
          (δ, Val.pair (face L δ b0γ) (constLine L (face L δ a1γ))))
        ++ tfills.filterMap (fun (γ, _, tf) => (γ.meet γ1).map fun key =>
          let key := key.minus γ1
          let t1' := mkLazy L (closure% fun L1 _ => face L1 key (face L1 γ1 (lineApp L1 tf .one)))
          (key, Val.pair t1' (constLine L (face L key a1γ))))
      let fib := mkLazy L (closure% fun L1 _ =>
        let fibTy := prim' L1 "fiber" [T1, A1γ, f1, a1γ]
        let contr := vApp L1 (vSnd e1) a1γ .expl
        ext L1 fibTy contr (mkSystem θ))
      (γ1, lazyFst L fib, lazySnd L fib, f1, a1γ)
    let sidesA1 := fibs.map (fun (γ1, t1, α, f1, a1γ) =>
        (γ1, mkLine L (closure% fun L1 i' => papp' L1 α i' a1γ (vApp L1 f1 t1 .expl))))
      ++ rFaces.map (fun δ => (δ, mkLine L (closure% fun L1 _ => face L1 δ a1)))
    let a1' := mkLazy L (closure% fun L1 _ => ghcomp' L1 A1 (mkSystem sidesA1) a1)
    glue' sysG1 (fibs.map fun (γ1, t1, _, _, _) => (γ1, t1)) a1'

  partial def glueTy' (A : Val) (sys : System Val) : Val :=
    match sys.total? with
    | some Te => vFst Te
    | none => cache (.glueTy A sys)

  partial def glue' (tySys sys : System Val) (a : Val) : Val :=
    match sys.total? with
    | some t => t
    | none => cache (.glue tySys sys a)

  partial def unglue' (L : Nat) (b : Val) (sys : System Val) : Val :=
    match sys.total? with
    | some Te => vApp L (vFst (vSnd Te)) b .expl
    | none =>
      match b.whnf with
      | .glue _ _ a => a
      | b => cache (.unglue b sys)
end

end

end defun

section
variable (G : Globals)
include G

/-- Expose the head: deferred values, and solved metavariables. -/
partial def force (L : Nat) (v : Val) : Val :=
  match v.whnf with
  | .flex m sp =>
    match G.lookupMeta m with
    | .solved t => force L (vAppSp G L t sp)
    | .unsolved => .flex m sp
  | v => v

/-- A partial renaming from a context of size `dom` to one of size `cod`,
mapping levels of the codomain to levels of the domain. Quotation uses the
identity; unification uses the inverse of a metavariable's spine. -/
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

/-- Instantiate a case body with fresh variables for the constructor's
fields and interval binders, starting at level `l`; also the renaming
lifted over them. -/
def instCase (l : Nat) (env : Env) (c : String) (body : Tm) : Val × PRen :=
  let (nf, ni) := match G.con? c with
    | some (_, con) => (con.fields.length, con.ivars.length)
    | none => (0, 0)
  let args := (List.range nf).map (fun k => Val.var (l + k))
    ++ (List.range ni).map (fun k => Val.i (.var (l + nf + k)))
  let p := (List.range (nf + ni)).foldl (fun q _ => q.lift) (PRen.id l)
  (eval G (l + nf + ni) (args.reverse ++ env) body, p)

/-- Read a value back into core syntax under a partial renaming, failing on
a variable outside the renaming or on an occurrence of metavariable `occ`. -/
partial def readback (p : PRen) (occ : Option Nat) (v : Val) : Except String Tm := do
  let lvl (x : Nat) : Except String Nat :=
    match p.ren x with
    | some x' => pure (p.dom - x' - 1)
    | none => throw "unify: variable escapes its scope"
  let rbI (r : IExpr) : Except String IExpr := r.mapVarsM fun x => do pure (.var (← lvl x))
  let rbFace (α : Face) : Except String IExpr := rbI α.toIExpr
  let under (f : Val → Val) : Except String Tm := readback p.lift occ (f (.var p.cod))
  let underI (f : IExpr → Val) : Except String Tm := readback p.lift occ (f (.var p.cod))
  let rb := readback p occ
  let rbSys (sys : System Val) : Except String (List (IExpr × Tm)) :=
    sys.mapM fun (α, s) => do pure (← rbFace α, ← underI fun j => lineApp G (p.cod + 1) s j)
  let rbSysFlat (sys : System Val) : Except String (List (IExpr × Tm)) :=
    sys.mapM fun (α, t) => do pure (← rbFace α, ← rb t)
  let rbArgs (hd : Tm) (args : List Val) : Except String Tm :=
    args.foldlM (fun t u => do pure (.app t (← rb u) .expl)) hd
  match force G p.cod v with
  | .var x => pure (.var (← lvl x))
  | .flex m sp =>
    if occ == some m then throw "unify: occurs check"
    sp.reverse.foldlM (fun t (u, i) => do pure (.app t (← rb u) i)) (.mvar m)
  | .lam x i c => pure (.lam x i (← under fun u => c.apply G (p.cod + 1) u))
  | .ilam x c => pure (.ilam x (← underI fun r => c.apply G (p.cod + 1) (.i r)))
  | .line l body _ => pure (.ilam "i" (← underI fun r => act G (p.cod + 1) [(l, r)] body.get))
  | .sub .. | .lazy .. | .cached .. => panic! "readback: unforced value"
  | .app t u i => pure (.app (← rb t) (← rb u) i)
  | .papp q r x y => pure (.papp (← rb q) (← rbI r) (← rb x) (← rb y))
  | .univ => pure .univ
  | .interval => pure .interval
  | .i r => pure (.i (← rbI r))
  | .pi x i a c =>
    let b ← match a with
      | .interval => underI fun r => c.apply G (p.cod + 1) (.i r)
      | _ => under fun u => c.apply G (p.cod + 1) u
    pure (.pi x i (← rb a) b)
  | .sigma x a c => pure (.sigma x (← rb a) (← under fun u => c.apply G (p.cod + 1) u))
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
      pure (c, names, ← readback p' occ v)
    pure (.split (← rb P) cases' (← rb x))

/-- Read a value back into core syntax; `l` is the current context size. -/
def quote (l : Nat) (v : Val) : Tm :=
  match readback G (PRen.id l) none v with
  | .ok t => t
  | .error e => panic! s!"quote: {e}"

def nf (env : Env) (t : Tm) : Tm :=
  quote G env.length (eval G env.length env t)

end

end Kleenextt
