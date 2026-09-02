import Kleenextt.Syntax

/-! Cubical NbE in the style of cubicaltt, on de Bruijn levels.

Interval variables share the level space with ordinary variables. A value
lives in a context of some size `L`, mentions only levels below `L`, and may
be used in any larger context. Semantic interval binders (`ibind l body`)
record the level `l` of the bound variable; instantiating one substitutes for
that level. Interval substitution (`act`) is eager and re-runs the
computation rules on neutral forms, since substitution can unblock them.

Every semantic operation takes the current context size `L`, which is the
fresh-level supply: an operation that binds an interval variable uses `L` for
it and computes the body at `L + 1`. -/

namespace Kleenextt

/-- A system: components indexed by maximal, incomparable faces. A component
under face `α` does not mention the levels `α` fixes. -/
abbrev System (α : Type) := List (Face × α)

mutual
  inductive Val where
    | var (l : Nat)
    | flex (m : Nat) (sp : List (Val × Icit))
    | lam (x : String) (i : Icit) (c : Closure)
    | ilam (x : String) (c : Closure)
    | ibind (l : Nat) (body : Val)
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

/-- Metavariables (numbered densely in creation order), the object-level
definitions the kernel's computation rules refer to, and the declared
inductive types. -/
structure Globals where
  metas : Array MetaEntry := #[]
  /-- `(E : I → Type) → Equiv (E 1) (E 0)`; `hcomp` in the universe needs it. -/
  lineToEquiv : Option Val := none
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

end Subst

def Face.toSubst (α : Face) : Subst :=
  α.map fun (l, d) => (l, .ofBool d)

/-- Build a system from components, keeping only the maximal faces; the
first component for a face wins (overlapping components agree by typing). -/
def mkSystem (entries : System Val) : System Val :=
  (maximalFaces (entries.map (·.1))).filterMap fun α => entries.find? (·.1 == α)

/-- The cofibration a system covers. -/
def System.cof (sys : System Val) : IExpr :=
  sys.foldr (fun (α, _) acc => .join α.toIExpr acc) .zero

def System.total? (sys : System Val) : Option Val :=
  (sys.find? (·.1.isEmpty)).map (·.2)

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

/-- Evaluate an interval expression over indices in an environment. -/
def evalI (env : Env) (r : IExpr) : IExpr :=
  (r.mapVars fun idx =>
    match env.getD idx default with
    | .i s => s
    | _ => panic! "evalI: not an interval variable").norm

/-- Whether a value mentions any of the levels `ls` as an interval variable;
the support check that lets substitution skip untouched values. -/
partial def Val.mentionsAny (ls : List Nat) (v : Val) : Bool :=
  if ls.isEmpty then false else
  let go := Val.mentionsAny ls
  let goI (r : IExpr) : Bool := r.vars.any ls.contains
  let goClo : Closure → Bool
    | .mk env _ => env.any go
  let goSys (sys : System Val) : Bool := sys.any fun (α, u) => α.any (ls.contains ·.1) || go u
  match v with
  | .var _ | .univ | .interval => false
  | .flex _ sp => sp.any (go ·.1)
  | .lam _ _ c | .ilam _ c => goClo c
  | .ibind l' body => body.mentionsAny (ls.filter (· != l'))
  | .app t u _ | .pair t u => go t || go u
  | .papp p r x y => go p || goI r || go x || go y
  | .i r => goI r
  | .pi _ _ a c | .sigma _ a c => go a || goClo c
  | .fst t | .snd t => go t
  | .pathP a x y => go a || go x || go y
  | .transp a r u => go a || goI r || go u
  | .hcomp a sys u => go a || goSys sys || go u
  | .glueTy a sys => go a || goSys sys
  | .glue tySys sys a => goSys tySys || goSys sys || go a
  | .unglue b sys => go b || goSys sys
  | .prim _ args => args.any go
  | .split P env _ x => go P || env.any go || go x

section
variable (G : Globals)
include G

mutual
  partial def Closure.apply (L : Nat) : Closure → Val → Val
    | .mk env t, u => eval L (u :: env) t

  /-- Apply a value of line type `(i : I) → A` to an interval expression. -/
  partial def lineApp (L : Nat) (f : Val) (r : IExpr) : Val :=
    match f with
    | .ilam _ c => c.apply L (.i r)
    | .lam _ _ c => c.apply L (.i r)
    | .ibind l body => act L [(l, r)] body
    | f => vApp L f (.i r) .expl

  partial def vApp (L : Nat) (t u : Val) (i : Icit) : Val :=
    match t with
    | .lam _ _ c => c.apply L u
    | .ilam _ c => c.apply L u
    | .ibind l body =>
      match u with
      | .i r => act L [(l, r)] body
      | _ => panic! "vApp: interval binder applied to a non-interval"
    | .flex m sp => .flex m ((u, i) :: sp)
    | .transp a r f => transpApp L a r f u i
    | .hcomp a sys f => hcompApp L a sys f u i
    | .prim n args => prim' L n (args ++ [u])
    | t => .app t u i

  partial def vAppSp (L : Nat) (t : Val) : Spine → Val
    | [] => t
    | (u, i) :: sp => vApp L (vAppSp L t sp) u i

  partial def vFst : Val → Val
    | .pair u _ => u
    | t => .fst t

  partial def vSnd : Val → Val
    | .pair _ w => w
    | t => .snd t

  partial def papp' (L : Nat) (p : Val) (r : IExpr) (x y : Val) : Val :=
    if r.isZero then x
    else if r.isOne then y
    else match p with
    | .ilam _ c => c.apply L (.i r)
    | .lam _ _ c => c.apply L (.i r)
    | .ibind l body => act L [(l, r)] body
    | .flex m sp => .flex m ((.i r, .expl) :: sp)
    | p => .papp p r x y

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
    | .lam x i t => .lam x i (.mk env t)
    | .ilam x t => .ilam x (.mk env t)
    | .app t u i => vApp L (eval L env t) (eval L env u) i
    | .univ => .univ
    | .pi x i a b => .pi x i (eval L env a) (.mk env b)
    | .sigma x a b => .sigma x (eval L env a) (.mk env b)
    | .pair t u => .pair (eval L env t) (eval L env u)
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
  outside the support of `σ` is returned as is. -/
  partial def act (L : Nat) (σ : Subst) (v : Val) : Val :=
    let actClo : Closure → Closure
      | .mk env t => .mk (env.map (act L σ)) t
    if !v.mentionsAny (σ.map (·.1)) then v else
    match v with
    | .var l => .var l
    | .flex m sp => .flex m (sp.map fun (u, i) => (act L σ u, i))
    | .lam x i c => .lam x i (actClo c)
    | .ilam x c => .ilam x (actClo c)
    | .ibind l body => .ibind L (act (L + 1) ((l, .var L) :: σ) body)
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
    | .prim n args => prim' L n (args.map (act L σ))
    | .split P env cases x => splitApp L (act L σ P) (env.map (act L σ)) cases (act L σ x)

  /-- Substitute in a system: a face `α` becomes the faces on which `σ`
  makes `α`'s equations hold. -/
  partial def actSys (L : Nat) (σ : Subst) (sys : System Val) : System Val :=
    mkSystem <| sys.flatMap fun (α, u) =>
      let β : Face := α.filter fun (l, _) => (σ.get l).isNone
      let ψ := β.apply <| α.foldr (init := .one) fun (l, d) acc =>
        match σ.get l with
        | some r => .meet (if d then r else .neg r) acc
        | none => acc
      (invFormula ψ true).filterMap fun δ =>
        (δ.meet β).map fun key => (key, act L (σ.under key) u)

  partial def face (L : Nat) (α : Face) (v : Val) : Val :=
    act L α.toSubst v

  partial def faceSys (L : Nat) (α : Face) (sys : System Val) : System Val :=
    actSys L α.toSubst sys

  partial def prim' (L : Nat) (name : String) (args : List Val) : Val :=
    match name, args with
    | "I", [] => .interval
    | "PathP", [a, x, y] => .pathP a x y
    | "Path", [a, x, y] => .pathP (.ilam "_" (.mk [a] (.var 1))) x y
    | _, _ =>
      match G.con? name with
      | some (_, con) =>
        -- A saturated higher constructor reduces to its boundary on a face that holds.
        if args.length == con.arity then
          let env := args.reverse
          match con.boundary.find? (fun (φ, _) => (evalI env φ).isOne) with
          | some (_, e) => eval L env e
          | none => .prim name args
        else .prim name args
      | none =>
        match primDef name with
        | some (arity, body) =>
          if args.length == arity then args.foldl (fun f a => vApp L f a .expl) (eval L [] body)
          else .prim name args
        | none => .prim name args

  /-- Dependent case analysis: reduces on a saturated constructor and, for a
  HIT, on an `hcomp` (the CHM rule, composing over the filler). -/
  partial def splitApp (L : Nat) (P : Val) (env : Env) (cases : List (String × List String × Tm)) (x : Val) : Val :=
    match x with
    | .prim c args =>
      match cases.find? (·.1 == c), G.con? c with
      | some (_, _, body), some (_, con) =>
        if args.length == con.arity then eval L (args.reverse ++ env) body
        else .split P env cases x
      | _, _ => .split P env cases x
    | .hcomp (.prim D []) sys u =>
      match G.data? D with
      | some d =>
        if d.hit then
          let fill := hfill' L (.prim D []) sys u
          let pline := .ibind L (vApp (L + 1) P (lineApp (L + 1) fill (.var L)) .expl)
          let sides := sys.map fun (α, s) =>
            (α, .ibind L (splitApp (L + 1) (face (L + 1) α P) (env.map (face (L + 1) α)) cases
              (lineApp (L + 1) s (.var L))))
          comp' L pline (mkSystem sides) (splitApp L P env cases u) false
        else .split P env cases x
      | none => .split P env cases x
    | _ => .split P env cases x

  /-- `hcomp` at a strict inductive type: constructor-wise, along the field
  telescope, when the base and every side are the same constructor. -/
  partial def hcompData (L : Nat) (A : Val) (sys : System Val) (u : Val) : Val :=
    match u with
    | .prim c args =>
      match G.con? c with
      | some (_, con) =>
        let sideArgs := sys.map fun (α, s) =>
          match lineApp (L + 1) s (.var L) with
          | .prim c' args' => if c' == c && args'.length == args.length then (α, some args') else (α, none)
          | _ => (α, none)
        if args.length != con.fields.length || sideArgs.any (·.2.isNone) then .hcomp A sys u
        else
          let sideArgs := sideArgs.map fun (α, as) => (α, as.getD [])
          .prim c (hcompFields L 0 con.fields [] sideArgs args)
      | none => .hcomp A sys u
    | _ => .hcomp A sys u

  /-- The fields of a constructor-wise `hcomp`; `fills` are the fillers of
  the previous fields, most recent first, which the next field's type may
  depend on. -/
  partial def hcompFields (L : Nat) (k : Nat) (fields : List (String × Tm)) (fills : List Val)
      (sideArgs : List (Face × List Val)) (args : List Val) : List Val :=
    match fields with
    | [] => []
    | (_, T) :: rest =>
      let tline := .ibind L (eval (L + 1) (fills.map fun f => lineApp (L + 1) f (.var L)) T)
      let sysk := sideArgs.map fun (α, as) => (α, .ibind L (as.getD k default))
      let uk := args.getD k default
      let vk := comp' L tline sysk uk false
      let fk := compFill' L tline sysk uk
      vk :: hcompFields L (k + 1) rest (fk :: fills) sideArgs args

  /-- The filler of a heterogeneous composition, as a line. -/
  partial def compFill' (L : Nat) (a : Val) (sys : System Val) (u0 : Val) : Val :=
    let diag := IExpr.meet (.var L) (.var (L + 1))
    let sides := sys.map fun (α, s) => (α, .ibind (L + 1) (lineApp (L + 2) s diag))
    .ibind L (comp' (L + 1) (.ibind (L + 1) (lineApp (L + 2) a diag))
      (mkSystem (sides ++ [([(L, false)], .ibind (L + 1) u0)])) u0 false)

  /-- `transp^i A r u`, with `A` a line; identity when `r = 1`. -/
  partial def transp' (L : Nat) (a : Val) (r : IExpr) (u : Val) : Val :=
    if r.isOne then u else
    match lineApp (L + 1) a (.var L) with
    | .pi .. => .transp a r u
    | .sigma _ A c =>
      let aline := .ibind L A
      let v1 := transp' L aline r (vFst u)
      let fill := transpFill L aline r (vFst u)
      let bline := .ibind L (c.apply (L + 1) (lineApp (L + 1) fill (.var L)))
      .pair v1 (transp' L bline r (vSnd u))
    | .pathP .. =>
      let k := IExpr.var L
      let (x0, y0) := match lineApp L a .zero with
        | .pathP _ x y => (x, y)
        | _ => panic! "transp: line is not constantly a path type"
      let body := match lineApp (L + 2) a (.var (L + 1)) with
        | .pathP A' x' y' =>
          let aline := .ibind (L + 1) (lineApp (L + 2) A' k)
          let base := papp' (L + 1) u k x0 y0
          let sides := (invFormula r true).map (fun δ => (δ, .ibind (L + 1) (face (L + 2) δ base)))
            ++ [([(L, false)], .ibind (L + 1) x'), ([(L, true)], .ibind (L + 1) y')]
          comp' (L + 1) aline (mkSystem sides) base false
        | _ => panic! "transp: line is not constantly a path type"
      .ibind L body
    | .univ => u
    | .prim n [] => if (G.data? n).isSome then u else .transp a r u
    | .glueTy A sysG => transpGlue L r u A sysG
    | _ => .transp a r u

  /-- `transp` at a function type, applied: `(transp^i ((x : A) → B) r f) v`. -/
  partial def transpApp (L : Nat) (a : Val) (r : IExpr) (f u : Val) (i : Icit) : Val :=
    match lineApp (L + 1) a (.var L) with
    | .pi _ _ .interval c =>
      transp' L (.ibind L (c.apply (L + 1) u)) r (vApp L f u i)
    | .pi _ _ dom c =>
      let domNeg := .ibind L (act (L + 1) [(L, .neg (.var L))] dom)
      let w := transpFill L domNeg r u
      let vline := .ibind L (lineApp (L + 1) w (.neg (.var L)))
      let v0 := lineApp L vline .zero
      transp' L (.ibind L (c.apply (L + 1) (lineApp (L + 1) vline (.var L)))) r (vApp L f v0 i)
    | _ => .app (.transp a r f) u i

  /-- The filler `Transp^i A r u`: a line from `u` to `transp^i A r u`. -/
  partial def transpFill (L : Nat) (a : Val) (r : IExpr) (u : Val) : Val :=
    .ibind L (transp' (L + 1)
      (.ibind (L + 1) (lineApp (L + 2) a (.meet (.var L) (.var (L + 1)))))
      (.join r (.neg (.var L))) u)

  /-- Transport from `A r` to `A 1`; the identity when `r = 1`. -/
  partial def forward (L : Nat) (a : Val) (r : IExpr) (u : Val) : Val :=
    transp' L (.ibind L (lineApp (L + 1) a (.join (.var L) r))) r u

  /-- Heterogeneous composition, derived: `comp^i A [φ ↦ u] u₀ =
  hcomp^i (A 1) [φ ↦ forward A i (u i)] (forward A 0 u₀)`, with `ghcomp`
  in place of `hcomp` when `general`. -/
  partial def comp' (L : Nat) (a : Val) (sys : System Val) (u0 : Val) (general : Bool) : Val :=
    let sides := sys.map fun (α, s) =>
      (α, .ibind L (forward (L + 1) (face (L + 1) α a) (.var L) (lineApp (L + 1) s (.var L))))
    let base := forward L a .zero u0
    if general then ghcomp' L (lineApp L a .one) (mkSystem sides) base
    else hcomp' L (lineApp L a .one) (mkSystem sides) base

  /-- `ghcomp A [φ ↦ u] u₀ = hcomp A [φ ↦ u, ¬φ ↦ u₀] u₀`. -/
  partial def ghcomp' (L : Nat) (A : Val) (sys : System Val) (u : Val) : Val :=
    let extra := (invFormula sys.cof false).map fun β => (β, .ibind L (face (L + 1) β u))
    hcomp' L A (mkSystem (sys ++ extra)) u

  partial def hfill' (L : Nat) (A : Val) (sys : System Val) (u : Val) : Val :=
    let sides := sys.map fun (α, s) =>
      (α, .ibind (L + 1) (lineApp (L + 2) s (.meet (.var L) (.var (L + 1)))))
    .ibind L (hcomp' (L + 1) A (mkSystem (sides ++ [([(L, false)], .ibind (L + 1) u)])) u)

  partial def hcomp' (L : Nat) (A : Val) (sys : System Val) (u : Val) : Val :=
    match sys.total? with
    | some s => lineApp L s .one
    | none =>
    match A with
    | .pi .. => .hcomp A sys u
    | .sigma _ a c =>
      let sys1 := sys.map fun (α, s) => (α, .ibind L (vFst (lineApp (L + 1) s (.var L))))
      let sys2 := sys.map fun (α, s) => (α, .ibind L (vSnd (lineApp (L + 1) s (.var L))))
      let u1 := vFst u
      let v1 := hcomp' L a sys1 u1
      let fill1 := hfill' L a sys1 u1
      let bline := .ibind L (c.apply (L + 1) (lineApp (L + 1) fill1 (.var L)))
      .pair v1 (comp' L bline sys2 (vSnd u) false)
    | .pathP a x y =>
      let k := IExpr.var L
      let body :=
        let sides := sys.map (fun (α, s) =>
            (α, .ibind (L + 1) (papp' (L + 2) (lineApp (L + 2) s (.var (L + 1))) k
              (face (L + 2) α x) (face (L + 2) α y))))
          ++ [([(L, false)], .ibind (L + 1) x), ([(L, true)], .ibind (L + 1) y)]
        hcomp' (L + 1) (lineApp (L + 1) a k) (mkSystem sides) (papp' (L + 1) u k x y)
      .ibind L body
    | .univ => hcompU L sys u
    | .glueTy B sysG => hcompGlue L B sysG sys u
    | .prim n [] =>
      match G.data? n with
      | some d => if d.hit then .hcomp A sys u else hcompData L A sys u
      | none => .hcomp A sys u
    | _ => .hcomp A sys u

  /-- `hcomp` at a function type, applied. -/
  partial def hcompApp (L : Nat) (A : Val) (sys : System Val) (f u : Val) (i : Icit) : Val :=
    match A with
    | .pi _ _ _ c =>
      let sides := sys.map fun (α, s) =>
        (α, .ibind L (vApp (L + 1) (lineApp (L + 1) s (.var L)) (face (L + 1) α u) i))
      hcomp' L (c.apply L u) (mkSystem sides) (vApp L f u i)
    | _ => .app (.hcomp A sys f) u i

  /-- `hcomp` in the universe is a `Glue` type along the transport
  equivalences of the sides. -/
  partial def hcompU (L : Nat) (sys : System Val) (u : Val) : Val :=
    match G.lineToEquiv with
    | some lte =>
      glueTy' u (sys.map fun (α, s) => (α, .pair (lineApp L s .one) (vApp L lte s .expl)))
    | none => .hcomp .univ sys u

  partial def hcompGlue (L : Nat) (B : Val) (sysG sys : System Val) (u : Val) : Val :=
    let comps := sysG.map fun (γ, Te) =>
      let T := vFst Te
      let f := vFst (vSnd Te)
      let sysγ := faceSys L γ sys
      let uγ := face L γ u
      (γ, f, hcomp' L T sysγ uγ, hfill' L T sysγ uγ)
    let sidesB := sys.map (fun (α, s) =>
        (α, .ibind L (unglue' (L + 1) (lineApp (L + 1) s (.var L)) (faceSys (L + 1) α sysG))))
      ++ comps.map (fun (γ, f, _, fill) =>
        (γ, .ibind L (vApp (L + 1) f (lineApp (L + 1) fill (.var L)) .expl)))
    let a := hcomp' L B (mkSystem sidesB) (unglue' L u sysG)
    glue' sysG (comps.map fun (γ, _, t, _) => (γ, t)) a

  /-- Extend a partial element of a contractible type to a total one:
  `ext (c, p) [θ ↦ v] = hcomp [θ ↦ p v j, ¬θ ↦ c] c`. -/
  partial def ext (L : Nat) (X contr : Val) (θ : System Val) : Val :=
    let c := vFst contr
    let p := vSnd contr
    let sides := θ.map (fun (α, w) =>
        (α, .ibind L (papp' (L + 1) (vApp (L + 1) (face (L + 1) α p) w .expl) (.var L) (face (L + 1) α c) w)))
      ++ (invFormula θ.cof false).map (fun β => (β, .ibind L (face (L + 1) β c)))
    hcomp' L X (mkSystem sides) c

  /-- `transp^i (Glue [φ ↦ (T, e)] A) r b₀`, after Cubical Agda / Huber:
  the `∀i.φ` correction is folded into a `ghcomp`-based composition in `A`,
  so no empty systems arise. `A` and `sysG` are the peeked components at
  `i = var L`. -/
  partial def transpGlue (L : Nat) (r : IExpr) (b0 A : Val) (sysG : System Val) : Val :=
    let i := IExpr.var L
    let A1 := face L [(L, true)] A
    let sysG0 := faceSys L [(L, false)] sysG
    let sysG1 := faceSys L [(L, true)] sysG
    let a0 := unglue' L b0 sysG0
    let rFaces := invFormula r true
    let δs := sysG.filter fun (γ, _) => !γ.mentions L
    let tfills := δs.map fun (γ, Te) =>
      (γ, transpFill L (.ibind L (vFst Te)) (γ.apply r) (face L γ b0))
    let sidesA := rFaces.map (fun δ => (δ, .ibind L (face (L + 1) δ a0)))
      ++ (δs.zip tfills).map (fun ((γ, Te), (_, tf)) =>
        (γ, .ibind L (vApp (L + 1) (vFst (vSnd Te)) (lineApp (L + 1) tf i) .expl)))
    let a1 := comp' L (.ibind L A) (mkSystem sidesA) a0 true
    let fibs := sysG1.map fun (γ1, Te1) =>
      let T1 := vFst Te1
      let e1 := vSnd Te1
      let f1 := vFst e1
      let a1γ := face L γ1 a1
      let b0γ := face L γ1 b0
      let A1γ := face L γ1 A1
      let refl := fun (w : Val) => Val.ibind L w
      let θ := (invFormula (γ1.apply r) true).map (fun δ =>
          (δ, Val.pair (face L δ b0γ) (refl (face L δ a1γ))))
        ++ tfills.filterMap (fun (γ, tf) => (γ.meet γ1).map fun key =>
          let key := key.minus γ1
          let t1' := face L key (face L γ1 (lineApp L tf .one))
          (key, Val.pair t1' (refl (face L key a1γ))))
      let fibTy := prim' L "fiber" [T1, A1γ, f1, a1γ]
      let contr := vApp L (vSnd e1) a1γ .expl
      let fib := ext L fibTy contr (mkSystem θ)
      (γ1, vFst fib, vSnd fib, f1, a1γ)
    let sidesA1 := fibs.map (fun (γ1, t1, α, f1, a1γ) =>
        (γ1, .ibind L (papp' (L + 1) α i a1γ (vApp (L + 1) f1 t1 .expl))))
      ++ rFaces.map (fun δ => (δ, .ibind L (face (L + 1) δ a1)))
    let a1' := hcomp' L A1 (mkSystem sidesA1) a1
    glue' sysG1 (fibs.map fun (γ1, t1, _, _, _) => (γ1, t1)) a1'

  partial def glueTy' (A : Val) (sys : System Val) : Val :=
    match sys.total? with
    | some Te => vFst Te
    | none => .glueTy A sys

  partial def glue' (tySys sys : System Val) (a : Val) : Val :=
    match sys.total? with
    | some t => t
    | none => .glue tySys sys a

  partial def unglue' (L : Nat) (b : Val) (sys : System Val) : Val :=
    match sys.total? with
    | some Te => vApp L (vFst (vSnd Te)) b .expl
    | none =>
      match b with
      | .glue _ _ a => a
      | b => .unglue b sys
end

/-- Unfold solved metavariables at the head. -/
partial def force (L : Nat) (v : Val) : Val :=
  match v with
  | .flex m sp =>
    match G.lookupMeta m with
    | .solved t => force L (vAppSp G L t sp)
    | .unsolved => v
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
  | .ibind l body => pure (.ilam "i" (← underI fun r => act G (p.cod + 1) [(l, r)] body))
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
