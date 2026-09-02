import Kleenextt.Unify

/-! Bidirectional elaboration with implicit arguments, after elaboration-zoo 04:
implicit applications are inserted when an inferred type is an implicit Pi
(unless the term is an implicit lambda), and implicit lambdas are inserted
when checking against an implicit Pi. Cubical forms are elaborated by
restricting the context to each face of a cofibration. -/

namespace Kleenextt

/-- Whether a name came from the source or from an inserted implicit lambda;
only source names are in scope for lookup. -/
inductive NameOrigin where
  | source
  | inserted
  deriving DecidableEq

structure Cxt where
  env : Env := []
  types : List (String × NameOrigin × Val) := []
  bds : List BD := []
  lvl : Nat := 0

namespace Cxt

def names (cxt : Cxt) : List String :=
  cxt.types.map (·.1)

/-- Extend with a bound variable (a fresh neutral, or a fresh interval
variable when the type is `I`). -/
def bind (cxt : Cxt) (x : String) (a : Val) (origin := NameOrigin.source) : Cxt where
  env := (match a with | .interval => Val.i (.var cxt.lvl) | _ => .var cxt.lvl) :: cxt.env
  types := (x, origin, a) :: cxt.types
  bds := .bound :: cxt.bds
  lvl := cxt.lvl + 1

/-- Extend with a definition. -/
def define (cxt : Cxt) (x : String) (t a : Val) : Cxt where
  env := t :: cxt.env
  types := (x, .source, a) :: cxt.types
  bds := .defined :: cxt.bds
  lvl := cxt.lvl + 1

/-- Restrict to a face: the interval variables it fixes become constants,
which fresh metavariables must not abstract over. -/
def restrict (G : Globals) (cxt : Cxt) (α : Face) : Cxt :=
  { cxt with
    env := cxt.env.map (face G cxt.lvl α)
    types := cxt.types.map fun (x, o, a) => (x, o, face G cxt.lvl α a)
    bds := cxt.bds.zipWith (fun bd idx => if α.mentions (cxt.lvl - idx - 1) then .defined else bd)
      (List.range cxt.bds.length) }

def showVal (G : Globals) (cxt : Cxt) (v : Val) : String :=
  (quote G cxt.lvl v).pretty 0 cxt.names

/-- Close a value over the last variable of the context. -/
def closeVal (G : Globals) (cxt : Cxt) (v : Val) : Closure :=
  .mk cxt.env (quote G (cxt.lvl + 1) v)

/-- Interval expression over levels → over indices. -/
def quoteI (cxt : Cxt) (r : IExpr) : IExpr :=
  r.mapVars fun l => .var (cxt.lvl - l - 1)

def quoteSysFlat (G : Globals) (cxt : Cxt) (sys : System Val) : List (IExpr × Tm) :=
  sys.map fun (α, t) => (cxt.quoteI α.toIExpr, quote G cxt.lvl t)

end Cxt

abbrev ElabM := StateT Globals (Except String)

def freshMeta (cxt : Cxt) : ElabM Tm := do
  let G ← get
  let m := G.metas.size
  set { G with metas := G.metas.push .unsolved }
  pure (.insertedMeta m cxt.bds)

def evalC (cxt : Cxt) (t : Tm) : ElabM Val := do
  let G ← get
  pure (eval G cxt.lvl cxt.env t)

def forceC (cxt : Cxt) (v : Val) : ElabM Val := do
  let G ← get
  pure (force G cxt.lvl v)

def unifyCatch (cxt : Cxt) (expected inferred : Val) : ElabM Unit := do
  try unify cxt.lvl expected inferred
  catch e =>
    let G ← get
    throw s!"type mismatch ({e})\nexpected: {cxt.showVal G expected}\ninferred: {cxt.showVal G inferred}"

/-- Insert fresh implicit applications while the type is an implicit Pi. -/
partial def insertAll (cxt : Cxt) (t : Tm) (a : Val) : ElabM (Tm × Val) := do
  match ← forceC cxt a with
  | .pi _ .impl _ c =>
    let m ← freshMeta cxt
    let G ← get
    insertAll cxt (.app t m .impl) (c.apply G cxt.lvl (eval G cxt.lvl cxt.env m))
  | a => pure (t, a)

/-- Insert implicit applications unless the term is an implicit lambda. -/
def insert (cxt : Cxt) : Tm × Val → ElabM (Tm × Val)
  | (t@(.lam _ .impl _), a) => pure (t, a)
  | (t, a) => insertAll cxt t a

/-- Insert implicit applications until the implicit Pi named `name`. -/
partial def insertUntilName (cxt : Cxt) (name : String) (t : Tm) (a : Val) : ElabM (Tm × Val) := do
  match ← forceC cxt a with
  | a@(.pi x .impl _ c) =>
    if x == name then pure (t, a)
    else
      let m ← freshMeta cxt
      let G ← get
      insertUntilName cxt name (.app t m .impl) (c.apply G cxt.lvl (eval G cxt.lvl cxt.env m))
  | _ => throw s!"no implicit argument named {name}"

private def lookupVar (x : String) : Nat → List (String × NameOrigin × Val) → Except String (Nat × Val)
  | _, [] => throw s!"variable out of scope: {x}"
  | i, (x', origin, a) :: tys =>
    if x == x' && origin == .source then pure (i, a) else lookupVar x (i + 1) tys

/-! ## Primitives -/

private def rv (x : String) : Raw := .var x
private def rap (f : Raw) (args : List Raw) : Raw := args.foldl (fun t u => .app t u .expl) f
private def rpi (x : String) (a b : Raw) : Raw := .pi x .expl a b
private def rarr (a b : Raw) : Raw := .pi "_" .expl a b
private def rimpl (x : String) (a b : Raw) : Raw := .pi x .impl a b

/-- Types of the primitive constants. -/
private def primType : String → Option Raw
  | "PathP" => some <|
    rpi "A" (rarr (rv "I") .univ) <| rarr (rap (rv "A") [.i0]) <| rarr (rap (rv "A") [.i1]) .univ
  | "Path" => some <| rpi "A" .univ <| rarr (rv "A") <| rarr (rv "A") .univ
  | "isContr" => some (rarr .univ .univ)
  | "fiber" => some <| rimpl "A" .univ <| rimpl "B" .univ <| rarr (rarr (rv "A") (rv "B")) <| rarr (rv "B") .univ
  | "isEquiv" => some <| rimpl "A" .univ <| rimpl "B" .univ <| rarr (rarr (rv "A") (rv "B")) .univ
  | "Equiv" => some (rarr .univ (rarr .univ .univ))
  | _ => none

/-- The type `(i : I) → Type` of lines of types. -/
def lineU : Val := .pi "i" .expl .interval (.mk [] .univ)

/-- `(T : Type) × Equiv T A`, the type of a `Glue` component over `A`. -/
def glueCompTy (A : Val) : Val :=
  .sigma "T" .univ (.mk [A] (.app (.app (.prim "Equiv") (.var 0) .expl) (.var 1) .expl))

/-- The type of a constructor: its fields, then its interval binders. -/
def conType (d : DataInfo) (con : ConInfo) : Tm :=
  con.fields.foldr (fun (f, T) acc => .pi f .expl T acc)
    (con.ivars.foldr (fun i acc => .pi i .expl .interval acc) (.prim d.name))

mutual
  /-- Check a type: `I` is allowed as a Pi domain but is not in `Type`. -/
  partial def checkType (cxt : Cxt) (t : Raw) : ElabM Tm := do
    match t with
    | .var "I" =>
      match lookupVar "I" 0 cxt.types with
      | .ok _ => check cxt t .univ
      | .error _ => pure .interval
    | t => check cxt t .univ

  partial def checkI (cxt : Cxt) (t : Raw) : ElabM IExpr := do
    match t with
    | .i0 => pure .zero
    | .i1 => pure .one
    | .ineg r => do pure (.neg (← checkI cxt r))
    | .imeet r s => do pure (.meet (← checkI cxt r) (← checkI cxt s))
    | .ijoin r s => do pure (.join (← checkI cxt r) (← checkI cxt s))
    | .var x =>
      let (idx, a) ← lookupVar x 0 cxt.types
      match ← forceC cxt a with
      | .interval => pure (.var idx)
      | _ => throw s!"{x} is not an interval variable"
    | .hole => throw "interval metavariables are not supported"
    | _ => throw "expected an interval expression"

  partial def check (cxt : Cxt) (t : Raw) (a : Val) : ElabM Tm := do
    let G ← get
    match t, force G cxt.lvl a with
    | .lam x k t, .pi x' i a c =>
      let fits := match k with
        | .expl => i == Icit.expl
        | .impl => i == Icit.impl
        | .named n => n == x' && i == Icit.impl
      if fits then
        match a with
        | .interval =>
          let cxt' := cxt.bind x .interval
          return .ilam x (← check cxt' t (c.apply G cxt'.lvl (.i (.var cxt.lvl))))
        | _ =>
          return .lam x i (← check (cxt.bind x a) t (c.apply G (cxt.lvl + 1) (.var cxt.lvl)))
      else if i == Icit.impl then
        return .lam x' .impl (← check (cxt.bind x' a .inserted) (.lam x k t) (c.apply G (cxt.lvl + 1) (.var cxt.lvl)))
      else
        fallback cxt (.lam x k t) (.pi x' i a c)
    | .lam x _ t, .pathP A x0 x1 =>
      let cxt' := cxt.bind x .interval
      let t ← check cxt' t (lineApp G cxt'.lvl A (.var cxt.lvl))
      let G ← get
      -- The endpoints are evaluated in the restricted context rather than
      -- restricted after evaluation: the open value can be far larger.
      let at0 := eval G cxt'.lvl (cxt'.restrict G [(cxt.lvl, false)]).env t
      let at1 := eval G cxt'.lvl (cxt'.restrict G [(cxt.lvl, true)]).env t
      try unify cxt.lvl at0 x0; unify cxt.lvl at1 x1
      catch e =>
        let G ← get
        throw s!"path endpoints do not match ({e})\nexpected: {cxt.showVal G x0}, {cxt.showVal G x1}\nfound: {cxt.showVal G at0}, {cxt.showVal G at1}"
      return .ilam x t
    | t, .pi x .impl a c =>
      return .lam x .impl (← check (cxt.bind x a .inserted) t (c.apply G (cxt.lvl + 1) (.var cxt.lvl)))
    | .letE x a t u, a' =>
      let a ← checkType cxt a
      let va ← evalC cxt a
      let t ← check cxt t va
      let vt ← evalC cxt t
      let u ← check (cxt.define x vt va) u a'
      return .letE x a t u
    | .hole, _ => freshMeta cxt
    | .sorry, _ => pure (.prim "sorry")
    | .pair t u, .sigma _ a c =>
      let t ← check cxt t a
      let vt ← evalC cxt t
      let G ← get
      let u ← check cxt u (c.apply G cxt.lvl vt)
      return .pair t u
    | .glue sys a, .glueTy A sysG => checkGlue cxt sys a A sysG
    | .system _, _ => throw "a system can only be an argument of hcomp, hfill, comp, Glue or glue"
    | t, .interval => return .i (← checkI cxt t)
    | t, a => fallback cxt t a

  partial def fallback (cxt : Cxt) (t : Raw) (expected : Val) : ElabM Tm := do
    let (t, inferred) ← insert cxt (← infer cxt t)
    unifyCatch cxt expected inferred
    return t

  partial def infer (cxt : Cxt) : Raw → ElabM (Tm × Val)
    | .var x => do
      match lookupVar x 0 cxt.types with
      | .ok (i, a) =>
        match ← forceC cxt a with
        | .interval => pure (.i (.var i), .interval)
        | a => pure (.var i, a)
      | .error e =>
        let G ← get
        match G.def? x, G.data? x, G.con? x, primType x with
        | some (_, ty), _, _, _ => pure (.top x, ty)
        | _, some _, _, _ => pure (.prim x, .univ)
        | _, _, some (d, con), _ => pure (.prim x, eval G 0 [] (conType d con))
        | _, _, _, some ty =>
          let ty ← check {} ty .univ
          let G ← get
          pure (.prim x, eval G 0 [] ty)
        | _, _, _, none => if x == "I" then throw "I is not a term of a type" else throw e
    | .univ => pure (.univ, .univ)
    | .app t u k => do
      let (i, t, tty) ← match k with
        | .named n =>
          let (t, tty) ← infer cxt t
          let (t, tty) ← insertUntilName cxt n t tty
          pure (Icit.impl, t, tty)
        | .impl =>
          let (t, tty) ← infer cxt t
          pure (Icit.impl, t, tty)
        | .expl =>
          let (t, tty) ← infer cxt t
          let (t, tty) ← insertAll cxt t tty
          pure (Icit.expl, t, tty)
      let G ← get
      match force G cxt.lvl tty with
      | .pi _ i' .interval c =>
        if i != i' then throw "implicitness mismatch in application"
        let r ← checkI cxt u
        pure (.app t (.i r) i, c.apply G cxt.lvl (.i (evalI cxt.env r)))
      | .pathP A x y =>
        if i != .expl then throw "implicitness mismatch in application"
        let r ← checkI cxt u
        pure (.papp t r (quote G cxt.lvl x) (quote G cxt.lvl y), lineApp G cxt.lvl A (evalI cxt.env r))
      | .pi _ i' a c =>
        if i != i' then throw "implicitness mismatch in application"
        let u ← check cxt u a
        let G ← get
        pure (.app t u i, c.apply G cxt.lvl (eval G cxt.lvl cxt.env u))
      | tty =>
        let a := eval G cxt.lvl cxt.env (← freshMeta cxt)
        let c := Closure.mk cxt.env (← freshMeta (cxt.bind "x" a))
        unifyCatch cxt tty (.pi "x" i a c)
        let u ← check cxt u a
        let G ← get
        pure (.app t u i, c.apply G cxt.lvl (eval G cxt.lvl cxt.env u))
    | .lam x k t => do
      let i ← match k with
        | .expl => pure Icit.expl
        | .impl => pure Icit.impl
        | .named _ => throw "can't infer a type for a named implicit lambda"
      let G ← get
      let a := eval G cxt.lvl cxt.env (← freshMeta cxt)
      let cxt' := cxt.bind x a
      let (t, b) ← insert cxt' (← infer cxt' t)
      let G ← get
      pure (.lam x i t, .pi x i a (cxt.closeVal G b))
    | .pi x i a b => do
      let a ← checkType cxt a
      let va ← evalC cxt a
      let b ← check (cxt.bind x va) b .univ
      pure (.pi x i a b, .univ)
    | .sigma x a b => do
      let a ← check cxt a .univ
      let va ← evalC cxt a
      let b ← check (cxt.bind x va) b .univ
      pure (.sigma x a b, .univ)
    | .pair t u => do
      let (t, a) ← infer cxt t
      let (u, b) ← infer cxt u
      let G ← get
      pure (.pair t u, .sigma "_" a (.mk cxt.env (quote G (cxt.lvl + 1) b)))
    | .fst t => do
      let (t, a) ← infer cxt t
      match ← forceC cxt a with
      | .sigma _ a _ => pure (.fst t, a)
      | a => do let G ← get; throw s!"expected a pair type, inferred: {cxt.showVal G a}"
    | .snd t => do
      let (t, a) ← infer cxt t
      match ← forceC cxt a with
      | .sigma _ _ c =>
        let G ← get
        pure (.snd t, c.apply G cxt.lvl (vFst G (eval G cxt.lvl cxt.env t)))
      | a => do let G ← get; throw s!"expected a pair type, inferred: {cxt.showVal G a}"
    | .letE x a t u => do
      let a ← checkType cxt a
      let va ← evalC cxt a
      let t ← check cxt t va
      let vt ← evalC cxt t
      let (u, uty) ← infer (cxt.define x vt va) u
      pure (.letE x a t u, uty)
    | .hole => do
      let G ← get
      let a := eval G cxt.lvl cxt.env (← freshMeta cxt)
      let t ← freshMeta cxt
      pure (t, a)
    | .ann t a => do
      let a ← checkType cxt a
      let va ← evalC cxt a
      let t ← check cxt t va
      pure (t, va)
    | .sorry => throw "sorry needs a known type"
    | .split x P cases => do
      let (x, xty) ← infer cxt x
      let (x, xty) ← insertAll cxt x xty
      let G ← get
      let d ← match force G cxt.lvl xty with
        | .prim D [] =>
          match G.data? D with
          | some d => pure d
          | none => throw s!"case: {D} is not an inductive type"
        | a => throw s!"case: expected an inductive type, inferred: {cxt.showVal G a}"
      let P ← check cxt P (.pi "_" .expl (.prim d.name []) (.mk [] .univ))
      let vP ← evalC cxt P
      let vx ← evalC cxt x
      let mut cases' : List (String × List String × Tm) := []
      for con in d.cons do
        let some (_, names, body) := cases.find? (·.1 == con.name)
          | throw s!"case: missing case for {con.name}"
        unless names.length == con.arity do
          throw s!"case: {con.name} takes {con.arity} arguments"
        let mut c := cxt
        let mut fenv : Env := []
        let mut args : List Val := []
        for ((_, T), name) in con.fields.zip (names.take con.fields.length) do
          let G ← get
          let v := Val.var c.lvl
          c := c.bind name (eval G c.lvl fenv T)
          fenv := v :: fenv
          args := args ++ [v]
        for name in names.drop con.fields.length do
          args := args ++ [Val.i (.var c.lvl)]
          c := c.bind name .interval
        let G ← get
        let body ← check c body (vApp G c.lvl vP (prim' G c.lvl con.name args) .expl)
        let G ← get
        let vbody := eval G c.lvl c.env body
        let conEnv := args.reverse
        let casesSoFar := cases' ++ [(con.name, names, body)]
        -- A `sorry` case is exempt from its boundary, like a cctt hole.
        let boundary := if body matches .prim "sorry" then [] else con.boundary
        for (φ, e) in boundary do
          for δ in invFormula (evalI conEnv φ) true do
            let G ← get
            let lhs := face G c.lvl δ vbody
            let rhs := splitApp G c.lvl (face G c.lvl δ vP) (cxt.env.map (face G c.lvl δ)) casesSoFar
              (eval G c.lvl (conEnv.map (face G c.lvl δ)) e)
            try unify c.lvl lhs rhs
            catch err => throw s!"case: the {con.name} case does not respect its boundary ({err})"
        cases' := casesSoFar
      let G ← get
      pure (.split P cases' x, vApp G cxt.lvl vP vx .expl)
    | t@(.i0) | t@(.i1) | t@(.ineg _) | t@(.imeet _ _) | t@(.ijoin _ _) => do
      pure (.i (← checkI cxt t), .interval)
    | .system _ => throw "a system can only be an argument of hcomp, hfill, comp, Glue or glue"
    | .transp A r u => do
      let A ← check cxt A lineU
      let r ← checkI cxt r
      let G ← get
      let vA := eval G cxt.lvl cxt.env A
      let vr := evalI cxt.env r
      for δ in invFormula vr true do
        let G ← get
        let Aδ := eval G cxt.lvl (cxt.restrict G δ).env A
        let at0 := lineApp G cxt.lvl Aδ .zero
        let ati := lineApp G (cxt.lvl + 1) Aδ (.var cxt.lvl)
        try unify (cxt.lvl + 1) ati at0
        catch e => throw s!"transp: the type line is not constant where the cofibration holds ({e})"
      let u ← check cxt u (lineApp G cxt.lvl vA .zero)
      pure (.transp A r u, lineApp G cxt.lvl vA .one)
    | .hcomp g A j sys u => do
      let A ← check cxt A .univ
      let vA ← evalC cxt A
      let (entries, vsys) ← checkBoundSys cxt j sys vA
      let u ← check cxt u vA
      checkBoundary cxt vsys u
      pure (.hcomp g A entries u, vA)
    | .hfill A j sys u r => do
      let A ← check cxt A .univ
      let vA ← evalC cxt A
      let (entries, vsys) ← checkBoundSys cxt j sys vA
      let u ← check cxt u vA
      checkBoundary cxt vsys u
      let r ← checkI cxt r
      pure (.hfill A entries u r, vA)
    | .comp i A j sys u => do
      let cxti := cxt.bind i .interval
      let A ← check cxti A .univ
      let G ← get
      let vAline : Val := .ilam i (.mk cxt.env A)
      let vAi := eval G cxti.lvl cxti.env A
      let (entries, vsys) ← checkBoundSys cxt j sys vAi
      let u ← check cxt u (lineApp G cxt.lvl vAline .zero)
      checkBoundary cxt vsys u
      let G ← get
      pure (.comp A entries u, lineApp G cxt.lvl vAline .one)
    | .glueTy A sys => do
      let A ← check cxt A .univ
      let vA ← evalC cxt A
      let (entries, _) ← checkFlatSys cxt sys (glueCompTy vA)
      pure (.glueTy A entries, .univ)
    | .glue .. => throw "glue needs a known Glue type; add a type annotation"
    | .unglue b => do
      let (b, bty) ← infer cxt b
      let (b, bty) ← insertAll cxt b bty
      match ← forceC cxt bty with
      | .glueTy A sysG =>
        let G ← get
        pure (.unglue b (cxt.quoteSysFlat G sysG), A)
      | a => do let G ← get; throw s!"expected a Glue type, inferred: {cxt.showVal G a}"

  /-- Check the components of a system `[φ ↦ t]` whose terms bind an interval
  variable `j`, against a type `ty` in `cxt, j`. Returns the core entries and
  the components as lines in `j`, indexed by face. -/
  partial def checkBoundSys (cxt : Cxt) (j : String) (sys : List (Raw × Raw)) (ty : Val) :
      ElabM (List (IExpr × Tm) × System Val) := do
    let cxtj := cxt.bind j .interval
    let mut entries : List (IExpr × Tm) := []
    let mut vsys : System Val := []
    for (φ, t) in sys do
      let φ ← checkI cxt φ
      let faces := invFormula (evalI cxt.env φ) true
      if faces.isEmpty then
        entries := entries ++ [(φ, ← check cxtj t ty)]
      for δ in faces do
        let G ← get
        let cxtδ := cxtj.restrict G δ
        let t' ← check cxtδ t (face G cxtj.lvl δ ty)
        let G ← get
        vsys := vsys ++ [(δ, .ilam j (.mk cxtδ.env.tail t'))]
        entries := entries ++ [(φ, t')]
    checkCompatible cxt true vsys
    pure (entries, mkSystem vsys)

  /-- Check the components of a system whose terms do not bind a variable. -/
  partial def checkFlatSys (cxt : Cxt) (sys : List (Raw × Raw)) (ty : Val) :
      ElabM (List (IExpr × Tm) × System Val) := do
    let mut entries : List (IExpr × Tm) := []
    let mut vsys : System Val := []
    for (φ, t) in sys do
      let φ ← checkI cxt φ
      let faces := invFormula (evalI cxt.env φ) true
      if faces.isEmpty then
        entries := entries ++ [(φ, ← check cxt t ty)]
      for δ in faces do
        let G ← get
        let cxtδ := cxt.restrict G δ
        let t' ← check cxtδ t (face G cxt.lvl δ ty)
        let G ← get
        vsys := vsys ++ [(δ, eval G cxtδ.lvl cxtδ.env t')]
        entries := entries ++ [(φ, t')]
    checkCompatible cxt false vsys
    pure (entries, mkSystem vsys)

  /-- Overlapping components must agree on their common face. -/
  partial def checkCompatible (cxt : Cxt) (lines : Bool) (vsys : System Val) : ElabM Unit := do
    for (δ1, s1) in vsys do
      for (δ2, s2) in vsys do
        if δ1 != δ2 && δ1.compatible δ2 then
          let G ← get
          let l := cxt.lvl
          let (v1, v2) :=
            if lines then
              (lineApp G (l + 1) (face G (l + 1) (δ2.minus δ1) s1) (.var l),
               lineApp G (l + 1) (face G (l + 1) (δ1.minus δ2) s2) (.var l))
            else (face G l (δ2.minus δ1) s1, face G l (δ1.minus δ2) s2)
          try unify (if lines then l + 1 else l) v1 v2
          catch e => throw s!"system components disagree where their faces overlap ({e})"

  /-- The base of a composition must agree with the sides at `0`. -/
  partial def checkBoundary (cxt : Cxt) (vsys : System Val) (u : Tm) : ElabM Unit := do
    for (δ, s) in vsys do
      let G ← get
      let uδ := eval G cxt.lvl (cxt.restrict G δ).env u
      try unify cxt.lvl uδ (lineApp G cxt.lvl s .zero)
      catch e => throw s!"the base does not match the sides of the system ({e})"

  partial def checkGlue (cxt : Cxt) (sys : List (Raw × Raw)) (a : Raw) (A : Val) (sysG : System Val) : ElabM Tm := do
    let mut entries : List (IExpr × Tm) := []
    let mut comps : System Val := []
    for (φ, t) in sys do
      let φ ← checkI cxt φ
      for δ in invFormula (evalI cxt.env φ) true do
        match sysG.find? (·.1 == δ) with
        | none => throw "glue: a face of the system is not a face of the Glue type"
        | some (_, Te) =>
          let G ← get
          let cxtδ := cxt.restrict G δ
          let t' ← check cxtδ t (vFst G Te)
          let G ← get
          comps := comps ++ [(δ, eval G cxtδ.lvl cxtδ.env t')]
          entries := entries ++ [(φ, t')]
    for (δ, _) in sysG do
      unless comps.any (·.1 == δ) do throw "glue: the system does not cover every face of the Glue type"
    let a ← check cxt a A
    for (δ, vt) in comps do
      let G ← get
      let Te := (sysG.find? (·.1 == δ)).get!.2
      let aδ := eval G cxt.lvl (cxt.restrict G δ).env a
      try unify cxt.lvl aδ (vApp G cxt.lvl (vFst G (vSnd G Te)) vt .expl)
      catch e => throw s!"glue: the base is not the image of the component under the equivalence ({e})"
    let G ← get
    pure (.glue (cxt.quoteSysFlat G sysG) entries a)
end

/-- Replace solved metavariables by their solutions; fail on unsolved ones. -/
partial def zonk (G : Globals) (env : Env) (l : Nat) : Tm → Except String Tm
  | .mvar m => metaSolution m
  | .insertedMeta m bds => do
    let _ ← metaSolution m
    pure (quote G l (eval G l env (.insertedMeta m bds)))
  | .var i => pure (.var i)
  | .univ => pure .univ
  | .interval => pure .interval
  | .i r => pure (.i r)
  | .prim n => pure (.prim n)
  | .top n => pure (.top n)
  | .app t u i => do pure (.app (← z t) (← z u) i)
  | .lam x i t => do pure (.lam x i (← under t))
  | .ilam x t => do pure (.ilam x (← underI t))
  | .pi x i a b => do pure (.pi x i (← z a) (← if a matches .interval then underI b else under b))
  | .sigma x a b => do pure (.sigma x (← z a) (← under b))
  | .pair t u => do pure (.pair (← z t) (← z u))
  | .fst t => do pure (.fst (← z t))
  | .snd t => do pure (.snd (← z t))
  | .letE x a t u => do pure (.letE x (← z a) (← z t) (← under u))
  | .papp p r x y => do pure (.papp (← z p) r (← z x) (← z y))
  | .transp a r u => do pure (.transp (← z a) r (← z u))
  | .hcomp g a sys u => do pure (.hcomp g (← z a) (← zsys sys) (← z u))
  | .hfill a sys u r => do pure (.hfill (← z a) (← zsys sys) (← z u) r)
  | .comp a sys u => do pure (.comp (← underI a) (← zsys sys) (← z u))
  | .glueTy a sys => do pure (.glueTy (← z a) (← zflat sys))
  | .glue tySys sys a => do pure (.glue (← zflat tySys) (← zflat sys) (← z a))
  | .unglue b sys => do pure (.unglue (← z b) (← zflat sys))
  | .glueU tySys us a => do pure (.glueU (← zsys tySys) (← zflat us) (← z a))
  | .unglueU b sys => do pure (.unglueU (← z b) (← zsys sys))
  | .split P cases x => do
    let cases' ← cases.mapM fun (c, names, body) => do
      let (nf, ni) := match G.con? c with
        | some (_, con) => (con.fields.length, con.ivars.length)
        | none => (0, 0)
      let args := (List.range nf).map (fun k => Val.var (l + k))
        ++ (List.range ni).map (fun k => Val.i (.var (l + nf + k)))
      pure (c, names, ← zonk G (args.reverse ++ env) (l + nf + ni) body)
    pure (.split (← z P) cases' (← z x))
where
  z := zonk G env l
  under (t : Tm) := zonk G (.var l :: env) (l + 1) t
  underI (t : Tm) := zonk G (.i (.var l) :: env) (l + 1) t
  zsys (sys : List (IExpr × Tm)) := sys.mapM fun (φ, t) => do pure (φ, ← underI t)
  zflat (sys : List (IExpr × Tm)) := sys.mapM fun (φ, t) => do pure (φ, ← z t)
  metaSolution (m : Nat) : Except String Tm :=
    match G.lookupMeta m with
    | .solved v => pure (quote G l v)
    | .unsolved => throw s!"unsolved metavariable ?{m}"

end Kleenextt
