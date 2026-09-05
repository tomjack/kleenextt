import Lean

/-! Derived closure defunctionalization.

A `defun` block wraps a semantic domain and the mutual block of rules over
it. Closures are written at their use sites as `closure% fun x y => body`;
the block is elaborated twice:

1. Against an `unsafe` function-valued closure type, each site wrapped in a
   `site` marker; the elaborated definitions are traversed to record, per
   site, the locals its body captures with their types. Everything declared
   in this pass is discarded.
2. For real: the closure type is an inductive with one constructor per
   site, its fields the captured locals; each site becomes its constructor
   applied to the locals; `apply` re-elaborates each site's lambda in the
   arm for its constructor; each `deriving` clause produces a function
   mapping a class method over the fields.

`defun C (x : A) (y : B) : V deriving f (p : P) via K.m := impl … in cmds
end defun` declares `C.apply : C → A → B → V` and `C.f : P → C → C`
applying `K.m p` to every field, with `⟨impl⟩ : K V` a local instance for
fields of type `V`; `deriving f (p : P) : T folding op e via K.m := impl`
instead folds the fields' `K.m p` values with `op` from `e`. `cmds` must
declare the inductive `V` (alone or in a `mutual` block, with a nullary
constructor) and, after it, the `mutual` block holding the sites. Section
variables are not captured. -/

open Lean Elab Command Term Meta Parser
open Lean.Parser.Term (bracketedBinderF matchAltExpr)

namespace Kleenextt.Core.Defun

/-- The first-pass marker around a closure site's body. -/
def site {α : Sort u} (_id : Nat) (x : α) : α := x

/-- A closure site: `closure% fun x y => body`, inside a `defun` block. -/
syntax (name := closureSite) "closure% " term : term

@[term_elab closureSite] def elabClosureSite : TermElab := fun stx _ =>
  throwErrorAt stx "closure% outside a defun block"

def derivingSpec := leading_parser
  "deriving " >> ident >> many (ppSpace >> Term.bracketedBinder) >>
  optional (Term.typeSpec >> " folding " >> termParser maxPrec >> ppSpace >> termParser maxPrec) >>
  " via " >> ident >> " := " >> termParser

@[command_parser] def defunCmd := leading_parser
  "defun " >> ident >> many (ppSpace >> Term.bracketedBinder) >> Term.typeSpec >>
  many (ppLine >> derivingSpec) >> " in" >>
  many1 (ppLine >> notFollowedBy (atomic (symbol "end" >> symbol "defun")) "end defun" >> commandParser) >>
  ppDedent (ppLine >> "end" >> "defun")

/-! ## Syntax utilities -/

partial def containsKind (k : SyntaxNodeKind) : Syntax → Bool
  | .node _ k' args => k == k' || args.any (containsKind k)
  | _ => false

/-- The explicit binders `(x : T)` of a binder list, as name/type pairs. -/
def explicitBinders (stx : Syntax) : CommandElabM (Array (Name × Term)) := do
  let mut out := #[]
  for b in stx.getArgs do
    unless b.isOfKind ``Term.explicitBinder do
      throwErrorAt b "defun: expected an explicit binder `(x : T)`"
    let ty : Term := ⟨b[2][1]⟩
    for x in b[1].getArgs do
      unless x.isIdent do throwErrorAt x "defun: expected a named binder"
      out := out.push (x.getId, ty)
  return out

def binderNames (binders : Array Syntax) (acc : NameSet := {}) : NameSet :=
  binders.foldl (init := acc) fun acc b =>
    b[1].getArgs.foldl (init := acc) fun acc x => if x.isIdent then acc.insert x.getId else acc

/-- The section variables in scope at and inside a block. -/
partial def sectionVariables (stx : Syntax) : CommandElabM NameSet :=
  return go stx (binderNames (← getScope).varDecls)
where
  go (stx : Syntax) (acc : NameSet) : NameSet :=
    match stx with
    | .node _ k args =>
      if k == ``Command.variable then binderNames args[1]!.getArgs acc
      else args.foldl (fun acc a => go a acc) acc
    | _ => acc

/-- Number the closure sites in pre-order and replace each by `f id fn`,
where `fn` is the site's lambda with its own inner sites replaced. -/
partial def rewriteSites [Monad m] (f : Nat → Term → m Term) : Syntax → StateT Nat m Syntax
  | .node info k args => do
    if k == ``closureSite then
      let id ← modifyGet fun n => (n, n + 1)
      let fn ← rewriteSites f args[1]!
      return ← f id ⟨fn⟩
    else
      return .node info k (← args.mapM (rewriteSites f))
  | stx => pure stx

/-- The pass-1 form of a declaration: `unsafe`, not `partial`, no `deriving`. -/
partial def unsafeify : Syntax → Syntax
  | .node info k args =>
    if k == ``Command.declaration then
      let mods := args[0]!
        |>.setArg 5 (mkNullNode #[mkNode ``Command.unsafe #[mkAtom "unsafe"]])
        |>.setArg 6 mkNullNode
      let decl := args[1]!
      let decl :=
        if decl.isOfKind ``Command.inductive || decl.isOfKind ``Command.structure
            || decl.isOfKind ``Command.classInductive then
          decl.setArg (decl.getNumArgs - 1) (mkNode ``Command.optDeriving #[mkNullNode])
        else if decl.isOfKind ``Command.definition then
          decl.setArg (decl.getNumArgs - 1) mkNullNode
        else decl
      .node info k #[mods, decl]
    else if k == ``Command.deriving then mkNullNode
    else .node info k (args.map unsafeify)
  | stx => stx

/-- Append declarations to a `mutual` block, or make one from a lone declaration. -/
def extendMutual (cmd : Syntax) (extra : Array Syntax) : Syntax :=
  if cmd.isOfKind ``Command.mutual then
    cmd.setArg 1 (mkNullNode (cmd[1].getArgs ++ extra))
  else
    mkNode ``Command.mutual #[mkAtom "mutual", mkNullNode (#[cmd] ++ extra), mkAtom "end"]

def declaresInductive (name : Name) (stx : Syntax) : Bool :=
  stx.isOfKind ``Command.declaration && stx[1].isOfKind ``Command.inductive
    && stx[1][1][0].getId == name

/-! ## Analysis of the first pass -/

structure Site where
  id : Nat
  /-- The constant the site occurs in. -/
  decl : Name
  ctor : Name := .anonymous
  /-- The captured locals: names as bound at the site, delaborated types. -/
  fields : Array (Name × Term)
  fn : Term := ⟨.missing⟩
  deriving Inhabited

/-- Find the sites in the constants added since `old`, with their captures. -/
def analyze (old : Environment) (sectionVars : NameSet) (val : Ident) : CommandElabM (Array Site) := do
  let env ← getEnv
  let consts := env.constants.map₂.toList.filter fun (n, _) => !old.contains n
  let sites ← liftTermElabM do
    let valName ← resolveGlobalConstNoOverload val
    let ref ← IO.mkRef (#[] : Array Site)
    for (n, ci) in consts do
      let some v := ci.value? | continue
      discard <| Meta.transform v (pre := fun e => do
        if e.isAppOfArity ``site 3 then
          let some id := (e.getArg! 1).nat? | throwError "defun: malformed site marker"
          let lctx ← getLCtx
          let decls := (collectFVars {} (e.getArg! 2)).fvarIds.filterMap lctx.find?
            |>.qsort (·.index < ·.index)
          let mut fields := #[]
          for d in decls do
            if sectionVars.contains d.userName then continue
            if fields.any (·.1 == d.userName) then
              throwError "defun: two captured locals named `{d.userName}` at site {id}"
            -- Unfold abbreviations mentioning the domain: they may be
            -- declared after the inductive block.
            let ty ← Meta.transform (← instantiateMVars d.type) (pre := fun e => do
              let e' ← whnfR e
              return if e' == e || (e'.find? (·.isConstOf valName)).isNone then .continue else .visit e')
            fields := fields.push (d.userName, ← PrettyPrinter.delab ty)
          ref.modify (·.push { id, decl := n, fields })
        return .continue)
    ref.get
  let sites := sites.qsort (·.id < ·.id)
  -- Constructor names: the enclosing definition, numbered.
  let mut counts : NameMap Nat := {}
  let mut out := #[]
  for s in sites do
    let short := s.decl.componentsRev.head!
    let k := (counts.find? s.decl).getD 0 + 1
    counts := counts.insert s.decl k
    out := out.push { s with ctor := Name.mkStr .anonymous s!"{short}_{k}" }
  return out

/-! ## Elaboration -/

structure Deriving where
  name : Name
  params : Array (Name × Term)
  /-- Result type, combining operation and its unit, for a fold over the
  fields; an endomap of the closure type when absent. -/
  fold : Option (Term × Term × Term)
  method : Name
  impl : Term

def parseDeriving (stx : Syntax) : CommandElabM Deriving := do
  let fold := match stx[3].getArgs with
    | #[ty, _, op, unit] => some (⟨ty[1]⟩, ⟨op⟩, ⟨unit⟩)
    | _ => none
  return { name := stx[1].getId, params := ← explicitBinders stx[2], fold,
           method := stx[5].getId, impl := ⟨stx[7]⟩ }

def freshIdents (n : Nat) (base : String) : CommandElabM (Array Ident) :=
  (Array.range n).mapM fun k => return mkIdent (← liftCoreM (mkFreshUserName (.mkSimple s!"{base}{k}")))

/-- The constructor applied to the captured locals; `ref` positions the
arguments at the site (with its original source info, so that the linters
count them as uses of the locals). -/
def mkCtorApp (cloName : Name) (s : Site) (ref : Syntax := .missing) : Term :=
  Syntax.mkApp (mkIdent (cloName ++ s.ctor))
    (s.fields.map fun (x, _) => ⟨Syntax.ident ref.getHeadInfo x.toString.toRawSubstring x []⟩)

def mkExplicitBinder (x : Ident) (ty : Term) : CommandElabM (TSyntax ``Term.bracketedBinder) :=
  `(bracketedBinderF| ($x : $ty))

def emptyModifiers : Syntax :=
  mkNode ``Command.declModifiers (Array.replicate 7 mkNullNode)

def mkCtor (name : Ident) (binders : Array (TSyntax ``Term.bracketedBinder)) : Syntax :=
  mkNode ``Command.ctor #[mkNullNode, mkAtom "|", emptyModifiers, name,
    mkNode ``Command.optDeclSig #[mkNullNode (binders.map (·.raw)), mkNullNode]]

def mkInductive (name : Ident) (ctors : Array Syntax) : Syntax :=
  mkNode ``Command.declaration #[emptyModifiers,
    mkNode ``Command.inductive #[mkAtom "inductive", mkNode ``Command.declId #[name, mkNullNode],
      mkNode ``Command.optDeclSig #[mkNullNode, mkNullNode], mkNullNode #[mkAtom "where"],
      mkNullNode ctors, mkNullNode, mkNode ``Command.optDeriving #[mkNullNode]]]

@[command_elab defunCmd] def elabDefun : CommandElab := fun stx => do
  let cloName := stx[1].getId
  let params ← explicitBinders stx[2]
  let retTy : Term := ⟨stx[3][1]⟩
  unless retTy.raw.isIdent do throwErrorAt retTy "defun: the result must be the domain's inductive type"
  let valName := retTy.raw.getId
  let derivings ← stx[4].getArgs.mapM parseDeriving
  let cmds := stx[6].getArgs
  let sectionVars ← sectionVariables stx
  let cloId := mkIdent cloName
  let some indIdx := cmds.findIdx? (fun c => declaresInductive valName c
      || (c.isOfKind ``Command.mutual && c[1].getArgs.any (declaresInductive valName)))
    | throwError "defun: no declaration of `{valName}` in the block"
  let some funIdx := cmds.findIdx? (containsKind ``closureSite)
    | throwError "defun: no closure sites in the block"
  unless cmds[funIdx]!.isOfKind ``Command.mutual do
    throwErrorAt cmds[funIdx]! "defun: closure sites must be inside a `mutual` block"
  if funIdx ≤ indIdx then throwError "defun: the sites must come after the domain's declaration"

  -- Pass 1.
  let hoas ← params.foldrM (init := retTy) fun (_, a) b => `($a → $b)
  let hoasClo ← `(unsafe structure $cloId where apply : $hoas)
  let mkSite1 (id : Nat) (fn : Term) : CommandElabM Term :=
    `($(mkIdent (cloName ++ `mk)) (Kleenextt.Core.Defun.site $(quote id) $fn))
  let (cmds1, _) ← (cmds.mapM (rewriteSites mkSite1)).run 0
  let cmds1 := cmds1.map unsafeify
  let cmds1 := cmds1.set! indIdx (extendMutual cmds1[indIdx]! #[hoasClo])
  -- The derived functions exist in the first pass only to be referenced.
  let stubs ← derivings.mapM fun (d : Deriving) => do
    let binders ← d.params.mapM fun (x, ty) => mkExplicitBinder (mkIdent x) ty
    match d.fold with
    | some (ty, _, unit) =>
      `(unsafe def $(mkIdent (cloName ++ d.name)):ident $binders:bracketedBinder* (_ : $cloId) : $ty := $unit)
    | none =>
      `(unsafe def $(mkIdent (cloName ++ d.name)):ident $binders:bracketedBinder* (c : $cloId) : $cloId := c)
  let cmds1 := cmds1.extract 0 funIdx ++ stubs.map (·.raw) ++ cmds1.extract funIdx cmds1.size
  let saved ← get
  let sites ← try
      withEnv (← getEnv).unlockAsync do
        withScope (fun sc => { sc with opts := Elab.async.set sc.opts false }) do
          for c in cmds1 do elabCommand c
          analyze saved.env sectionVars ⟨retTy⟩
    finally
      modify fun s => { s with scopes := saved.scopes, infoState := saved.infoState }
  if (← get).messages.hasErrors && !saved.messages.hasErrors then return
  if sites.isEmpty then throwError "defun: no closure sites survived elaboration"
  for s in sites do
    if s.fields.any fun (x, _) => x.hasMacroScopes then
      logWarning m!"defun: site {s.ctor} captures an inaccessible local"

  -- Pass 2: the inductive, the sites, `apply`, and the derived maps.
  let ctors ← sites.mapM fun s => do
    let bs ← s.fields.mapM fun (x, ty) => mkExplicitBinder (mkIdent x.eraseMacroScopes) ty
    return mkCtor (mkIdent s.ctor) bs
  let ind := mkInductive cloId ctors
  let fns ← IO.mkRef ({} : Std.HashMap Nat Term)
  let mkSite2 (id : Nat) (fn : Term) : CommandElabM Term := do
    let some s := sites.find? (·.id == id) | throwError "defun: site {id} not found by the first pass"
    fns.modify (·.insert id fn)
    return mkCtorApp cloName s fn
  let (cmds2, _) ← (cmds.mapM (rewriteSites mkSite2)).run 0
  let fns ← fns.get
  let sites := sites.map fun s => { s with fn := fns.getD s.id s.fn }
  let args ← freshIdents params.size "a"
  let binders ← (params.zip args).mapM fun ((_, ty), a) => mkExplicitBinder a ty
  let c := mkIdent (← liftCoreM (mkFreshUserName `c))
  let alts ← sites.mapM fun s =>
    `(matchAltExpr| | $(mkCtorApp cloName s):term => ($(s.fn):term) $args:ident*)
  let apply ← `(partial def $(mkIdent (cloName ++ `apply)):ident ($c : $cloId) $binders:bracketedBinder* : $retTy :=
    match $c:ident with $alts:matchAlt*)
  let derived ← derivings.mapM fun (d : Deriving) => do
    let args ← freshIdents d.params.size "p"
    let binders ← (d.params.zip args).mapM fun ((_, ty), a) => mkExplicitBinder a ty
    let cls := mkIdent d.method.getPrefix
    let meth := mkIdent d.method
    let alts ← sites.mapM fun s => do
      let apps ← s.fields.mapM fun (x, _) => `($meth $args:ident* $(mkIdent x):ident)
      let rhs ← match d.fold with
        | some (_, op, unit) => apps.foldlM (init := unit) fun acc a => `($op $acc $a)
        | none => pure (Syntax.mkApp (mkIdent (cloName ++ s.ctor)) apps)
      `(matchAltExpr| | $(mkCtorApp cloName s):term => $rhs:term)
    let resTy : Term := match d.fold with
      | some (ty, _, _) => ty
      | none => cloId
    `(partial def $(mkIdent (cloName ++ d.name)):ident $binders:bracketedBinder* ($c : $cloId) : $resTy :=
      let _ : $cls $retTy := ⟨$(d.impl)⟩
      match $c:ident with $alts:matchAlt*)
  -- The `partial` derived functions need the closure type inhabited, which
  -- follows from a nullary constructor of the domain.
  let nonempty ← `(deriving instance Nonempty for $retTy, $cloId)
  let cmds2 := cmds2.set! indIdx (extendMutual cmds2[indIdx]! #[ind])
  let cmds2 := cmds2.set! funIdx (extendMutual cmds2[funIdx]! (#[apply] ++ derived))
  let cmds2 := cmds2.insertIdx! (indIdx + 1) nonempty
  for c in cmds2 do elabCommand c

end Kleenextt.Core.Defun
