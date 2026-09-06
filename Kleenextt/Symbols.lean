import Kleenextt.Syntax

/-! Names and their binding sites, read off the syntax: what a command
defines, and what the identifier at a position refers to, by walking the
scopes of the grammar's binding forms. -/

namespace Kleenextt.Symbols

open Lean

/-- A name at its binding site. -/
structure Symbol where
  name : String
  pos : String.Pos.Raw
  endPos : String.Pos.Raw
  deriving Inhabited

def ofIdent (stx : Syntax) : Symbol :=
  let pos := stx.getPos?.getD 0
  { name := stx.getId.toString, pos, endPos := stx.getTailPos?.getD pos }

/-- The names a command defines: a definition, or a data type and its
constructors. -/
def ofCmd (cmd : Syntax) : Array Symbol :=
  match cmd with
  | `(kcmd| def $x:ident : $_ := $_) => #[ofIdent x]
  | `(kcmd| data $x:ident := $cons|*) =>
    cons.getElems.foldl (init := #[ofIdent x]) fun acc con =>
      match con with
      | `(kcon| $c:ident $_* $[[$_,*]]?) => acc.push (ofIdent c)
      | _ => acc
  | _ => #[]

inductive Target
  /-- Bound in the same command. -/
  | «local» (binder : Symbol)
  | global (name : String)
  | «import» (module : String)

/-- Whether `pos` is within `stx`, its end included so that a cursor just
after an identifier still counts. -/
private def contains (stx : Syntax) (pos : String.Pos.Raw) : Bool :=
  match stx.getPos?, stx.getTailPos? with
  | some s, some e => s ≤ pos && pos ≤ e
  | _, _ => false

/-- A binder's bound identifiers and its type, if any. -/
private def bindersOf (b : Syntax) : Array Syntax × Option Syntax :=
  if b.isOfKind ``Syntax.Binder.var then (#[b[0]], none)
  else if b.isOfKind ``Syntax.Binder.typed || b.isOfKind ``Syntax.PiBinder.expl
      || b.isOfKind ``Syntax.PiBinder.impl then (b[1].getArgs, some b[3])
  else if b.isOfKind ``Syntax.Binder.impl then (#[b[1]], none)
  else if b.isOfKind ``Syntax.Binder.named then (#[b[3]], none)
  else if b.isOfKind ``Syntax.PiBinder.untyped then (b[1].getArgs, none)
  else (#[], none)

mutual
  /-- What the identifier at `pos` within `stx` refers to, with `scope` the
  binders in effect, innermost first. -/
  partial def resolveIn (stx : Syntax) (pos : String.Pos.Raw) (scope : List Symbol) : Option Target :=
    if !contains stx pos then none
    else if stx.isIdent then
      let s := ofIdent stx
      match scope.find? (·.name == s.name) with
      | some b => some (.local b)
      | none => some (.global s.name)
    else if stx.isOfKind ``Syntax.Expr.lam then
      resolveBinders stx[1] pos scope fun scope => resolveIn stx[3] pos scope
    else if stx.isOfKind ``Syntax.Expr.pi || stx.isOfKind ``Syntax.Expr.piAscii then
      resolveBinders stx[0] pos scope fun scope => resolveIn stx[2] pos scope
    else if stx.isOfKind ``Syntax.Expr.sigmaDep then
      resolveIn stx[3] pos scope <|> bound stx[1] pos <|> resolveIn stx[6] pos (ofIdent stx[1] :: scope)
    else if stx.isOfKind ``Syntax.Expr.let then
      resolveIn stx[3] pos scope <|> resolveIn stx[5] pos scope <|> bound stx[1] pos
        <|> resolveIn stx[7] pos (ofIdent stx[1] :: scope)
    else if stx.isOfKind ``Syntax.Expr.split then
      resolveIn stx[1] pos scope <|> resolveIn stx[2] pos scope <|> stx[4].getArgs.findSome? fun c =>
        if !c.isOfKind ``Syntax.case then none
        else resolveIn c[0] pos scope <|> c[1].getArgs.findSome? (bound · pos)
          <|> resolveIn c[3] pos (c[1].getArgs.foldl (fun sc x => ofIdent x :: sc) scope)
    else if stx.isOfKind ``Syntax.Expr.appNamed then
      resolveIn stx[0] pos scope <|> resolveIn stx[4] pos scope
    else if stx.isOfKind ``Syntax.Cmd.import then
      some (.import stx[1].getId.toString)
    else if stx.isOfKind ``Syntax.Cmd.data then
      resolveIn stx[1] pos scope <|> stx[3].getArgs.findSome? fun c =>
        if !c.isOfKind ``Syntax.con then none
        else resolveIn c[0] pos scope <|> resolveBinders c[1] pos scope fun scope => resolveIn c[2] pos scope
    else
      stx.getArgs.findSome? (resolveIn · pos scope)

  /-- A binder group: each type is resolved in the scope of the binders
  before it, and `k` gets the scope with all of them. -/
  partial def resolveBinders (group : Syntax) (pos : String.Pos.Raw) (scope : List Symbol)
      (k : List Symbol → Option Target) : Option Target := Id.run do
    let mut scope := scope
    for b in group.getArgs do
      let (xs, ty?) := bindersOf b
      if let some ty := ty? then
        if contains ty pos then return resolveIn ty pos scope
      if let some r := xs.findSome? (bound · pos) then return some r
      scope := xs.foldl (fun sc x => if x.isIdent then ofIdent x :: sc else sc) scope
    k scope

  /-- The binder itself, when the cursor is on it. -/
  partial def bound (x : Syntax) (pos : String.Pos.Raw) : Option Target :=
    if x.isIdent && contains x pos then some (.local (ofIdent x)) else none
end

/-- What the identifier at `pos` in a command refers to. -/
def resolve (cmd : Syntax) (pos : String.Pos.Raw) : Option Target :=
  resolveIn cmd pos []

end Kleenextt.Symbols
