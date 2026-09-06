import Kleenextt.Frontend
import Kleenextt.Server

open Kleenextt.Frontend

def usage : String :=
  "usage: kleenextt check FILE...      check the files, running their # commands\n" ++
  "       kleenextt nf FILE EXPR      normalize a name or expression in FILE's context\n" ++
  "       kleenextt --server          run a language server on stdio"

def run (env : Lean.Environment) : List String → IO UInt32
  | ["--server"] => Kleenextt.Server.run env
  | "check" :: files@(_ :: _) => do
    let (_, l) ← (files.forM fun f => discard <| loadFile f true).run { env }
    pure (if l.errors == 0 then 0 else 1)
  | ["nf", file, expr] => do
    let (closure, l) ← (loadFile file false).run { env }
    if l.errors != 0 then return 1
    let e ← IO.ofExcept (parseExpr env expr)
    IO.println (← normalize (stateOf closure) e)
    pure 0
  | _ => do
    IO.eprintln usage
    pure 2

def main (args : List String) : IO UInt32 := do
  try run (← Lean.mkEmptyEnvironment) args
  catch e =>
    IO.eprintln s!"error: {e}"
    pure 1
