import Lean.Data.Lsp
import Kleenextt.Frontend

/-! What the server and its workers share: locked output, parameter parsing,
and the message they exchange beyond LSP. -/

namespace Kleenextt.Lsp

open Lean Lean.Lsp Lean.JsonRpc Frontend

/-- Writes serialised through a lock; dropped from a cancelled task, so a
stale check publishes nothing after its replacement has started. -/
structure Out where
  stream : IO.FS.Stream
  lock : Std.Mutex Unit

def Out.new (stream : IO.FS.Stream) : BaseIO Out := do
  pure { stream, lock := ← Std.Mutex.new () }

def Out.send (o : Out) (msg : JsonRpc.Message) : IO Unit :=
  o.lock.atomically do
    unless ← IO.checkCanceled do
      o.stream.writeLspMessage msg

def Out.notify [ToJson α] (o : Out) (method : String) (params : α) : IO Unit :=
  o.send (.notification method (Json.toStructured? params).toOption)

def Out.respond [ToJson α] (o : Out) (id : RequestID) (result : α) : IO Unit :=
  o.send (.response id (toJson result))

def parseParams [FromJson α] (params? : Option Json.Structured) : IO α :=
  match params? with
  | some (.arr a) => IO.ofExcept (fromJson? (Json.arr a))
  | some (.obj o) => IO.ofExcept (fromJson? (Json.obj o))
  | none => throw (IO.userError "missing params")

def pathOf (uri : DocumentUri) : System.FilePath :=
  (System.Uri.fileUriToPath? uri).getD uri

def toLsp (text : FileMap) (d : Frontend.Diagnostic) : Lsp.Diagnostic :=
  { range := { start := text.utf8PosToLspPos d.pos, «end» := text.utf8PosToLspPos d.endPos }
    severity? := some (match d.severity with
      | .error => .error
      | .info => .information)
    source? := some "kleenextt"
    message := d.msg }

/-- Worker to server, `$/kleenextt/command`: the range of the command being
elaborated, for the document version being checked; none at the start and
end of a check. -/
structure CommandParams where
  uri : DocumentUri
  version : Nat
  range? : Option Range := none
  deriving ToJson, FromJson

end Kleenextt.Lsp
