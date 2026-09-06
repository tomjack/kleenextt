import Lean.Server.Utils
import Kleenextt.Lsp

/-! `kleenextt --server`: a language server on stdio. Each open `.ktt` file is
checked by its own `kleenextt --worker` process, whose diagnostics and
progress are forwarded to the client. The evaluator is pure, so a command
cannot be interrupted from inside: an edit at or above the command being
elaborated kills the worker, and a fresh one replays the unchanged prefix
from the disk cache; an edit below it waits for it. Closing a file kills
its worker. -/

namespace Kleenextt.Server

open Lean Lean.Lsp Lean.JsonRpc Frontend Kleenextt.Lsp

structure Worker where
  child : IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .piped }
  /-- The worker's stdin. -/
  out : Out

structure DocState where
  version : Nat
  text : FileMap
  worker : Option Worker := none
  /-- Bumped whenever a worker is started or killed, so a reader of a killed
  worker knows to stand down. -/
  gen : Nat := 0
  /-- The command the worker is elaborating. -/
  current : Option Range := none
  /-- Forwarded requests the worker has not answered. -/
  pending : Array RequestID := #[]

structure Context where
  env : Environment
  out : Out
  docs : Std.Mutex (Std.HashMap DocumentUri DocState)

/-- Kill the document's worker, answering what it left unanswered. -/
def kill (ctx : Context) (d : DocState) : IO DocState := do
  if let some w := d.worker then
    w.child.kill
  for id in d.pending do
    ctx.out.send (.response id .null)
  pure { d with worker := none, current := none, pending := #[], gen := d.gen + 1 }

def onWorkerMessage (ctx : Context) (uri : DocumentUri) (gen : Nat) (msg : JsonRpc.Message) : IO Unit := do
  match msg with
  | .notification "$/kleenextt/command" params? =>
    let p : CommandParams ← parseParams params?
    ctx.docs.atomically do
      if let some d := (← get)[uri]? then
        if d.gen == gen then
          modify (·.insert uri { d with current := p.range? })
  | .notification _ _ => ctx.out.send msg
  | .response id _ | .responseError id .. =>
    ctx.docs.atomically do
      if let some d := (← get)[uri]? then
        modify (·.insert uri { d with pending := d.pending.erase id })
    ctx.out.send msg
  | .request .. => pure ()

/-- An exit the server did not ask for. -/
def onWorkerExit (ctx : Context) (uri : DocumentUri) (gen : Nat) (code : UInt32) : IO Unit :=
  ctx.docs.atomically do
    if let some d := (← get)[uri]? then
      if d.gen == gen then
        IO.eprintln s!"kleenextt: worker for {uri} exited with {code}"
        modify (·.insert uri (← kill ctx { d with worker := none }))

/-- Start a worker on the document as it currently reads. -/
def spawn (ctx : Context) (uri : DocumentUri) (d : DocState) : IO DocState := do
  let child ← IO.Process.spawn {
    cmd := (← IO.appPath).toString
    args := #["--worker"]
    stdin := .piped, stdout := .piped, stderr := .piped }
  let out ← Out.new (IO.FS.Stream.ofHandle child.stdin)
  let gen := d.gen + 1
  discard <| IO.asTask (prio := .dedicated) do
    let err := IO.FS.Stream.ofHandle child.stderr
    repeat
      let line ← err.getLine
      if line.isEmpty then break
      IO.eprint line
  discard <| IO.asTask (prio := .dedicated) do
    let stream := IO.FS.Stream.ofHandle child.stdout
    repeat
      let msg ← try stream.readLspMessage catch _ => break
      onWorkerMessage ctx uri gen msg
    onWorkerExit ctx uri gen (← child.wait)
  out.notify "textDocument/didOpen"
    { textDocument := { uri, languageId := "kleenextt", version := d.version, text := d.text.source }
      : DidOpenTextDocumentParams }
  pure { d with worker := some { child, out }, gen, current := none, pending := #[] }

private def posLE (a b : Lsp.Position) : Bool :=
  a.line < b.line || (a.line == b.line && a.character ≤ b.character)

/-- Whether the change reaches the command being elaborated, whose work is
then wasted; a change after it can wait. -/
private def touches (current : Option Range) : TextDocumentContentChangeEvent → Bool
  | .rangeChange r _ => match current with
    | some c => posLE r.start c.end
    | none => false
  | .fullChange _ => true

def didChange (ctx : Context) (p : DidChangeTextDocumentParams) : IO Unit := do
  let uri := p.textDocument.uri
  ctx.docs.atomically do
    let some d := (← get)[uri]? | return
    let text := Lean.Server.foldDocumentChanges p.contentChanges d.text
    let version := p.textDocument.version?.getD (d.version + 1)
    let d := { d with version, text }
    match d.worker with
    | some w =>
      if p.contentChanges.any (touches d.current) then
        modify (·.insert uri (← spawn ctx uri (← kill ctx d)))
      else
        modify (·.insert uri d)
        w.out.notify "textDocument/didChange" p
    | none => modify (·.insert uri (← spawn ctx uri d))

def didClose (ctx : Context) (uri : DocumentUri) : IO Unit := do
  ctx.docs.atomically do
    if let some d := (← get)[uri]? then
      discard <| kill ctx d
      modify (·.erase uri)
  ctx.out.notify "$/lean/fileProgress" { textDocument := { uri }, processing := #[] : LeanFileProgressParams }
  ctx.out.notify "textDocument/publishDiagnostics" { uri, diagnostics := #[] : PublishDiagnosticsParams }

/-- Forward a request about a document to its worker. -/
def forward (ctx : Context) (id : RequestID) (uri : DocumentUri) (msg : JsonRpc.Message) : IO Unit := do
  ctx.docs.atomically do
    match (← get)[uri]? with
    | some d =>
      match d.worker with
      | some w =>
        modify (·.insert uri { d with pending := d.pending.push id })
        w.out.send msg
      | none => ctx.out.send (.response id .null)
    | none => ctx.out.send (.response id .null)

def capabilities : ServerCapabilities :=
  { textDocumentSync? := some {
      openClose := true
      change := .incremental
      willSave := false
      willSaveWaitUntil := false
      save? := none }
    definitionProvider := true }

/-- Until `exit` or the end of input. -/
partial def loop (ctx : Context) (inp : IO.FS.Stream) : IO Unit := do
  let msg ← try inp.readLspMessage catch _ => return
  match msg with
  | .request id "initialize" _ =>
    ctx.out.respond id { capabilities, serverInfo? := some { name := "kleenextt" } : InitializeResult }
  | .request id "shutdown" _ => ctx.out.send (.response id .null)
  | .request id "textDocument/definition" params? =>
    let p : TextDocumentPositionParams ← parseParams params?
    forward ctx id p.textDocument.uri msg
  | .request id method _ =>
    ctx.out.send (.responseError id .methodNotFound s!"unsupported request: {method}" none)
  | .notification "exit" _ => return
  | .notification "textDocument/didOpen" params? =>
    let p : DidOpenTextDocumentParams ← parseParams params?
    let doc := p.textDocument
    ctx.docs.atomically do
      let d ← spawn ctx doc.uri { version := doc.version, text := doc.text.toFileMap }
      modify (·.insert doc.uri d)
  | .notification "textDocument/didChange" params? => didChange ctx (← parseParams params?)
  | .notification "textDocument/didClose" params? =>
    let p : DidCloseTextDocumentParams ← parseParams params?
    didClose ctx p.textDocument.uri
  | _ => pure ()
  loop ctx inp

def run (env : Environment) : IO UInt32 := do
  let ctx : Context := {
    env
    out := ← Out.new (← IO.getStdout)
    docs := ← Std.Mutex.new {} }
  loop ctx (← IO.getStdin)
  ctx.docs.atomically do
    for (_, d) in ← get do
      discard <| kill ctx d
  pure 0

end Kleenextt.Server
