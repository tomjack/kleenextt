import Lean.Data.Lsp
import Lean.Server.Utils
import Kleenextt.Frontend

/-! `kleenextt --server`: a language server on stdio. Each open `.ktt` file is
checked in its own task, cancelled between commands when it changes, and its
messages are published as diagnostics as they arrive, with Lean's
`$/lean/fileProgress` marking the unchecked remainder. Imports are checked
from disk and kept across checks while every file in their closure is
unchanged. -/

namespace Kleenextt.Server

open Lean Lsp JsonRpc Frontend

/-- Import closures checked from disk and the sources they were checked from. -/
structure Cache where
  loaded : Std.HashMap String (Array KModule) := {}
  sources : Std.HashMap String String := {}

structure Doc where
  version : Nat
  text : FileMap
  task : Task (Except IO.Error Unit)

/-- What a completed check of a document found: its import closure, and the
sources the imports were read from. -/
structure Analysis where
  closure : Array KModule
  sources : Std.HashMap String String

structure Context where
  env : Environment
  out : IO.FS.Stream
  /-- Serialises writes; cancelling a document's task while holding it keeps
  the task's later output out. -/
  lock : Std.Mutex Unit
  cache : IO.Ref Cache
  docs : IO.Ref (Std.HashMap DocumentUri Doc)
  analyses : IO.Ref (Std.HashMap DocumentUri Analysis)

/-- Dropped from a cancelled task, so a stale check publishes nothing after
its replacement has started. -/
def send (ctx : Context) (msg : JsonRpc.Message) : IO Unit :=
  ctx.lock.atomically do
    unless ← IO.checkCanceled do
      ctx.out.writeLspMessage msg

def notify [ToJson α] (ctx : Context) (method : String) (params : α) : IO Unit :=
  send ctx (.notification method (Json.toStructured? params).toOption)

def respond [ToJson α] (ctx : Context) (id : RequestID) (result : α) : IO Unit :=
  send ctx (.response id (toJson result))

def pathOf (uri : DocumentUri) : System.FilePath :=
  (System.Uri.fileUriToPath? uri).getD uri

/-- The cached closures whose files all still have the content they were
checked from. -/
def Cache.fresh (c : Cache) : IO Cache := do
  let mut fresh : Std.HashMap String Bool := {}
  for (path, source) in c.sources do
    let current ← try IO.FS.readFile path catch _ => pure ""
    fresh := fresh.insert path (current == source)
  pure {
    loaded := c.loaded.filter fun _ closure => closure.all fun m => fresh[m.path]?.getD false
    sources := c.sources.filter fun path _ => fresh[path]?.getD false }

def Cache.merge (c : Cache) (l : Loader) : Cache :=
  { loaded := l.loaded.fold (·.insert) c.loaded, sources := l.sources.fold (·.insert) c.sources }

def toLsp (text : FileMap) (d : Frontend.Diagnostic) : Lsp.Diagnostic :=
  { range := { start := text.utf8PosToLspPos d.pos, «end» := text.utf8PosToLspPos d.endPos }
    severity? := some (match d.severity with
      | .error => .error
      | .info => .information)
    source? := some "kleenextt"
    message := d.msg }

/-- Check a document, on the task that owns it. -/
def check (ctx : Context) (uri : DocumentUri) (version : Nat) (text : FileMap) : IO Unit := do
  let path := pathOf uri
  let diags ← IO.mkRef (#[] : Array Lsp.Diagnostic)
  let publish : IO Unit := do
    notify ctx "textDocument/publishDiagnostics"
      { uri, version? := some version, diagnostics := ← diags.get : PublishDiagnosticsParams }
  let emit (ictx : Parser.InputContext) (d : Frontend.Diagnostic) : IO Unit := do
    if ictx.fileName == path.toString then
      diags.modify (·.push (toLsp text d))
      publish
    else
      IO.eprintln (d.format ictx)
  let progress (_ : Parser.InputContext) (cmd? : Option Syntax) : IO Unit := do
    let processing := match cmd? with
      | some cmd => #[{ range := {
          start := text.utf8PosToLspPos (cmd.getPos?.getD 0)
          «end» := text.utf8PosToLspPos text.source.rawEndPos } }]
      | none => #[]
    notify ctx "$/lean/fileProgress"
      { textDocument := { uri, version? := some version }, processing : LeanFileProgressParams }
  publish
  let cache ← (← ctx.cache.get).fresh
  let loader : Loader := { env := ctx.env, loaded := cache.loaded, sources := cache.sources, emit, progress }
  let (closure, l) ← (loadFile path true (some text.source)).run loader
  unless ← IO.checkCanceled do
    ctx.cache.modify (·.merge l)
    ctx.analyses.modify (·.insert uri { closure, sources := l.sources })

/-- Replace the document's check, after the previous one has stopped. -/
def startCheck (ctx : Context) (uri : DocumentUri) (version : Nat) (text : FileMap) : IO Unit := do
  let prev := (← ctx.docs.get)[uri]?
  if let some d := prev then ctx.lock.atomically (IO.cancel d.task)
  let task ← IO.asTask (prio := .dedicated) do
    if let some d := prev then discard <| IO.wait d.task
    try check ctx uri version text
    catch e => IO.eprintln s!"{uri}: {e}"
  ctx.docs.modify (·.insert uri { version, text, task })

def close (ctx : Context) (uri : DocumentUri) : IO Unit := do
  if let some d := (← ctx.docs.get)[uri]? then
    ctx.lock.atomically (IO.cancel d.task)
    ctx.docs.modify (·.erase uri)
    ctx.analyses.modify (·.erase uri)
    notify ctx "$/lean/fileProgress" { textDocument := { uri }, processing := #[] : LeanFileProgressParams }
    notify ctx "textDocument/publishDiagnostics" { uri, diagnostics := #[] : PublishDiagnosticsParams }

def parseParams [FromJson α] (params? : Option Json.Structured) : IO α :=
  match params? with
  | some (.arr a) => IO.ofExcept (fromJson? (Json.arr a))
  | some (.obj o) => IO.ofExcept (fromJson? (Json.obj o))
  | none => throw (IO.userError "missing params")

/-- Where the identifier at `pos` is defined: its binder in this command, a
definition earlier in this document as it currently reads, or one in an
import as of the last completed check. -/
def definition (ctx : Context) (uri : DocumentUri) (doc : Doc) (pos : Lsp.Position) : IO (Option Location) := do
  let text := doc.text
  let path := pathOf uri
  let (cmds, _) := parseCmds ctx.env text.source path.toString
  let at_ := text.lspPosToUtf8Pos pos
  let some cmd := cmds.find? fun c => c.getPos?.getD 0 ≤ at_ && at_ ≤ c.getTailPos?.getD 0
    | return none
  let range (t : FileMap) (s : Symbols.Symbol) : Range :=
    { start := t.utf8PosToLspPos s.pos, «end» := t.utf8PosToLspPos s.endPos }
  match Symbols.resolve cmd at_ with
  | none => return none
  | some (.local b) => return some { uri, range := range text b }
  | some (.import m) =>
    let file := path.parent.getD "." / (m.replace "." "/" ++ ".ktt")
    return some { uri := System.Uri.pathToUri file, range := { start := ⟨0, 0⟩, «end» := ⟨0, 0⟩ } }
  | some (.global name) =>
    let before := cmds.filter fun c => c.getPos?.getD 0 < at_
    if let some s := (before.flatMap Symbols.ofCmd).reverse.find? (·.name == name) then
      return some { uri, range := range text s }
    let some analysis := (← ctx.analyses.get)[uri]? | return none
    for m in analysis.closure.pop.reverse do
      if let some s := m.symbols.reverse.find? (·.name == name) then
        if let some source := analysis.sources[m.path]? then
          return some { uri := System.Uri.pathToUri m.path, range := range source.toFileMap s }
    return none

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
    respond ctx id { capabilities, serverInfo? := some { name := "kleenextt" } : InitializeResult }
  | .request id "shutdown" _ => send ctx (.response id .null)
  | .request id "textDocument/definition" params? =>
    let p : TextDocumentPositionParams ← parseParams params?
    match (← ctx.docs.get)[p.textDocument.uri]? with
    | some d => respond ctx id (← definition ctx p.textDocument.uri d p.position)
    | none => send ctx (.response id .null)
  | .request id method _ =>
    send ctx (.responseError id .methodNotFound s!"unsupported request: {method}" none)
  | .notification "exit" _ => return
  | .notification "textDocument/didOpen" params? =>
    let p : DidOpenTextDocumentParams ← parseParams params?
    let doc := p.textDocument
    startCheck ctx doc.uri doc.version doc.text.toFileMap
  | .notification "textDocument/didChange" params? =>
    let p : DidChangeTextDocumentParams ← parseParams params?
    let uri := p.textDocument.uri
    if let some d := (← ctx.docs.get)[uri]? then
      let text := Lean.Server.foldDocumentChanges p.contentChanges d.text
      startCheck ctx uri (p.textDocument.version?.getD (d.version + 1)) text
  | .notification "textDocument/didClose" params? =>
    let p : DidCloseTextDocumentParams ← parseParams params?
    close ctx p.textDocument.uri
  | _ => pure ()
  loop ctx inp

def run (env : Environment) : IO UInt32 := do
  let ctx : Context := {
    env
    out := ← IO.getStdout
    lock := ← Std.Mutex.new ()
    cache := ← IO.mkRef {}
    docs := ← IO.mkRef {}
    analyses := ← IO.mkRef {} }
  loop ctx (← IO.getStdin)
  pure 0

end Kleenextt.Server
