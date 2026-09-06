import Lean.Server.Utils
import Kleenextt.Lsp

/-! `kleenextt --server`: a language server on stdio. Each open `.ktt` file is
checked by its own `kleenextt --worker` process, whose diagnostics and
progress are forwarded to the client. A command that runs past the time
budget gets its worker killed and is remembered as slow: the replacement
checks it at its type only, until `$/kleenextt/check` asks for it in full.
A killed worker starts over, so the file's imports and earlier commands are
checked again. -/

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
  /-- Bumped whenever a worker is started or killed; a timer acts only on the
  generation it was set for. -/
  gen : Nat := 0
  /-- The latest version the worker has reported on. -/
  seen : Nat := 0
  current : Option CommandInfo := none
  /-- Forwarded requests the worker has not answered. -/
  pending : Array RequestID := #[]
  /-- Commands requested in full, until the check that runs them completes. -/
  forced : Array Nat := #[]

structure Context where
  env : Environment
  out : Out
  budgetMs : IO.Ref Nat
  slow : IO.Ref (Std.HashSet Nat)
  docs : Std.Mutex (Std.HashMap DocumentUri DocState)

def after (ms : Nat) (act : IO Unit) : IO Unit :=
  discard <| IO.asTask (prio := .dedicated) do
    IO.sleep ms.toUInt32
    act

/-- Kill the document's worker, answering what it left unanswered. -/
def kill (ctx : Context) (d : DocState) : IO DocState := do
  if let some w := d.worker then
    w.child.kill
  for id in d.pending do
    ctx.out.send (.response id .null)
  pure { d with worker := none, current := none, pending := #[], gen := d.gen + 1 }

/-- Mark the document as being checked by nobody and drop a worker whose
generation has passed. -/
def onWorkerExit (ctx : Context) (uri : DocumentUri) (gen : Nat) (code : UInt32) : IO Unit :=
  ctx.docs.atomically do
    if let some d := (← get)[uri]? then
      if d.gen == gen then
        IO.eprintln s!"kleenextt: worker for {uri} exited with {code}"
        modify (·.insert uri (← kill ctx { d with worker := none }))

mutual
  /-- Start a worker on the document as it currently reads. -/
  partial def spawn (ctx : Context) (uri : DocumentUri) (d : DocState) : IO DocState := do
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
    out.notify "$/kleenextt/policy" { slow := (← ctx.slow.get).toArray, forced := d.forced : PolicyParams }
    out.notify "textDocument/didOpen"
      { textDocument := { uri, languageId := "kleenextt", version := d.version, text := d.text.source }
        : DidOpenTextDocumentParams }
    pure { d with worker := some { child, out }, gen, seen := 0, current := none, pending := #[] }

  /-- Kill the worker and start over, without the commands requested in full. -/
  partial def restart (ctx : Context) (uri : DocumentUri) (d : DocState) : IO DocState := do
    spawn ctx uri { ← kill ctx d with forced := #[] }

  partial def onWorkerMessage (ctx : Context) (uri : DocumentUri) (gen : Nat) (msg : JsonRpc.Message) : IO Unit := do
    match msg with
    | .notification "$/kleenextt/command" params? =>
      let p : CommandParams ← parseParams params?
      ctx.docs.atomically do
        let some d := (← get)[uri]? | return
        unless d.gen == gen do return
        let forced := if p.command?.isNone then #[] else d.forced
        modify (·.insert uri { d with seen := max d.seen p.version, current := p.command?, forced })
        if let some c := p.command? then
          let budget ← ctx.budgetMs.get
          unless c.forced || budget == 0 do
            after budget (overBudget ctx uri gen c.hash)
    | .notification _ _ => ctx.out.send msg
    | .response id _ | .responseError id .. =>
      ctx.docs.atomically do
        if let some d := (← get)[uri]? then
          modify (·.insert uri { d with pending := d.pending.erase id })
      ctx.out.send msg
    | .request .. => pure ()

  /-- The command is still running after the budget: remember it as slow and
  start over. -/
  partial def overBudget (ctx : Context) (uri : DocumentUri) (gen : Nat) (h : Nat) : IO Unit :=
    ctx.docs.atomically do
      let some d := (← get)[uri]? | return
      unless d.gen == gen do return
      let some c := d.current | return
      unless c.hash == h && !c.forced do return
      ctx.slow.modify (·.insert h)
      modify (·.insert uri (← restart ctx uri d))
end

private def posLE (a b : Lsp.Position) : Bool :=
  a.line < b.line || (a.line == b.line && a.character ≤ b.character)

/-- Whether the change reaches the command being checked in full, which then
has to start over; a change after it can wait for it. -/
private def touches (current : Option CommandInfo) : TextDocumentContentChangeEvent → Bool
  | .rangeChange r _ => match current with
    | some c => posLE r.start c.range.end
    | none => true
  | .fullChange _ => true

def didChange (ctx : Context) (p : DidChangeTextDocumentParams) : IO Unit := do
  let uri := p.textDocument.uri
  ctx.docs.atomically do
    let some d := (← get)[uri]? | return
    let text := Lean.Server.foldDocumentChanges p.contentChanges d.text
    let version := p.textDocument.version?.getD (d.version + 1)
    let d := { d with version, text }
    match d.worker with
    | none => modify (·.insert uri (← spawn ctx uri d))
    | some w =>
      modify (·.insert uri d)
      w.out.notify "textDocument/didChange" p
      let forcedRunning := d.current.any (·.forced)
      let budget ← ctx.budgetMs.get
      unless budget == 0 || (forcedRunning && !(p.contentChanges.any (touches d.current))) do
        let gen := d.gen
        after budget <| ctx.docs.atomically do
          let some d := (← get)[uri]? | return
          unless d.gen == gen && d.seen < version do return
          modify (·.insert uri (← restart ctx uri d))

/-- Check in full up to a position, or the whole document. -/
def checkInFull (ctx : Context) (p : CheckParams) : IO Unit := do
  let uri := p.textDocument.uri
  ctx.docs.atomically do
    let some d := (← get)[uri]? | return
    let path := (pathOf uri).toString
    let (cmds, _) := parseCmds ctx.env d.text.source path
    let ictx := Parser.mkInputContext d.text.source path
    let limit := p.position?.map d.text.lspPosToUtf8Pos
    let hashes := cmds.filterMap fun c =>
      if limit.all (c.getPos?.getD 0 ≤ ·) then some (cmdHash ictx c) else none
    let forced := (Std.HashSet.ofArray (d.forced ++ hashes)).toArray
    let d := { d with forced }
    match d.worker with
    | none => modify (·.insert uri (← spawn ctx uri d))
    | some w =>
      modify (·.insert uri d)
      w.out.notify "$/kleenextt/policy" { slow := (← ctx.slow.get).toArray, forced : PolicyParams }

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

/-- `initializationOptions.timeBudget`, in seconds; `0` for none. -/
def applyInitOptions (ctx : Context) (params? : Option Json.Structured) : IO Unit := do
  let json : Json := match params? with
    | some (.obj o) => Json.obj o
    | _ => Json.null
  match json.getObjVal? "initializationOptions" with
  | .ok opts =>
    match opts.getObjVal? "timeBudget" with
    | .ok (.num n) => ctx.budgetMs.set (n.toFloat * 1000).toUInt64.toNat
    | _ => pure ()
  | _ => pure ()

/-- Until `exit` or the end of input. -/
partial def loop (ctx : Context) (inp : IO.FS.Stream) : IO Unit := do
  let msg ← try inp.readLspMessage catch _ => return
  match msg with
  | .request id "initialize" params? =>
    applyInitOptions ctx params?
    ctx.out.respond id { capabilities, serverInfo? := some { name := "kleenextt" } : InitializeResult }
  | .request id "shutdown" _ => ctx.out.send (.response id .null)
  | .request id "textDocument/definition" params? =>
    let p : TextDocumentPositionParams ← parseParams params?
    forward ctx id p.textDocument.uri msg
  | .request id "$/kleenextt/check" params? =>
    checkInFull ctx (← parseParams params?)
    ctx.out.send (.response id .null)
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
    budgetMs := ← IO.mkRef 5000
    slow := ← IO.mkRef {}
    docs := ← Std.Mutex.new {} }
  loop ctx (← IO.getStdin)
  ctx.docs.atomically do
    for (_, d) in ← get do
      discard <| kill ctx d
  pure 0

end Kleenextt.Server
