import Lean.CompactedRegion
import Kleenextt.Core

/-! Checked commands on disk, by hash: `$XDG_CACHE_HOME/kleenextt`, or
`~/.cache/kleenextt`, one compacted region per key, the format of `.olean`
files, so sharing within a term is kept and a file is mapped rather than
parsed. A mapped region stays for the life of the process. Keys are seeded
by the binary, since the layout of what is stored is the binary's. -/

namespace Kleenextt.Cache

open Lean

/-- The cache directory, created; `none` when there is no home. -/
def dir : IO (Option System.FilePath) := do
  let base ← match ← IO.getEnv "XDG_CACHE_HOME" with
    | some d => pure (some (System.FilePath.mk d))
    | none => pure ((← IO.getEnv "HOME").map (System.FilePath.mk · / ".cache"))
  let some base := base | return none
  let d := base / "kleenextt"
  try
    IO.FS.createDirAll d
    pure (some d)
  catch _ => pure none

/-- A hash of the running binary's identity, to seed keys with. -/
def seed : IO UInt64 := do
  try
    let m ← (← IO.appPath).metadata
    pure (mixHash (hash m.byteSize) (hash m.modified.sec))
  catch _ => pure 7

def name (key : UInt64) : String :=
  String.ofList (Nat.toDigits 16 key.toNat)

def file (d : System.FilePath) (key : UInt64) : System.FilePath :=
  d / (name key ++ ".ktc")

/-- A missing or unreadable entry is a miss. -/
unsafe def readUnsafe (α : Type) (d : System.FilePath) (key : UInt64) : IO (Option α) := do
  try
    let (a, _) ← CompactedRegion.read (α := α) (file d key) #[]
    pure (some a)
  catch _ => pure none

/-- The value saved under `key` by `write` at the same type, else `none`. -/
@[implemented_by readUnsafe]
opaque read (α : Type) (d : System.FilePath) (key : UInt64) : IO (Option α) :=
  pure none

/-- Written whole, then moved into place, so a reader never sees a part. -/
unsafe def writeUnsafe {α : Type} (d : System.FilePath) (key : UInt64) (a : α) : IO Unit := do
  try
    let target := file d key
    let tmp := target.addExtension s!"{← IO.Process.getPID}.tmp"
    discard <| CompactedRegion.save (α := α) tmp (Name.mkSimple (name key)) a #[] none
    IO.FS.rename tmp target
  catch e => IO.eprintln s!"kleenextt: cache write failed: {e}"

@[implemented_by writeUnsafe]
opaque write {α : Type} (d : System.FilePath) (key : UInt64) (a : α) : IO Unit :=
  pure ()

end Kleenextt.Cache
