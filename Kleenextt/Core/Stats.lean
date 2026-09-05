namespace Kleenextt.Core

/-! Evaluation counters in a global reference, bumped from pure code through
an opaque identity. -/

inductive Counter where
  /-- `hcomp'` past the total-face shortcut -/
  | hcomp
  /-- `hcomp'` by the type it ends at -/
  | hcompSigma
  | hcompPath
  | hcompHIT
  | hcompData
  /-- `hcompData` past the closed shortcut, with no side forced -/
  | hcompDataClosed
  | hcompGlue
  | hcompHU
  | hcompU
  | hcompStuck
  /-- `transp'` past the `r = 1` shortcut -/
  | transp
  /-- `transp'` by the type it ends at -/
  | transpSigma
  | transpPath
  | transpStuck
  | transpGlue
  | transpHU
  | lemEq
  /-- `split` on an `hcomp` at a HIT -/
  | splitHcomp
  /-- entries into `act` -/
  | act
  /-- nodes `act` rebuilt, past the support check -/
  | actNodes
  /-- `sub` nodes created -/
  | subs
  /-- `lazy` nodes created -/
  | lazies
  /-- `lazy` bodies computed -/
  | lazyBodies
  /-- `cached` nodes created -/
  | cacheds
  /-- lines created -/
  | lines
  /-- line bodies computed -/
  | bodies
  /-- line instantiations -/
  | insts
  /-- the highest level a line body was computed at: a gauge, not a count -/
  | maxLevel
  /-- the largest cofibration `frc` worked under: a gauge -/
  | maxFace
  deriving Repr, Inhabited

def Counter.all : List Counter :=
  [.hcomp, .hcompSigma, .hcompPath, .hcompHIT, .hcompData, .hcompDataClosed, .hcompGlue, .hcompHU, .hcompU, .hcompStuck,
   .transp, .transpSigma, .transpPath, .transpStuck, .transpGlue, .transpHU, .lemEq, .splitHcomp,
   .act, .actNodes, .subs, .lazies, .lazyBodies, .cacheds, .lines, .bodies, .insts, .maxLevel, .maxFace]

def Counter.name : Counter → String
  | .hcomp => "hcomp"
  | .hcompSigma => "hcomp Σ"
  | .hcompPath => "hcomp Path"
  | .hcompHIT => "hcomp HIT"
  | .hcompData => "hcomp data"
  | .hcompDataClosed => "hcomp data closed"
  | .hcompGlue => "hcomp Glue"
  | .hcompHU => "hcomp hcompU"
  | .hcompU => "hcomp U"
  | .hcompStuck => "hcomp stuck"
  | .transp => "transp"
  | .transpSigma => "transp Σ"
  | .transpPath => "transp Path"
  | .transpStuck => "transp stuck"
  | .transpGlue => "transpGlue"
  | .transpHU => "transpHU"
  | .lemEq => "lemEq"
  | .splitHcomp => "split hcomp"
  | .act => "act"
  | .actNodes => "act nodes"
  | .subs => "subs"
  | .lazies => "lazies"
  | .lazyBodies => "lazy bodies"
  | .cacheds => "cacheds"
  | .lines => "lines"
  | .bodies => "bodies"
  | .insts => "instantiations"
  | .maxLevel => "max level"
  | .maxFace => "max face"

abbrev Stats := Array Nat

def Stats.empty : Stats := Array.replicate Counter.all.length 0

def Stats.pretty (s : Stats) : String :=
  ", ".intercalate <| Counter.all.mapIdx fun k c => s!"{c.name} {s.getD k 0}"

initialize statsRef : IO.Ref Stats ← IO.mkRef Stats.empty

@[noinline] unsafe def tickUnsafe {α : Type} (c : Counter) (a : α) : α :=
  unsafeBaseIO do
    statsRef.modify fun s => s.modify c.ctorIdx (· + 1)
    pure a

@[implemented_by tickUnsafe] def tick {α : Type} (_ : Counter) (a : α) : α := a

@[noinline] unsafe def gaugeUnsafe {α : Type} (c : Counter) (n : Nat) (a : α) : α :=
  unsafeBaseIO do
    statsRef.modify fun s => s.modify c.ctorIdx (max n)
    pure a

/-- `max` into `c`. -/
@[implemented_by gaugeUnsafe] def gauge {α : Type} (_ : Counter) (_ : Nat) (a : α) : α := a

def Stats.reset : IO Unit := statsRef.set Stats.empty
def Stats.read : IO Stats := statsRef.get

/-- Resident set size in MB. -/
def residentMB : IO Nat := do
  let s ← IO.FS.readFile "/proc/self/statm"
  match s.splitOn " " with
  | _ :: pages :: _ => pure ((pages.trimAscii.toNat?.getD 0) * 4096 / 1048576)
  | _ => pure 0

end Kleenextt.Core
