namespace Kleenextt

/-! Evaluation counters, kept in a global reference and bumped from pure code
through an opaque identity function, for the `#ktime` command. -/

inductive Counter where
  /-- `hcomp'` past the total-face shortcut -/
  | hcomp
  /-- `transp'` past the `r = 1` shortcut -/
  | transp
  | transpGlue
  | transpHU
  | lemEq
  /-- entries into `act` -/
  | act
  /-- nodes `act` rebuilt, past the support check -/
  | actNodes
  /-- lines created -/
  | lines
  /-- line bodies computed -/
  | bodies
  /-- line instantiations -/
  | insts
  deriving Repr, Inhabited

def Counter.all : List Counter :=
  [.hcomp, .transp, .transpGlue, .transpHU, .lemEq, .act, .actNodes, .lines, .bodies, .insts]

def Counter.name : Counter → String
  | .hcomp => "hcomp"
  | .transp => "transp"
  | .transpGlue => "transpGlue"
  | .transpHU => "transpHU"
  | .lemEq => "lemEq"
  | .act => "act"
  | .actNodes => "act nodes"
  | .lines => "lines"
  | .bodies => "bodies"
  | .insts => "instantiations"

abbrev Stats := Array Nat

def Stats.empty : Stats := Array.replicate Counter.all.length 0

def Stats.pretty (s : Stats) : String :=
  ", ".intercalate <| Counter.all.mapIdx fun k c => s!"{c.name} {s.getD k 0}"

initialize statsRef : IO.Ref Stats ← IO.mkRef Stats.empty

@[noinline] unsafe def tickUnsafe {α : Type} (c : Counter) (a : α) : α :=
  unsafeBaseIO do
    statsRef.modify fun s => s.modify c.ctorIdx (· + 1)
    pure a

/-- Count one event of kind `c` on the way to `a`. -/
@[implemented_by tickUnsafe] def tick {α : Type} (_ : Counter) (a : α) : α := a

def Stats.reset : IO Unit := statsRef.set Stats.empty
def Stats.read : IO Stats := statsRef.get

end Kleenextt
