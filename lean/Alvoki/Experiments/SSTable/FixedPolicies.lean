import Alvoki.Experiments.SSTable.FixedReader

namespace ImmutableSSTable.Fixed

/-- Eager checks all blocks at open and still verifies subsequently loaded bytes.
Skip retains footer and size checks but disables data checksums. -/
inductive Validation where
  | lazy
  | eager
  | skip
  deriving DecidableEq

def openWithValidation [Monad m] [MonadExceptOf String m] (source : Source m)
    (validation : Validation) : m (Layout × Nat) := do
  let (layout, count) ← openLayout source
  if validation = .eager then
    for block in [:layout.blockCount count] do
      discard <| readBlock source layout count block
  return (layout, count)

def readBlockWithValidation [Monad m] [MonadExceptOf String m] (source : Source m)
    (validation : Validation) (layout : Layout) (count block : Nat) : m ByteArray := do
  if validation != .skip then
    readBlock source layout count block
  else
    let rows := layout.blockRows count block
    unless 0 < rows do throw "fixed SSTable block out of bounds"
    let size := layout.blockReadSize count block
    let bytes ← source.readAt (layout.blockOffset block) size
    unless bytes.size = size do throw "invalid SSTable block size"
    return bytes.extract 0 (rows * layout.rowWidth)

/-- Compare rows with one block retained for the duration of the lookup.
The final exact-match probe shares the same buffer. -/
def lookupWithReuse [Monad m] [MonadExceptOf String m] (source : Source m)
    (validation : Validation) (layout : Layout) (count : Nat) (key : ByteArray) :
    m (Option ByteArray) := do
  let read : Nat → StateT (Option (Nat × ByteArray)) m Entry := fun index => do
    let block := index / layout.rowsPerBlock
    let payload ← match ← get with
      | some (previous, bytes) =>
        if previous = block then pure bytes
        else load block
      | none => load block
    return readRow layout payload (index % layout.rowsPerBlock)
  let table := Table.ofReader count read
  return (← (table.lookup key).run none).1
where
  load (block : Nat) : StateT (Option (Nat × ByteArray)) m ByteArray := do
    let bytes ← liftM (readBlockWithValidation source validation layout count block)
    set (some (block, bytes))
    return bytes

end ImmutableSSTable.Fixed
