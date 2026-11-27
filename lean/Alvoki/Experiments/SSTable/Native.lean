import Alvoki.Experiments.SSTable.Core

namespace ImmutableSSTable

@[extern "alvoki_sstable_size"]
private opaque handleSize (handle : @& IO.FS.Handle) : IO Nat

@[extern "alvoki_sstable_pread"]
private opaque pread (handle : @& IO.FS.Handle) (offset : UInt64) (count : USize) : IO ByteArray

/-- Retaining the source retains the same open file across rename/unlink. Callers
    keep its contents immutable for the lifetime of any table opened on it. -/
def handleSource (handle : IO.FS.Handle) : Source (EIO String) where
  size := (handleSize handle).toEIO toString
  readAt offset count := do
    if count > 16 || offset + count > 2^63 - 1 then
      throw "SSTable read outside positional I/O bounds"
    (pread handle offset.toUInt64 count.toUSize).toEIO toString

def openNative (path : System.FilePath) : EIO String (Table (EIO String)) := do
  let handle ← (IO.FS.Handle.mk path .read).toEIO toString
  openTable (handleSource handle)

structure BuilderState where
  count : Nat := 0
  lastKey : Option UInt64 := none
  deriving Inhabited

/-- One successful push emits exactly one format row and advances its count. -/
def BuilderState.push (state : BuilderState) (row : Entry) :
    Except String (BuilderState × ByteArray) := do
  if state.count ≥ maxRows then throw "SSTable row count exceeds format limit"
  if let some prev := state.lastKey then
    if row.key ≤ prev then throw "SSTable keys must strictly increase"
  return (⟨state.count + 1, some row.key⟩, encodeEntry row)

/-- Build at a fresh path owned exclusively by the caller until return.
    Retains one entry at a time. A caught construction error removes the
    incomplete file. Crash publication and durability belong to the caller. -/
def buildFile (path : System.FilePath) (nextRow : IO (Option Entry)) : IO Nat := do
  let handle ← IO.FS.Handle.mk path .writeNew
  try
    handle.write (ByteArray.mk (Array.replicate 16 0))
    let mut state : BuilderState := {}
    while let some row ← nextRow do
      let (updated, bytes) ← IO.ofExcept (state.push row)
      handle.write bytes
      state := updated
    handle.flush
    handle.rewind
    handle.write (encodeHeader state.count)
    handle.flush
    return state.count
  catch err =>
    IO.FS.removeFile path
    throw err

end ImmutableSSTable
