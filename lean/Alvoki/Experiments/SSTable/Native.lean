import Alvoki.Experiments.SSTable.Builder

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
    if count > rowSize || offset + count > 2^63 - 1 then
      throw "SSTable read outside positional I/O bounds"
    (pread handle offset.toUInt64 count.toUSize).toEIO toString

def openNative (path : System.FilePath) : EIO String (Table (EIO String)) := do
  let handle ← (IO.FS.Handle.mk path .read).toEIO toString
  openTable (handleSource handle)

/-- Build at a fresh path owned exclusively by the caller until return.
    Retains one entry at a time. After acquiring the handle, a caught error triggers
    best-effort removal of the incomplete file. Crash publication and durability belong to the caller. -/
def buildFile (path : System.FilePath) (nextRow : IO (Option Entry)) : IO Nat := do
  let handle ← IO.FS.Handle.mk path .writeNew
  try
    buildStream ⟨handle.write, handle.flush, handle.rewind⟩ nextRow IO.userError
  catch err =>
    try IO.FS.removeFile path catch _ => pure ()
    throw err

end ImmutableSSTable
