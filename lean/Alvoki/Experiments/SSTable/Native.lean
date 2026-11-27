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
    if count > maxRowSize || offset + count > maxFileSize then
      throw "SSTable read outside positional I/O bounds"
    (pread handle offset.toUInt64 count.toUSize).toEIO toString

@[extern "alvoki_fsync"]
private opaque syncHandle (handle : @& IO.FS.Handle) : IO Unit

/-- Sync file contents through an already flushed output handle. -/
def syncFileHandle (handle : IO.FS.Handle) : IO Unit := syncHandle handle

/-- Own a fresh output path through build, flush and sync. The writer must
flush the complete image before returning. Callbacks must leave the name
unchanged and must not retain the handle. -/
def withFreshOutput (path : System.FilePath) (writeImage : IO.FS.Handle → IO Nat)
    (syncOutput : IO.FS.Handle → IO Unit) : IO Nat := do
  let handle ← IO.FS.Handle.mk path .writeNew
  try
    let count ← writeImage handle
    syncOutput handle
    return count
  catch err =>
    try IO.FS.removeFile path catch _ => pure ()
    throw err

end ImmutableSSTable
