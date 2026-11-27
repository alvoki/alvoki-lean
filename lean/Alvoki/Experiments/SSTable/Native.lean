import Alvoki.Experiments.SSTable.Core

namespace ImmutableSSTable

@[extern "alvoki_sstable_size"]
private opaque handleSize (handle : @& IO.FS.Handle) : IO Nat

@[extern "alvoki_sstable_pread"]
private opaque pread (handle : @& IO.FS.Handle) (offset : UInt64) (count : USize) : IO ByteArray

/-- The read adapter acquires a file once and uses its description for both
    its extent and all subsequent positional reads. -/
structure ReadPrimitives (m : Type → Type) (handle : Type) where
  openFile : System.FilePath → IO.FS.Mode → m handle
  size : handle → m Nat
  pread : handle → UInt64 → USize → m ByteArray

@[inline] def ReadPrimitives.source [Monad m] [MonadExceptOf String m]
    (ops : ReadPrimitives m handle) (held : handle) : Source m where
  size := ops.size held
  readAt offset count := do
    if count > maxRowSize || offset + count > maxFileSize then
      throw "SSTable read outside positional I/O bounds"
    ops.pread held offset.toUInt64 count.toUSize

@[inline] def nativeReadPrimitives : ReadPrimitives (EIO String) IO.FS.Handle where
  openFile path mode := (IO.FS.Handle.mk path mode).toEIO toString
  size held := (handleSize held).toEIO toString
  pread held offset count := (pread held offset count).toEIO toString

/-- Retaining the source retains the same open file across rename/unlink. Callers
    keep its contents immutable for the lifetime of any table opened on it. -/
def handleSource (handle : IO.FS.Handle) : Source (EIO String) :=
  nativeReadPrimitives.source handle

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
