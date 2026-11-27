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

/-- Local operations for one exclusively owned output file. The schedule
uses the description returned by the exclusive open for all file mutations. -/
structure OutputOps (m : Type → Type) (handle : Type) where
  openFile : System.FilePath → IO.FS.Mode → m handle
  append : handle → ByteArray → m Unit
  flush : handle → m Unit
  sync : handle → m Unit
  remove : System.FilePath → m Unit

@[inline] def OutputOps.sink (ops : OutputOps m handle) (output : handle) : Sink m :=
  ⟨ops.append output, ops.flush output⟩

/-- Own a fresh output path through build, flush and sync. The writer must
flush the complete image before returning. Callbacks leave the name unchanged
and do not retain the handle. Cleanup preserves the primary error. -/
@[inline] def withFreshOutputWith [Monad m] [MonadExceptOf ε m] (ops : OutputOps m handle)
    (path : System.FilePath) (writeImage : handle → m Nat) : m Nat := do
  let handle ← ops.openFile path .writeNew
  let writeAndSync : m Nat := do
    let count ← writeImage handle
    ops.sync handle
    return count
  tryCatchThe ε writeAndSync fun error => do
    tryCatchThe ε (ops.remove path) (fun _ => pure ())
    throwThe ε error

@[inline] def nativeOutputOps (syncOutput : IO.FS.Handle → IO Unit) : OutputOps IO IO.FS.Handle :=
  ⟨IO.FS.Handle.mk, IO.FS.Handle.write, IO.FS.Handle.flush, syncOutput, IO.FS.removeFile⟩

end ImmutableSSTable
