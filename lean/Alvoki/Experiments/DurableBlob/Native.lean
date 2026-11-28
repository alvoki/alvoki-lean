import Alvoki.Experiments.DurableBlob.Protocol

namespace DurableBlob
open System

@[extern "alvoki_fsync"]
opaque syncHandle (handle : @& IO.FS.Handle) : IO Unit

/-- The Linux adapter's primitive operations. `files` below is shared by
the IO binding and the filesystem-effect interpreter. -/
structure Primitives (m : Type → Type) (handle : Type) where
  openFile : FilePath → IO.FS.Mode → m handle
  write : handle → ByteArray → m Unit
  flush : handle → m Unit
  sync : handle → m Unit
  rename : FilePath → FilePath → m Unit
  read : FilePath → m ByteArray

@[inline] def Primitives.files [Monad m] (ops : Primitives m handle) (directory : FilePath)
    (syncStaged : handle → m Unit) : Files m handle :=
  let active := directory / "BLOB"
  let staged := directory / "BLOB.next"
  {
    writeStaged := fun bytes => do
      let handle ← ops.openFile staged .write
      ops.write handle bytes
      ops.flush handle
      return handle
    syncStaged
    renameStaged := ops.rename staged active
    syncDirectory := do ops.sync (← ops.openFile directory .read)
    readActive := ops.read active
  }

@[inline] def Primitives.backend [Monad m] (ops : Primitives m handle) (directory : FilePath) :
    Backend m ByteArray :=
  (ops.files directory ops.sync).backend

@[inline] private def linux : Primitives IO IO.FS.Handle :=
  ⟨IO.FS.Handle.mk, IO.FS.Handle.write, IO.FS.Handle.flush, syncHandle,
    IO.FS.rename, IO.FS.readBinFile⟩

/-- Test hooks may replace the staged sync. Production binds it to the
same fsync primitive as the directory sync. -/
def nativeFiles (directory : FilePath) (syncStaged : IO.FS.Handle → IO Unit) :
    Files IO IO.FS.Handle :=
  linux.files directory syncStaged

/-- The directory already exists durably. Its owner reserves BLOB and BLOB.next.
The active file is initialized by the caller before the first session. -/
def native (directory : FilePath) : Backend IO ByteArray :=
  linux.backend directory

/-- Keep the actual returned directory handle in the reduction of native reopen. -/
theorem native_reopen_schedule (directory : FilePath) :
    (native directory).reopen = (do
      let bytes ← IO.FS.readBinFile (directory / "BLOB")
      (do syncHandle (← IO.FS.Handle.mk directory .read))
      return bytes) := rfl

end DurableBlob
