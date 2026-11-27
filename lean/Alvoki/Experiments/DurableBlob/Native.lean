import Alvoki.Experiments.DurableBlob.Protocol

namespace DurableBlob
open System

@[extern "alvoki_fsync"]
private opaque syncHandle (handle : @& IO.FS.Handle) : IO Unit

/-- Bind the Linux file operations to the protocol. The staged sync receives
the exact handle that performed the write and flush. -/
def nativeFiles (directory : FilePath) (syncStaged : IO.FS.Handle → IO Unit) :
    Files IO IO.FS.Handle :=
  let active := directory / "BLOB"
  let staged := directory / "BLOB.next"
  {
    writeStaged := fun bytes => do
      let handle ← IO.FS.Handle.mk staged .write
      handle.write bytes
      handle.flush
      return handle
    syncStaged
    renameStaged := IO.FS.rename staged active
    syncDirectory := do syncHandle (← IO.FS.Handle.mk directory .read)
    readActive := IO.FS.readBinFile active
  }

/-- The directory already exists durably. Its owner reserves BLOB and BLOB.next.
The active file is initialized by the caller before the first session. -/
def native (directory : FilePath) : Backend IO ByteArray :=
  (nativeFiles directory syncHandle).backend

end DurableBlob
