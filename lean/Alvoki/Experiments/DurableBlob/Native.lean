import Alvoki.Experiments.DurableBlob.Protocol

namespace DurableBlob
open System

@[extern "alvoki_fsync"]
private opaque syncHandle (handle : @& IO.FS.Handle) : IO Unit

/-- The directory already exists durably. Its owner reserves BLOB and BLOB.next.
The active file is initialized by the caller before the first session. -/
def native (directory : FilePath) : Backend IO ByteArray :=
  let active := directory / "BLOB"
  let staged := directory / "BLOB.next"
  Files.backend {
    writeStaged := fun bytes => do
      let handle ← IO.FS.Handle.mk staged .write
      handle.write bytes
      handle.flush
    syncStaged := do syncHandle (← IO.FS.Handle.mk staged .read)
    renameStaged := IO.FS.rename staged active
    syncDirectory := do syncHandle (← IO.FS.Handle.mk directory .read)
    readActive := IO.FS.readBinFile active
  }

end DurableBlob
