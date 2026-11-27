import Alvoki.Experiments.DurableBlob.Contract
import Alvoki.Storage.Publication.DiskPublication

namespace DurableBlob
open Alvoki.Storage

/-- The staging operations refer to one private file in the active file's
directory. Reading is exact or fails. The caller owns both names. -/
structure Files (m : Type → Type) where
  writeStaged : ByteArray → m Unit
  syncStaged : m Unit
  renameStaged : m Unit
  syncDirectory : m Unit
  readActive : m ByteArray

def Files.perform (files : Files m) (bytes : ByteArray) : Publication.Step → m Unit
  | .writeStaged => files.writeStaged bytes
  | .syncStaged => files.syncStaged
  | .renameStaged => files.renameStaged
  | .syncDirectory => files.syncDirectory

def Files.backend [Monad m] (files : Files m) : Backend m ByteArray where
  publish bytes := Publication.run (files.perform bytes)
  reopen := do
    let bytes ← files.readActive
    files.syncDirectory
    return bytes

end DurableBlob
