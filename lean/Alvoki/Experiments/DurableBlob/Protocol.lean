import Alvoki.Experiments.DurableBlob.Contract

namespace DurableBlob

/-- The staging operations refer to one private file in the active file's
directory. Reading is exact or fails. The caller owns both names. -/
structure Files (m : Type → Type) (stage : Type) where
  writeStaged : ByteArray → m stage
  syncStaged : stage → m Unit
  renameStaged : m Unit
  syncDirectory : m Unit
  readActive : m ByteArray

/-- The staged writer is carried directly from the write to its barrier. -/
@[inline] def publishWith [Monad m] (writeStaged : m stage) (syncStaged : stage → m Unit)
    (renameStaged syncDirectory : m Unit) : m Unit := do
  let staged ← writeStaged
  syncStaged staged
  renameStaged
  syncDirectory

def Files.backend [Monad m] (files : Files m stage) : Backend m ByteArray where
  publish bytes := publishWith (files.writeStaged bytes) files.syncStaged files.renameStaged files.syncDirectory
  reopen := do
    let bytes ← files.readActive
    files.syncDirectory
    return bytes

end DurableBlob
