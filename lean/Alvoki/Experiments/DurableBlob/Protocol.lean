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

def Files.backend [Monad m] (files : Files m stage) : Backend m ByteArray where
  publish bytes := do
    let staged ← files.writeStaged bytes
    files.syncStaged staged
    files.renameStaged
    files.syncDirectory
  reopen := do
    let bytes ← files.readActive
    files.syncDirectory
    return bytes

end DurableBlob
