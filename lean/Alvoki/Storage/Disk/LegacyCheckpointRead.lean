import Alvoki.Storage.Disk.CheckpointRead
import Alvoki.Storage.Disk.LegacyManifest

namespace Alvoki.Storage

/-- The v1 reader used by the original checkpoint and replay models. The
strict native open path uses `readIntegrityCheckpoint`. -/
@[inline] def readCheckpoint [Monad m] (readManifest : m (Option ByteArray))
    (readRun : UInt64 → Nat → m ByteArray) (validate : {α : Type} → Except String α → m α) :
    m (Option (PackedTable × UInt64)) := do
  let some header ← readManifest | return none
  let manifest ← validate (Manifest.decode header)
  let files ← readCheckpointRunBytes readRun manifest
  let table ← validate (loadRunSet manifest files)
  return some (table, manifest.generation)

end Alvoki.Storage
