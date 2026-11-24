import Alvoki.Storage.Disk.CheckpointRead
import Alvoki.Storage.Disk.ManifestIntegrity

namespace Alvoki.Storage
open Manifest

def checkpointIntegrityMismatch : String := "checkpoint run integrity mismatch"

/-- Check integrity and structure on the same ordered run bytes. -/
def loadIntegrityRunSet (manifest : IntegrityCheckpoint) (files : List ByteArray) : Except String PackedTable :=
  if manifest.validateRuns files then loadRunSet manifest.header files
  else .error checkpointIntegrityMismatch

theorem loadIntegrityRunSet_iff {manifest : IntegrityCheckpoint} {files : List ByteArray} {table : PackedTable} :
    loadIntegrityRunSet manifest files = .ok table ↔
      manifest.validateRuns files = true ∧ loadRunSet manifest.header files = .ok table := by
  simp [loadIntegrityRunSet]
  split <;> simp_all

/-- Read a v2 manifest and the exact run paths it selects. Report absence
before run reads, and finish validation before the caller can use the
checkpoint's watermark to replay the WAL. -/
@[macro_inline] def readIntegrityCheckpoint [Monad m] (readManifest : m (Option ByteArray))
    (readRun : UInt64 → Nat → m ByteArray) (validate : {α : Type} → Except String α → m α) :
    m (Option (PackedTable × UInt64)) := do
  let some bytes ← readManifest | return none
  let manifest ← validate (IntegrityCheckpoint.decode bytes)
  let files ← readCheckpointRunBytes readRun manifest.header
  let table ← validate (loadIntegrityRunSet manifest files)
  return some (table, manifest.header.generation)

/-- A rejected manifest stops before both run reads and the open continuation. -/
theorem readIntegrityCheckpoint_decode_error {bytes : ByteArray} {cause : String}
    (decoded : IntegrityCheckpoint.decode bytes = .error cause)
    (readRun : UInt64 → Nat → Except String ByteArray) (resume : Option (PackedTable × UInt64) → Except String α) :
    (readIntegrityCheckpoint (.ok (some bytes)) readRun id >>= resume) = .error cause := by
  simp [readIntegrityCheckpoint, decoded, bind, Except.bind]

end Alvoki.Storage
