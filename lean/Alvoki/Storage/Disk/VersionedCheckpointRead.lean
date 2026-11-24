import Alvoki.Storage.Disk.DiskRecoveryModel
import Alvoki.Storage.Disk.ManifestIntegrity

namespace Alvoki.Storage
open Manifest

def checkpointIntegrityMismatch : String := "checkpoint run integrity mismatch"

/-- Use the same ordered files for integrity checking and structural
loading. V1 continues to use the original structural loader. -/
def loadVersionedRunSet (manifest : VersionedCheckpoint) (files : List ByteArray) : Except String PackedTable :=
  match manifest with
  | .legacy header => loadRunSet header files
  | .integrity manifest =>
    if manifest.validateRuns files then loadRunSet manifest.header files
    else .error checkpointIntegrityMismatch

theorem loadVersionedRunSet_integrity_iff {manifest : IntegrityCheckpoint} {files : List ByteArray}
    {table : PackedTable} : loadVersionedRunSet (.integrity manifest) files = .ok table ↔
      manifest.validateRuns files = true ∧ loadRunSet manifest.header files = .ok table := by
  simp [loadVersionedRunSet]
  split <;> simp_all

theorem loadVersionedRunSet_fromRuns {header : Checkpoint} {files : List ByteArray} {table : PackedTable}
    (loaded : loadRunSet header files = .ok table) (count : files.length = header.runCount.toNat)
    (fits : ∀ bytes ∈ files, bytes.size < UInt64.size) :
    loadVersionedRunSet (.integrity (IntegrityCheckpoint.fromRuns header files)) files = .ok table :=
  loadVersionedRunSet_integrity_iff.mpr ⟨IntegrityCheckpoint.validateRuns_fromRuns header files count fits, loaded⟩

/-- Decode the manifest, read its run paths with the existing ordered loop,
and return the checkpoint used by WAL recovery only after validation. -/
@[macro_inline] def readVersionedCheckpoint [Monad m] (readManifest : m (Option ByteArray))
    (readRun : UInt64 → Nat → m ByteArray) (validate : {α : Type} → Except String α → m α) :
    m (Option (PackedTable × UInt64)) := do
  let some bytes ← readManifest | return none
  let manifest ← validate (VersionedCheckpoint.decode bytes)
  let files ← readCheckpointRunBytes readRun manifest.header
  let table ← validate (loadVersionedRunSet manifest files)
  return some (table, manifest.header.generation)

theorem readVersionedCheckpoint_absent [Monad m] [LawfulMonad m] (readRun : UInt64 → Nat → m ByteArray)
    (validate : {α : Type} → Except String α → m α) :
    readVersionedCheckpoint (pure none) readRun validate = readCheckpoint (pure none) readRun validate := by
  simp [readVersionedCheckpoint, readCheckpoint]

/-- After a successful manifest read and v1 decode, both readers perform
the same run read actions and validate the same structural load result. -/
theorem readVersionedCheckpoint_legacy [Monad m] [LawfulMonad m] (readRun : UInt64 → Nat → m ByteArray)
    (validate : {α : Type} → Except String α → m α)
    (accepts : ∀ {α : Type} (value : α), validate (.ok value) = pure value)
    {bytes : ByteArray} {header : Checkpoint} (decoded : Manifest.decode bytes = .ok header) :
    readVersionedCheckpoint (pure (some bytes)) readRun validate =
      readCheckpoint (pure (some bytes)) readRun validate := by
  simp [readVersionedCheckpoint, readCheckpoint, VersionedCheckpoint.decode_legacy decoded,
    decoded, accepts, VersionedCheckpoint.header, loadVersionedRunSet]

theorem readVersionedCheckpoint_legacy_io (readRun : UInt64 → Nat → IO ByteArray)
    {bytes : ByteArray} {header : Checkpoint} (decoded : Manifest.decode bytes = .ok header) :
    readVersionedCheckpoint (pure (some bytes)) readRun IO.ofExcept =
      readCheckpoint (pure (some bytes)) readRun IO.ofExcept := by
  have pureThen {α β : Type} (value : α) (resume : α → IO β) :
      ((pure value : IO α) >>= resume) = resume value := rfl
  simp only [readVersionedCheckpoint, readCheckpoint, pureThen, VersionedCheckpoint.decode_legacy decoded,
    decoded, IO.ofExcept, VersionedCheckpoint.header, loadVersionedRunSet]

private theorem readVersionedCheckpoint_integrity_step
    {readManifest : Except String (Option ByteArray)} (readRun : UInt64 → Nat → Except String ByteArray)
    {bytes : ByteArray} {manifest : IntegrityCheckpoint}
    (visible : readManifest = .ok (some bytes)) (decoded : IntegrityCheckpoint.decode bytes = .ok manifest) :
    readVersionedCheckpoint readManifest readRun id = (do
      let files ← (List.range manifest.header.runCount.toNat).mapM (readRun manifest.header.generation)
      let table ← loadVersionedRunSet (.integrity manifest) files
      return some (table, manifest.header.generation)) := by
  simp [readVersionedCheckpoint, visible, VersionedCheckpoint.decode_integrity decoded,
    VersionedCheckpoint.header, readCheckpointRunBytes_eq_mapM, bind, Except.bind]

/-- A successful v2 load identifies the bytes returned by the ordered
read loop. The integrity table was checked on those bytes before the
structural loader supplied the table and generation. -/
theorem readVersionedCheckpoint_integrity_observed
    {readManifest : Except String (Option ByteArray)} {readRun : UInt64 → Nat → Except String ByteArray}
    {bytes : ByteArray} {manifest : IntegrityCheckpoint}
    (visible : readManifest = .ok (some bytes)) (decoded : IntegrityCheckpoint.decode bytes = .ok manifest)
    {table : PackedTable} {generation : UInt64}
    (opened : readVersionedCheckpoint readManifest readRun id = .ok (some (table, generation))) :
    ∃ files, (List.range manifest.header.runCount.toNat).mapM (readRun manifest.header.generation) = .ok files ∧
      manifest.validateRuns files = true ∧ loadRunSet manifest.header files = .ok table ∧
      generation = manifest.header.generation := by
  rw [readVersionedCheckpoint_integrity_step readRun visible decoded] at opened
  cases readFiles : (List.range manifest.header.runCount.toNat).mapM (readRun manifest.header.generation) with
  | error message => rw [readFiles] at opened; contradiction
  | ok files =>
    rw [readFiles] at opened
    change (loadVersionedRunSet (.integrity manifest) files).map
      (fun loaded => some (loaded, manifest.header.generation)) = .ok (some (table, generation)) at opened
    cases loaded : loadVersionedRunSet (.integrity manifest) files with
    | error message => rw [loaded] at opened; contradiction
    | ok result =>
      rw [loaded] at opened
      have installed := Option.some.inj (Except.ok.inj opened)
      have ⟨checked, structural⟩ := loadVersionedRunSet_integrity_iff.mp loaded
      cases installed
      exact ⟨files, rfl, checked, structural, rfl⟩

/-- A v2 integrity mismatch stops the entire open continuation. In
particular the checkpoint table cannot supply a watermark to WAL replay. -/
theorem readVersionedCheckpoint_integrity_rejects
    {readManifest : Except String (Option ByteArray)} {readRun : UInt64 → Nat → Except String ByteArray}
    {bytes : ByteArray} {manifest : IntegrityCheckpoint} {files : List ByteArray}
    (visible : readManifest = .ok (some bytes)) (decoded : IntegrityCheckpoint.decode bytes = .ok manifest)
    (observed : (List.range manifest.header.runCount.toNat).mapM (readRun manifest.header.generation) = .ok files)
    (invalid : manifest.validateRuns files = false)
    (resume : Option (PackedTable × UInt64) → Except String α) :
    (readVersionedCheckpoint readManifest readRun id >>= resume) = .error checkpointIntegrityMismatch := by
  rw [readVersionedCheckpoint_integrity_step readRun visible decoded, observed]
  simp [loadVersionedRunSet, invalid, bind, Except.bind]

end Alvoki.Storage
