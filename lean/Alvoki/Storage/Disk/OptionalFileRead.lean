import Alvoki.Storage.Disk.DiskRecoveryModel

namespace Alvoki.Storage
open System

/-- Primitive results from the stable, engine-owned directory. The lstat
ENOENT and regular-file read premises state the locked namespace contract. -/
structure OptionalPathRead (visible : Option ByteArray) where
  lookup : Except IO.Error IO.FS.Metadata
  read : Except IO.Error ByteArray
  missing : ∀ name message, lookup = .error (.noFileOrDirectory name 2 message) → visible = none
  contents : ∀ metadata bytes, lookup = .ok metadata → metadata.type = .file →
    read = .ok bytes → visible = some bytes

def OptionalPathRead.result {visible : Option ByteArray} (observed : OptionalPathRead visible)
    (path : FilePath) : Except IO.Error (Option ByteArray) :=
  readOptionalDatabaseFile (pure observed.lookup) (fun _ => observed.read)
    (fun _ => IO.userError s!"expected a regular database file: '{path}'") Except.error

/-- A successful absent read only comes from ENOENT at the entry lookup. A
read error after successful lstat, including ENOENT, is still an error. -/
theorem OptionalPathRead.resultVisible {visible : Option ByteArray} (observed : OptionalPathRead visible)
    (path : FilePath) {value : Option ByteArray} (accepted : observed.result path = .ok value) :
    visible = value := by
  unfold result readOptionalDatabaseFile readOptionalDatabaseFileWithMetadata at accepted
  cases lookup : observed.lookup with
  | ok metadata =>
    cases regular : metadata.type == .file
    · simp [lookup, regular, Pure.pure, Bind.bind, Except.pure, Except.bind] at accepted
    · cases readResult : observed.read with
      | error error =>
        simp [lookup, regular, readResult, Pure.pure, Bind.bind, Except.pure, Except.bind] at accepted
      | ok bytes =>
        have regularFile : metadata.type = .file := by
          cases kind : metadata.type <;> first | rfl | (rw [kind] at regular; cases regular)
        have observedValue : some bytes = value := by
          simpa [lookup, regular, readResult, Pure.pure, Bind.bind, Except.pure, Except.bind] using accepted
        exact (observed.contents _ _ lookup regularFile readResult).trans observedValue
  | error error =>
    cases error <;> simp [lookup, Pure.pure, Bind.bind, Except.pure, Except.bind] at accepted
    rename_i name code message
    split at accepted
    · rename_i isMissing
      subst code
      exact (observed.missing _ _ lookup).trans (Except.ok.inj accepted)
    · contradiction

private theorem OptionalPathRead.resultVisibleString {visible : Option ByteArray}
    (observed : OptionalPathRead visible) (path : FilePath) {value : Option ByteArray}
    (accepted : (observed.result path).mapError toString = .ok value) : visible = value := by
  cases result : observed.result path with
  | error error => rw [result] at accepted; contradiction
  | ok found =>
    rw [result] at accepted
    exact (observed.resultVisible path result).trans (Except.ok.inj accepted)

def CheckpointFileReads.ofOptionalManifest {durable : CheckpointPublication.RunFiles}
    {active : Option ByteArray} (manifest : OptionalPathRead active) (directory : DiskDirectory)
    (runs : UInt64 → Nat → Except String ByteArray)
    (runVisible : ∀ bytes header, active = some bytes → Manifest.decode bytes = .ok header →
      ∀ index, index < header.runCount.toNat → ∀ value expected,
        runs header.generation index = .ok value → durable header.generation index = some expected →
        value = expected) :
    CheckpointFileReads durable active :=
  ⟨(manifest.result (directory.file .manifest)).mapError toString, runs,
    fun _ accepted => (manifest.resultVisibleString _ accepted).symm, runVisible⟩

end Alvoki.Storage

namespace Alvoki.WAL.Boundary
open Storage

def MarkedWalReads.ofOptionalFiles {before : ReopenImage} (directory : DiskDirectory)
    (marker : OptionalPathRead before.directory.active.walBoundary) (wal : OptionalPathRead before.wal.active) :
    MarkedWalReads before :=
  ⟨(marker.result (directory.file .walBoundary)).mapError toString,
    (wal.result (directory.file .wal)).mapError toString,
    fun _ accepted => marker.resultVisibleString _ accepted,
    fun _ accepted => wal.resultVisibleString _ accepted⟩

end Alvoki.WAL.Boundary
