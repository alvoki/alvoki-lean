import Alvoki.Storage.Disk.LockedOpenFileReads
import Alvoki.Storage.Disk.Proofs.Checkpoint.VersionedCheckpointLineage

namespace Alvoki.Storage

open Manifest
open WAL.Boundary (ReopenImage)

/-- The same locked path reports cover both formats. The extra premise
concerns only the v2 generation and indices selected by the visible manifest. -/
structure OpenPathReadReports.ObservesVersioned (reports : OpenPathReadReports) (directory : DiskDirectory)
    (before : ReopenImage) (durable : CheckpointPublication.RunFiles) : Prop
    extends OpenPathReadReports.Observes reports directory before durable where
  integrityRuns : ∀ bytes selected, before.directory.active.manifest = some bytes →
    IntegrityCheckpoint.decode bytes = .ok selected → ∀ index, index < selected.header.runCount.toNat →
      ∀ actual expected, reports.readBin (directory.file (.run selected.header.generation index)) = .ok actual →
        durable selected.header.generation index = some expected → actual = expected

/-- Construct the dual-format reader observations using the paths relative
to the same held database lock, with the original optional lookup semantics. -/
def VersionedCheckpointFileReads.ofLockedPaths {reports : OpenPathReadReports} {directory : DiskDirectory}
    {owners : DiskSession.LockOwners} {descriptor : Nat} {before : ReopenImage}
    {durable : CheckpointPublication.RunFiles} (held : owners.Owns directory descriptor)
    (observes : owners.Owns directory descriptor → reports.ObservesVersioned directory before durable) :
    VersionedCheckpointFileReads durable before.directory.active.manifest where
  toCheckpointFileReads := (observes held).toObserves.checkpointReads
  integrityRunDurable := by
    intro bytes selected manifest decoded index within value expected read stored
    change (reports.readBin (directory.file (.run selected.header.generation index))).mapError toString =
      .ok value at read
    cases reported : reports.readBin (directory.file (.run selected.header.generation index)) with
    | error => rw [reported] at read; contradiction
    | ok payload =>
      rw [reported] at read
      exact (Except.ok.inj read).symm.trans
        ((observes held).integrityRuns bytes selected manifest decoded index within payload expected reported stored)

/-- A successful lookup reports the selected manifest, including absence. -/
theorem VersionedCheckpointFileReads.ofLockedPaths_manifest_success
    {reports : OpenPathReadReports} {directory : DiskDirectory}
    {owners : DiskSession.LockOwners} {descriptor : Nat} {before : ReopenImage}
    {durable : CheckpointPublication.RunFiles} (held : owners.Owns directory descriptor)
    (observes : owners.Owns directory descriptor → reports.ObservesVersioned directory before durable)
    (success : ∃ value, reports.readOptional (directory.file .manifest) = .ok value) :
    (ofLockedPaths held observes).readManifest = .ok before.directory.active.manifest := by
  obtain ⟨value, reported⟩ := success
  let reads := ofLockedPaths held observes
  have accepted : reads.readManifest = .ok value := by
    change (reports.readOptional (directory.file .manifest)).mapError toString = .ok value
    rw [reported]
    rfl
  exact accepted.trans (congrArg Except.ok (reads.manifestVisible value accepted))

/-- A successful path report supplies the identical bytes to the run callback. -/
theorem VersionedCheckpointFileReads.ofLockedPaths_run_success
    {reports : OpenPathReadReports} {directory : DiskDirectory}
    {owners : DiskSession.LockOwners} {descriptor : Nat} {before : ReopenImage}
    {durable : CheckpointPublication.RunFiles} (held : owners.Owns directory descriptor)
    (observes : owners.Owns directory descriptor → reports.ObservesVersioned directory before durable)
    {generation : UInt64} {index : Nat} {payload : ByteArray}
    (reported : reports.readBin (directory.file (.run generation index)) = .ok payload) :
    (ofLockedPaths held observes).readRun generation index = .ok payload := by
  change (reports.readBin (directory.file (.run generation index))).mapError toString = .ok payload
  rw [reported]
  rfl

/-- Successful run reads at the selected FilePaths return the durable byte
arrays in manifest order. The same decoder selects the range for both formats. -/
theorem VersionedCheckpointFileReads.ofLockedPaths_runs_success
    {reports : OpenPathReadReports} {directory : DiskDirectory}
    {owners : DiskSession.LockOwners} {descriptor : Nat} {before : ReopenImage}
    {durable : CheckpointPublication.RunFiles} (held : owners.Owns directory descriptor)
    (observes : owners.Owns directory descriptor → reports.ObservesVersioned directory before durable)
    {bytes : ByteArray} {selected : VersionedCheckpoint} {files : List ByteArray}
    (manifest : before.directory.active.manifest = some bytes)
    (decoded : VersionedCheckpoint.decode bytes = .ok selected)
    (success : ∀ index, index < selected.header.runCount.toNat →
      ∃ payload, reports.readBin (directory.file (.run selected.header.generation index)) = .ok payload)
    (stored : (List.range selected.header.runCount.toNat).mapM (durable selected.header.generation) = some files) :
    (List.range selected.header.runCount.toNat).mapM
      ((ofLockedPaths held observes).readRun selected.header.generation) = .ok files := by
  exact (ofLockedPaths held observes).selected_runs_success manifest decoded
    (fun index within => (success index within).imp (fun _ => ofLockedPaths_run_success held observes)) stored

/-- The reports drive the shared loader to the table and generation of
the selected durable runs. Integrity checking and structural loading use
the same ordered byte arrays. -/
theorem VersionedCheckpointFileReads.ofLockedPaths_loads
    {reports : OpenPathReadReports} {directory : DiskDirectory}
    {owners : DiskSession.LockOwners} {descriptor : Nat} {before : ReopenImage}
    {durable : CheckpointPublication.RunFiles} (held : owners.Owns directory descriptor)
    (observes : owners.Owns directory descriptor → reports.ObservesVersioned directory before durable)
    {bytes : ByteArray} {selected : VersionedCheckpoint} {files : List ByteArray} {table : PackedTable}
    (manifest : before.directory.active.manifest = some bytes)
    (manifestRead : ∃ value, reports.readOptional (directory.file .manifest) = .ok value)
    (decoded : VersionedCheckpoint.decode bytes = .ok selected)
    (runReads : ∀ index, index < selected.header.runCount.toNat →
      ∃ payload, reports.readBin (directory.file (.run selected.header.generation index)) = .ok payload)
    (stored : (List.range selected.header.runCount.toNat).mapM (durable selected.header.generation) = some files)
    (checked : selected.ValidatesFiles files) (loaded : loadRunSet selected.header files = .ok table) :
    (ofLockedPaths held observes).result = .ok (some (table, selected.header.generation)) := by
  have readManifest := (ofLockedPaths_manifest_success held observes manifestRead).trans
    (congrArg Except.ok manifest)
  exact (ofLockedPaths held observes).completes_selected readManifest decoded
    (fun index within => (runReads index within).imp (fun _ => ofLockedPaths_run_success held observes))
    stored checked loaded

/-- Successful lookup of a missing manifest finishes checkpoint reading
without any run read or validation premise. -/
theorem VersionedCheckpointFileReads.ofLockedPaths_absent
    {reports : OpenPathReadReports} {directory : DiskDirectory}
    {owners : DiskSession.LockOwners} {descriptor : Nat} {before : ReopenImage}
    {durable : CheckpointPublication.RunFiles} (held : owners.Owns directory descriptor)
    (observes : owners.Owns directory descriptor → reports.ObservesVersioned directory before durable)
    (success : ∃ value, reports.readOptional (directory.file .manifest) = .ok value)
    (absent : before.directory.active.manifest = none) :
    (ofLockedPaths held observes).result = .ok none := by
  have read := (ofLockedPaths_manifest_success held observes success).trans (congrArg Except.ok absent)
  simp [VersionedCheckpointFileReads.result, readVersionedCheckpoint, read, Bind.bind, Except.bind, Pure.pure,
    Except.pure]

/-- With an absent or accepted v2 manifest, the same reported reads give
the exact checkpoint result under the strict native reader. -/
theorem VersionedCheckpointFileReads.integrityResult_eq
    {durable : CheckpointPublication.RunFiles} {binding : Option ByteArray}
    (reads : VersionedCheckpointFileReads durable binding)
    (manifestRead : reads.readManifest = .ok binding)
    (integrity : ∀ bytes, binding = some bytes →
      ∃ manifest, IntegrityCheckpoint.decode bytes = .ok manifest) :
    readIntegrityCheckpoint reads.readManifest reads.readRun id = reads.result := by
  change readIntegrityCheckpoint reads.readManifest reads.readRun id =
    readVersionedCheckpoint reads.readManifest reads.readRun id
  rw [manifestRead]
  cases binding with
  | none => exact readIntegrityCheckpoint_absent (m := Except String) reads.readRun id
  | some bytes =>
    obtain ⟨_, decoded⟩ := integrity bytes rfl
    exact readIntegrityCheckpoint_integrity (m := Except String) reads.readRun id (fun _ => rfl) decoded

end Alvoki.Storage
