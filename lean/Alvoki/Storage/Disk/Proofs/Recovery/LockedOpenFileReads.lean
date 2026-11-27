import Alvoki.Storage.Disk.Proofs.Filesystem.DiskLockLifecycle
import Alvoki.Storage.Disk.Proofs.Recovery.OptionalFileRead

namespace Alvoki.Storage

open System
open WAL.Boundary (MarkedWalReads ReopenImage)

theorem _root_.Alvoki.WAL.Boundary.observedOptional_success {read : Except IO.Error (Option ByteArray)}
    {expected : Option ByteArray} (reported : ∃ value, read = .ok value)
    (agrees : ∀ value, read.mapError toString = .ok value → value = expected) :
    read.mapError toString = .ok expected := by
  obtain ⟨value, observed⟩ := reported
  have accepted : read.mapError toString = .ok value := by rw [observed]; rfl
  rw [accepted, agrees value accepted]

/-- The primitive reports are keyed by the same full paths used by the
native adapter, including the run names chosen after manifest decoding. -/
structure OpenPathReadReports where
  lstat : FilePath → Except IO.Error IO.FS.Metadata
  readBin : FilePath → Except IO.Error ByteArray

namespace OpenPathReadReports

def readOptional (reports : OpenPathReadReports) (path : FilePath) : Except IO.Error (Option ByteArray) :=
  readOptionalDatabaseFile (pure (reports.lstat path)) (fun _ => reports.readBin path)
    (fun _ => IO.userError s!"expected a regular database file: '{path}'") Except.error

structure OptionalAgrees (reports : OpenPathReadReports) (file : FilePath) (visible : Option ByteArray) : Prop where
  missing : ∀ name error, reports.lstat file = .error (.noFileOrDirectory name 2 error) → visible = none
  contents : ∀ metadata bytes, reports.lstat file = .ok metadata → metadata.type = .file →
    reports.readBin file = .ok bytes → visible = some bytes

private def OptionalAgrees.observation {reports : OpenPathReadReports} {file : FilePath}
    {visible : Option ByteArray} (agrees : reports.OptionalAgrees file visible) : OptionalPathRead visible :=
  ⟨reports.lstat file, reports.readBin file, agrees.missing, agrees.contents⟩

/-- Interpret successful primitive reports at the actual resolved paths.
The run contract covers only files selected by the visible manifest. -/
structure Observes (reports : OpenPathReadReports) (directory : DiskDirectory)
    (before : ReopenImage) (durable : CheckpointPublication.RunFiles) : Prop where
  manifest : reports.OptionalAgrees (directory.file .manifest) before.directory.active.manifest
  marker : reports.OptionalAgrees (directory.file .walBoundary) before.directory.active.walBoundary
  wal : reports.OptionalAgrees (directory.file .wal) before.wal.active
  runs : ∀ bytes header, before.directory.active.manifest = some bytes → Manifest.decode bytes = .ok header →
    ∀ index, index < header.runCount.toNat → ∀ actual expected,
      reports.readBin (directory.file (.run header.generation index)) = .ok actual →
      durable header.generation index = some expected → actual = expected

def Observes.checkpointReads {reports : OpenPathReadReports} {directory : DiskDirectory}
    {before : ReopenImage} {durable : CheckpointPublication.RunFiles}
    (contract : reports.Observes directory before durable) :
    CheckpointFileReads durable before.directory.active.manifest :=
  .ofOptionalManifest contract.manifest.observation directory
    (fun generation index => (reports.readBin (directory.file (.run generation index))).mapError toString)
    (fun bytes header selected decoded index inRange actual expected read stored => by
      cases reported : reports.readBin (directory.file (.run header.generation index)) with
      | error => rw [reported] at read; contradiction
      | ok payload =>
        rw [reported] at read
        exact (Except.ok.inj read).symm.trans
          (contract.runs bytes header selected decoded index inRange payload expected reported stored))

def Observes.walReads {reports : OpenPathReadReports} {directory : DiskDirectory}
    {before : ReopenImage} {durable : CheckpointPublication.RunFiles}
    (contract : reports.Observes directory before durable) : MarkedWalReads before :=
  .ofOptionalFiles directory contract.marker.observation contract.wal.observation

/-- Successful reports at the held directory's selected manifest and run
paths suffice for the shared loader. Other run names need no successful
read, and an absent manifest selects no runs. -/
theorem checkpointCompletes {reports : OpenPathReadReports} {directory : DiskDirectory}
    {owners : DiskSession.LockOwners} {descriptor : Nat} {before : ReopenImage}
    {image : CheckpointPublication.Image} {files : List ByteArray} {base : PackedTable}
    (held : owners.Owns directory descriptor)
    (observes : owners.Owns directory descriptor → reports.Observes directory before image.durable)
    (manifestRead : reports.readOptional (directory.file .manifest) = .ok before.directory.active.manifest)
    (runReads : ∀ bytes header, before.directory.active.manifest = some bytes →
      Manifest.decode bytes = .ok header → ∀ index, index < header.runCount.toNat →
        ∃ payload, reports.readBin (directory.file (.run header.generation index)) = .ok payload)
    (durable : image.readDurableCheckpointRuns before.directory.active.manifest = some files)
    (loaded : (match before.directory.active.manifest with
      | none => Except.ok PackedTable.empty
      | some bytes => do let header ← Manifest.decode bytes; loadRunSet header files) = .ok base) :
    ∃ result, (observes held).checkpointReads.result = .ok result ∧ (result.getD (.empty, 0)).1 = base := by
  apply CheckpointReadObservations.completes (image := image) (observes held).checkpointReads _ _ durable loaded
  · change (reports.readOptional (directory.file .manifest)).mapError toString = .ok _
    rw [manifestRead]
    rfl
  · intro bytes header selected decoded index inRange
    obtain ⟨payload, read⟩ := runReads bytes header selected decoded index inRange
    refine ⟨payload, ?_⟩
    change (reports.readBin (directory.file (.run header.generation index))).mapError toString = .ok payload
    rw [read]
    rfl

end OpenPathReadReports

end Alvoki.Storage
