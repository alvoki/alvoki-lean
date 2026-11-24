import Alvoki.Storage.Disk.VersionedReadyWriter

namespace Alvoki.WAL.Boundary

open Storage

/-- When the empty database is opened under the canonical lock after any
admitted bootstrap cuts, the strict checkpoint reader sees an absent
manifest. The shared installer returns the first ready writer with empty
history and the acquired lock. -/
theorem ObservedMarkedState.VersionedReady.bootstrapWithLock
    {initial before : ReopenImage} (fresh : initial.Fresh) (attempts : EmptyBootstrapAttempts initial before)
    {directory : DiskDirectory} {descriptor : Nat} {owners : DiskSession.LockOwners}
    (acquisition : DiskSession.TryLockObserves owners directory (.ok true))
    {paths : OpenPathReadReports} {durable : CheckpointPublication.RunFiles}
    (observes : (owners.set (directory.file .lock) (some descriptor)).Owns directory descriptor →
      paths.ObservesVersioned directory before durable)
    (manifestRead : ∃ value, paths.readOptional (directory.file .manifest) = .ok value)
    {marker wal : Option ByteArray}
    (markerRead : paths.readOptional (directory.file .walBoundary) = .ok marker)
    (walRead : paths.readOptional (directory.file .wal) = .ok wal)
    (reports : FreshOpenReports) (created : wal = none → reports.createWal = .ok ())
    (synced : reports.syncWalDirectory = .ok ())
    (published : marker = none → ∀ step, reports.marker step = .ok ())
    (unlock : DiskSession.UnlockReport) (cause : String → IO.Error) :
    let heldOwners := owners.set (directory.file .lock) (some descriptor)
    let held : heldOwners.Owns directory descriptor := by
      simp [heldOwners, DiskSession.LockOwners.Owns, DiskSession.LockOwners.set]
    let reads := VersionedCheckpointFileReads.ofLockedPaths held observes
    let walReads := (observes held).toObserves.walReads
    let checkpoint := readIntegrityCheckpoint reads.readManifest reads.readRun id
    let reopened := (runFreshMarkedOpen checkpoint walReads.marker walReads.wal reports).run before
    ∃ state : ObservedMarkedState,
      DiskSession.runOpen directory descriptor (.ok true) (reopened.mapError cause) unlock owners =
        .ok ((state.writer.table, state.generation, state.writer.walBytes), state.writer.image) heldOwners ∧
      owners (directory.file .lock) = none ∧ heldOwners.Owns directory descriptor ∧
      MarkedWriterState.observeReopen state.writer.table state.writer.image = some state.writer ∧
      state.VersionedReady ∧ state.HasIntegrityManifest ∧
      state.writer.history = [] ∧ state.writer.table = .empty ∧ state.generation = 0 ∧
      state.durable = durable := by
  intro heldOwners held reads walReads checkpoint reopened
  have valid := attempts.valid fresh
  have missing : before.directory.active.manifest = none := valid.metadata.activeValid.1
  have observedManifest : reads.readManifest = .ok none :=
    (VersionedCheckpointFileReads.ofLockedPaths_manifest_success held observes manifestRead).trans
      (congrArg Except.ok missing)
  have observedMarker : walReads.marker = .ok marker := by
    change (paths.readOptional (directory.file .walBoundary)).mapError toString = .ok marker
    rw [markerRead]
    rfl
  have observedWal : walReads.wal = .ok wal := by
    change (paths.readOptional (directory.file .wal)).mapError toString = .ok wal
    rw [walRead]
    rfl
  let image : CheckpointPublication.Image := ⟨before.directory.project .manifest, durable⟩
  obtain ⟨after, fixed, ran, ready, absent, _, _, refined, represented, _⟩ :=
    emptyBootstrapOpen_ready (checkpointImage := image) valid reads.toCheckpointFileReads walReads
      observedManifest observedMarker observedWal reports created synced published
  have strict : checkpoint = reads.toCheckpointFileReads.result := by
    change readIntegrityCheckpoint reads.readManifest reads.readRun id =
      readCheckpoint reads.readManifest reads.readRun id
    rw [observedManifest]
    rfl
  let state : ObservedMarkedState := ⟨⟨.empty, 0, after, []⟩, 0, durable⟩
  have opened : reopened = .ok ((state.writer.table, state.generation, state.writer.walBytes), state.writer.image) := by
    simpa only [reopened, strict] using ran
  have installed : DiskSession.runOpen directory descriptor (.ok true) (reopened.mapError cause) unlock owners =
      .ok ((state.writer.table, state.generation, state.writer.walBytes), state.writer.image) heldOwners := by
    rw [opened]
    rfl
  obtain ⟨available, _, _, _⟩ := DiskSession.runOpen_success acquisition installed
  have selected : state.writer.image.directory.active.manifest = none :=
    (congrArg DirectoryPublication.Bindings.manifest ready.settled.1).trans absent
  have observed : MarkedWriterState.observeReopen state.writer.table state.writer.image = some state.writer := by
    have contents : after.wal.active = some (WAL.encode []) := ready.settled.2.2.1
    change MarkedWriterState.observeReopen .empty after = some state.writer
    rw [MarkedWriterState.observeReopen, contents]
    rfl
  refine ⟨state, installed, available, held, observed, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · refine ⟨selected ▸ (absent ▸ ready), ⟨_, refined, represented⟩, ?_, ?_⟩
    · rw [selected]
      trivial
    · rw [selected]
      rfl
  · intro bytes present
    rw [selected] at present
    contradiction

end Alvoki.WAL.Boundary
