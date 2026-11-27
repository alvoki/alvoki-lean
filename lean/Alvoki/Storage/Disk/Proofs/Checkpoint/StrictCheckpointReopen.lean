import Alvoki.Storage.Disk.Proofs.Write.VersionedReadyWriter

namespace Alvoki.WAL.Boundary
open Storage CheckpointPublication Manifest

private theorem ObservedMarkedState.VersionedReady.installWithLock {state : ObservedMarkedState}
    (valid : state.VersionedReady) {published : Image}
    (trace : VersionedRetry state.writer.history.length.toUInt64
      (CheckpointRepresentsPrefix state.writer.history) state.publicationInput published)
    (integrity : published.manifest.Valid (fun binding => ∀ bytes, binding = some bytes →
      ∃ selected, IntegrityCheckpoint.decode bytes = .ok selected))
    {reopen : ReopenImage} (attempts : MarkedReopenAttempts (published.markedReopenImage state.writer.image) reopen)
    {directory : DiskDirectory} {descriptor : Nat} {owners : DiskSession.LockOwners}
    (acquisition : DiskSession.TryLockObserves owners directory (.ok true))
    {paths : OpenPathReadReports}
    (observes : (owners.set (directory.file .lock) (some descriptor)).Owns directory descriptor →
      paths.ObservesVersioned directory reopen published.durable)
    (manifestRead : ∃ result, paths.readOptional (directory.file .manifest) = .ok result)
    (runReads : ∀ bytes selected, reopen.directory.active.manifest = some bytes →
      IntegrityCheckpoint.decode bytes = .ok selected → ∀ index, index < selected.header.runCount.toNat →
        ∃ payload, paths.readBin (directory.file (.run selected.header.generation index)) = .ok payload)
    (markerRead : ∃ result, paths.readOptional (directory.file .walBoundary) = .ok result)
    (walRead : ∃ result, paths.readOptional (directory.file .wal) = .ok result)
    (report : Publication.Step → RepairReport) (unlock : DiskSession.UnlockReport) (cause : String → IO.Error) :
    let heldOwners := owners.set (directory.file .lock) (some descriptor)
    let held : heldOwners.Owns directory descriptor := by
      simp [heldOwners, DiskSession.LockOwners.Owns, DiskSession.LockOwners.set]
    let checkpointReads := VersionedCheckpointFileReads.ofLockedPaths held observes
    let walReads := (observes held).toObserves.walReads
    let reopened := runSharedMarkedOpen
      (readIntegrityCheckpoint checkpointReads.readManifest checkpointReads.readRun id)
      walReads.marker walReads.wal report .success reopen
    ∃ next : ObservedMarkedState,
      DiskSession.runLockedMarkedOpen directory descriptor (.ok true) unlock cause reopened owners =
        .ok ((next.writer.table, next.generation, next.writer.walBytes), next.writer.image) heldOwners ∧
      owners (directory.file .lock) = none ∧ heldOwners.Owns directory descriptor ∧
      MarkedWriterState.observeReopen next.writer.table next.writer.image = some next.writer ∧
      next.VersionedReady ∧ next.HasIntegrityManifest ∧ next.writer.history = state.writer.history ∧
      next.durable = published.durable ∧ next.writer.table.pins.active = [] ∧
      next.writer.image.directory.active.manifest = reopen.directory.active.manifest := by
  intro heldOwners held checkpointReads walReads reopened
  have manifestChoice := published.markedReopenManifestChoice valid.ready.settled attempts
  have chosenIntegrity : ∀ bytes, reopen.directory.active.manifest = some bytes →
      ∃ selected, IntegrityCheckpoint.decode bytes = .ok selected := by
    rcases manifestChoice with active | survived
    · exact active ▸ integrity.activeValid
    · exact integrity.crashValid _ survived
  have chosenRunReads (bytes : ByteArray) (selected : VersionedCheckpoint)
      (visible : reopen.directory.active.manifest = some bytes)
      (decoded : VersionedCheckpoint.decode bytes = .ok selected)
      (index : Nat) (within : index < selected.header.runCount.toNat) :
      ∃ payload, paths.readBin (directory.file (.run selected.header.generation index)) = .ok payload := by
    obtain ⟨strict, parsed⟩ := chosenIntegrity bytes visible
    have same := Except.ok.inj (decoded.symm.trans (VersionedCheckpoint.decode_integrity parsed))
    subst selected
    exact runReads bytes strict visible parsed index within
  have bytesFit : (WAL.encode state.writer.history).size < UInt64.size := valid.ready.length ▸ valid.ready.fits
  obtain ⟨_, table, generation, model, decoded, installed, previous, owned, ready, observed, refined, represented,
    freshPins⟩ := trace.installs_marked_locked valid.validPublicationInput valid.ready.settled rfl bytesFit
      valid.ready.ordered attempts acquisition observes manifestRead chosenRunReads markerRead walRead report unlock cause
  let writer : MarkedWriterState :=
    ⟨table, (WAL.encode state.writer.history).size, reopen.syncDirectory, state.writer.history⟩
  let next : ObservedMarkedState := ⟨writer, generation, published.durable⟩
  have nextReady : next.VersionedReady := .ofCheckpointReopen trace valid.validPublicationInput valid.ready.settled
    bytesFit attempts ready decoded refined represented
  have manifestObserved : checkpointReads.readManifest = .ok reopen.directory.active.manifest :=
    VersionedCheckpointFileReads.ofLockedPaths_manifest_success held observes manifestRead
  have sameRead := checkpointReads.integrityResult_eq manifestObserved chosenIntegrity
  have exactInstall : DiskSession.runLockedMarkedOpen directory descriptor (.ok true) unlock cause reopened owners =
      .ok ((next.writer.table, next.generation, next.writer.walBytes), next.writer.image) heldOwners := by
    change DiskSession.runLockedMarkedOpen directory descriptor (.ok true) unlock cause
      (runSharedMarkedOpen (readIntegrityCheckpoint checkpointReads.readManifest checkpointReads.readRun id)
        walReads.marker walReads.wal report .success reopen) owners = _
    rw [sameRead]
    exact installed
  exact ⟨next, exactInstall, previous, owned, observed, nextReady, chosenIntegrity, rfl, rfl, freshPins, rfl⟩

/-- A reported v2 checkpoint error can be followed by admitted retries and
strict native reopen. The successful locked result yields a ready writer
whose selected checkpoint is either absent or accepted by the v2 decoder. -/
theorem CheckpointPreparation.reopenAfterIntegrityCheckpointErrorWithLock {state : ObservedMarkedState}
    (prepared : CheckpointPreparation state) (valid : state.VersionedReady) (integrity : state.HasIntegrityManifest)
    (byteLengthsFit : ∀ bytes ∈ prepared.runs.files, bytes.size < UInt64.size)
    {checkpointReport : Step → StepReport} {published : Image}
    (failed : state.publicationInput.runVersionedWithReports (.integrity prepared.runs) checkpointReport =
      some (.error () published))
    {reopen : ReopenImage} (attempts : MarkedReopenAttempts (published.markedReopenImage state.writer.image) reopen)
    {directory : DiskDirectory} {descriptor : Nat} {owners : DiskSession.LockOwners}
    (acquisition : DiskSession.TryLockObserves owners directory (.ok true))
    {paths : OpenPathReadReports}
    (observes : (owners.set (directory.file .lock) (some descriptor)).Owns directory descriptor →
      paths.ObservesVersioned directory reopen published.durable)
    (manifestRead : ∃ result, paths.readOptional (directory.file .manifest) = .ok result)
    (runReads : ∀ bytes selected, reopen.directory.active.manifest = some bytes →
      IntegrityCheckpoint.decode bytes = .ok selected → ∀ index, index < selected.header.runCount.toNat →
        ∃ payload, paths.readBin (directory.file (.run selected.header.generation index)) = .ok payload)
    (markerRead : ∃ result, paths.readOptional (directory.file .walBoundary) = .ok result)
    (walRead : ∃ result, paths.readOptional (directory.file .wal) = .ok result)
    (report : Publication.Step → RepairReport) (unlock : DiskSession.UnlockReport) (cause : String → IO.Error) :
    let heldOwners := owners.set (directory.file .lock) (some descriptor)
    let held : heldOwners.Owns directory descriptor := by
      simp [heldOwners, DiskSession.LockOwners.Owns, DiskSession.LockOwners.set]
    let checkpointReads := VersionedCheckpointFileReads.ofLockedPaths held observes
    let walReads := (observes held).toObserves.walReads
    let reopened := runSharedMarkedOpen
      (readIntegrityCheckpoint checkpointReads.readManifest checkpointReads.readRun id)
      walReads.marker walReads.wal report .success reopen
    ∃ next : ObservedMarkedState,
      DiskSession.runLockedMarkedOpen directory descriptor (.ok true) unlock cause reopened owners =
        .ok ((next.writer.table, next.generation, next.writer.walBytes), next.writer.image) heldOwners ∧
      owners (directory.file .lock) = none ∧ heldOwners.Owns directory descriptor ∧
      MarkedWriterState.observeReopen next.writer.table next.writer.image = some next.writer ∧
      next.VersionedReady ∧ next.HasIntegrityManifest ∧ next.writer.history = state.writer.history ∧
      next.durable = published.durable ∧ next.writer.table.pins.active = [] ∧
      next.writer.image.directory.active.manifest = reopen.directory.active.manifest := by
  obtain ⟨next, installed, previous, owned, observed, ready, strict, history, files, pins, selected⟩ :=
    valid.installWithLock (prepared.reportedFromVersionedReady valid byteLengthsFit failed)
      (prepared.reportedIntegrityBindings valid integrity failed) attempts acquisition observes manifestRead
      runReads markerRead walRead report unlock cause
  exact ⟨next, installed, previous, owned, observed, ready, strict, history, files, pins, selected⟩

/-- Reopen a settled strict writer through any admitted retries with no
intervening operation. The selected manifest and its files stay the same,
the acknowledged history is preserved, and the new session starts with fresh pins. -/
theorem ObservedMarkedState.VersionedReady.reopenWithLock {state : ObservedMarkedState}
    (valid : state.VersionedReady) (integrity : state.HasIntegrityManifest)
    {reopen : ReopenImage} (attempts : MarkedReopenAttempts state.writer.image reopen)
    {directory : DiskDirectory} {descriptor : Nat} {owners : DiskSession.LockOwners}
    (acquisition : DiskSession.TryLockObserves owners directory (.ok true))
    {paths : OpenPathReadReports}
    (observes : (owners.set (directory.file .lock) (some descriptor)).Owns directory descriptor →
      paths.ObservesVersioned directory reopen state.durable)
    (manifestRead : ∃ result, paths.readOptional (directory.file .manifest) = .ok result)
    (runReads : ∀ bytes selected, reopen.directory.active.manifest = some bytes →
      IntegrityCheckpoint.decode bytes = .ok selected → ∀ index, index < selected.header.runCount.toNat →
        ∃ payload, paths.readBin (directory.file (.run selected.header.generation index)) = .ok payload)
    (markerRead : ∃ result, paths.readOptional (directory.file .walBoundary) = .ok result)
    (walRead : ∃ result, paths.readOptional (directory.file .wal) = .ok result)
    (report : Publication.Step → RepairReport) (unlock : DiskSession.UnlockReport) (cause : String → IO.Error) :
    let heldOwners := owners.set (directory.file .lock) (some descriptor)
    let held : heldOwners.Owns directory descriptor := by
      simp [heldOwners, DiskSession.LockOwners.Owns, DiskSession.LockOwners.set]
    let checkpointReads := VersionedCheckpointFileReads.ofLockedPaths held observes
    let walReads := (observes held).toObserves.walReads
    let reopened := runSharedMarkedOpen
      (readIntegrityCheckpoint checkpointReads.readManifest checkpointReads.readRun id)
      walReads.marker walReads.wal report .success reopen
    ∃ next : ObservedMarkedState,
      DiskSession.runLockedMarkedOpen directory descriptor (.ok true) unlock cause reopened owners =
        .ok ((next.writer.table, next.generation, next.writer.walBytes), next.writer.image) heldOwners ∧
      owners (directory.file .lock) = none ∧ heldOwners.Owns directory descriptor ∧
      MarkedWriterState.observeReopen next.writer.table next.writer.image = some next.writer ∧
      next.VersionedReady ∧ next.HasIntegrityManifest ∧ next.writer.history = state.writer.history ∧
      next.durable = state.durable ∧ next.writer.table.pins.active = [] ∧
      next.writer.image.directory.active.manifest = state.writer.image.directory.active.manifest ∧
      next.generation = state.generation := by
  have original := state.publicationInput.markedReopenImage_start valid.ready.settled rfl
  have liftedAttempts : MarkedReopenAttempts (state.publicationInput.markedReopenImage state.writer.image) reopen := by
    rw [original]
    exact attempts
  have only : state.publicationInput.manifest.crashImages = [state.publicationInput.manifest.active] := by
    simp [ObservedMarkedState.publicationInput, DirectoryPublication.Image.project, valid.ready.settled.2.1]
  have known : state.publicationInput.manifest.Valid (fun binding => ∀ bytes, binding = some bytes →
      ∃ selected, IntegrityCheckpoint.decode bytes = .ok selected) := by
    refine ⟨valid.validPublicationInput.hasCrashImage, integrity, ?_⟩
    intro candidate survives
    rw [only] at survives
    exact (List.mem_singleton.mp survives).symm ▸ integrity
  have same : reopen.directory.active.manifest = state.writer.image.directory.active.manifest := by
    rcases state.publicationInput.markedReopenManifestChoice valid.ready.settled liftedAttempts with visible | survives
    · exact visible.symm
    · rw [only] at survives
      exact List.mem_singleton.mp survives
  obtain ⟨next, installed, previous, owned, observed, ready, strict, history, files, pins, chosen⟩ :=
    valid.installWithLock (.refl state.publicationInput) known liftedAttempts acquisition observes manifestRead
      runReads markerRead walRead report unlock cause
  have selected := chosen.trans same
  have matched := ready.generationMatches
  rw [selected] at matched
  exact ⟨next, installed, previous, owned, observed, ready, strict, history, files, pins, selected,
    Except.ok.inj (matched.symm.trans valid.generationMatches)⟩

end Alvoki.WAL.Boundary
