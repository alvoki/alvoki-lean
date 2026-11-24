import Alvoki.Storage.Disk.LockedMarkedReopenEffects
import Alvoki.Storage.Disk.IntegrityDatabaseTrace

namespace Alvoki.Storage.DiskSession
open WAL.Boundary

/-- Reports for an attempted strict open. A rejected acquisition does not
need any claim about the paths that recovery would have read. -/
structure LockedMarkedReopenReports (directory : DiskDirectory) (before : LockedReopenState)
    (durable : CheckpointPublication.RunFiles) where
  descriptor : Nat
  acquired : Except IO.Error Bool
  acquisition : TryLockObserves before.owners directory acquired
  unlock : UnlockReport
  localUnlock : unlock.LocalFlock
  cause : String → IO.Error
  paths : OpenPathReadReports
  observes : acquired = .ok true →
    (before.owners.set (directory.file .lock) (some descriptor)).Owns directory descriptor →
    paths.ObservesVersioned directory before.image durable
  repair : Publication.Step → RepairReport
  aligned : AlignedSyncReport

private def LockedMarkedReopenReports.recovery {directory : DiskDirectory} {before : LockedReopenState}
    {durable : CheckpointPublication.RunFiles} (reports : LockedMarkedReopenReports directory before durable) :
    EStateM.Result String ReopenImage (PackedTable × UInt64 × Nat) :=
  let optional := fun file => (reports.paths.readOptional (directory.file file)).mapError toString
  let runRead := fun generation index => (reports.paths.readBin (directory.file (.run generation index))).mapError toString
  let checkpoint := readIntegrityCheckpoint (optional .manifest) runRead id
  runSharedMarkedOpen checkpoint (optional .walBoundary) (optional .wal) reports.repair reports.aligned before.image

def LockedMarkedReopenReports.run {directory : DiskDirectory} {before : LockedReopenState}
    {durable : CheckpointPublication.RunFiles} (reports : LockedMarkedReopenReports directory before durable) :
    EStateM.Result IO.Error LockedReopenState ((PackedTable × UInt64 × Nat) × ReopenImage) :=
  runLockedMarkedOpenRetainingImage directory reports.descriptor reports.acquired reports.unlock reports.cause
    reports.recovery before

theorem LockedMarkedReopenReports.failure_retry {directory : DiskDirectory} {before after : LockedReopenState}
    {durable : CheckpointPublication.RunFiles} {initial : ReopenImage}
    (reports : LockedMarkedReopenReports directory before durable)
    (attempts : MarkedReopenAttempts initial before.image) (bound : MarkerBound initial.directory)
    {error : IO.Error} (failed : reports.run = .error error after) :
    MarkedReopenAttempts initial after.image := by
  by_cases acquired : reports.acquired = .ok true
  · let owners := before.owners.set (directory.file .lock) (some reports.descriptor)
    have held : owners.Owns directory reports.descriptor := by
      simp [owners, LockOwners.Owns, LockOwners.set]
    let observed := reports.observes acquired
    let checkpoint := VersionedCheckpointFileReads.ofLockedPaths held observed
    let wal := (observed held).toObserves.walReads
    exact runLockedStrictMarkedOpenRetainingImage_retry attempts bound directory reports.descriptor reports.acquired
      reports.unlock reports.cause checkpoint wal reports.repair reports.aligned failed
  · obtain ⟨_, unchanged⟩ := runLockedMarkedOpenRetainingImage_notAcquired directory reports.descriptor
      reports.acquired reports.unlock reports.cause reports.recovery before acquired
    have same := (EStateM.Result.error.inj (failed.symm.trans unchanged)).2
    simpa only [same] using attempts

/-- Ownership retained at an earlier error blocks a second cooperating
acquisition until a later lifetime event releases it. -/
theorem LockedMarkedReopenReports.whileHeld {directory : DiskDirectory} {before : LockedReopenState}
    {durable : CheckpointPublication.RunFiles} {owner : Nat}
    (reports : LockedMarkedReopenReports directory before durable) (owned : before.owners.Owns directory owner) :
    ∃ cause, reports.run = .error cause before := by
  apply runLockedMarkedOpenRetainingImage_notAcquired
  intro acquired
  have none := reports.acquisition acquired
  change before.owners (directory.file .lock) = some owner at owned
  rw [none] at owned
  contradiction

/-- Observed count of remaining references to the same exclusive open file
description after closure or process exit, including duplicate and inherited
references. Ownership is released only when this count reaches zero. -/
structure LockDescriptionCloseReport where
  descriptor : Nat
  remainingReferences : Nat

/-- A finite retry shares one directory, durable run map, and joint file and
lock state. A crash choice describes filesystem effects. Changes to lock
ownership require the observed open, close, or last-reference effects. -/
inductive LockedMarkedReopenFailureTrace (directory : DiskDirectory) (durable : CheckpointPublication.RunFiles)
    (initial : LockedReopenState) : LockedReopenState → Prop where
  | start : LockedMarkedReopenFailureTrace directory durable initial initial
  | failure (prior : LockedMarkedReopenFailureTrace directory durable initial before)
      (reports : LockedMarkedReopenReports directory before durable)
      (failed : reports.run = .error error after) :
      LockedMarkedReopenFailureTrace directory durable initial after
  | close (prior : LockedMarkedReopenFailureTrace directory durable initial before)
      {descriptor : Nat} (owned : before.owners.Owns directory descriptor)
      (phase : Phase Unit) (unlock : UnlockReport) (localUnlock : unlock.LocalFlock)
      (closed : runClose directory descriptor unlock ⟨phase, before.owners⟩ = .ok () after) :
      LockedMarkedReopenFailureTrace directory durable initial ⟨before.image, after.owners⟩
  | lastReferenceClosed (prior : LockedMarkedReopenFailureTrace directory durable initial before)
      (report : LockDescriptionCloseReport) (owned : before.owners.Owns directory report.descriptor)
      (last : report.remainingReferences = 0) :
      LockedMarkedReopenFailureTrace directory durable initial
        ⟨before.image, before.owners.release (directory.file .lock) report.descriptor⟩
  | crash (prior : LockedMarkedReopenFailureTrace directory durable initial before)
      (pairSurvives : pair ∈ before.image.directory.crashImages)
      (walSurvives : wal ∈ before.image.wal.crashImages) :
      LockedMarkedReopenFailureTrace directory durable initial ⟨.crash pair wal, before.owners⟩
  | delayedDirectorySync (prior : LockedMarkedReopenFailureTrace directory durable initial before) :
      LockedMarkedReopenFailureTrace directory durable initial ⟨before.image.syncMetadata, before.owners⟩
  | delayedWalFileSync (prior : LockedMarkedReopenFailureTrace directory durable initial before)
      {target : WalFileSyncTarget} (bound : target.TargetsLiveWal before.image) :
      LockedMarkedReopenFailureTrace directory durable initial ⟨before.image.allowVisibleWal, before.owners⟩

/-- Exact reported locked retry steps preserve the physically admitted
marked history of attempts, even after a cleanup error retains ownership. -/
theorem LockedMarkedReopenFailureTrace.toAttempts {directory : DiskDirectory} {durable : CheckpointPublication.RunFiles}
    {initial after : LockedReopenState} {origin : ReopenImage}
    (path : LockedMarkedReopenFailureTrace directory durable initial after)
    (earlierAttempts : MarkedReopenAttempts origin initial.image) (bound : MarkerBound origin.directory) :
    MarkedReopenAttempts origin after.image := by
  induction path with
  | start => exact earlierAttempts
  | failure _ reports failed earlier => exact reports.failure_retry earlier bound failed
  | close _ _ _ _ _ _ earlier => exact earlier
  | lastReferenceClosed _ _ _ _ earlier => exact earlier
  | crash _ pairSurvives walSurvives earlier => exact .crash earlier pairSurvives walSurvives
  | delayedDirectorySync _ earlier => exact .delayedDirectorySync earlier
  | delayedWalFileSync _ targets earlier => exact .delayedWalFileSync earlier targets

private theorem markerBound_of_ready {writer : MarkedWriterState} {manifest : Option ByteArray}
    (ready : writer.ReadyFor manifest) : MarkerBound writer.image.directory := by
  let count := (WAL.encode writer.history).size.toUInt64
  have active := congrArg DirectoryPublication.Bindings.walBoundary ready.settled.1
  refine ⟨WAL.Boundary.encode count, count, active, WAL.Boundary.decode_encode _, ?_⟩
  intro pair selected
  have same : pair = writer.image.directory.active := by
    rcases List.mem_cons.mp selected with visible | survived
    · exact visible
    · rw [ready.settled.2.1] at survived
      exact List.mem_singleton.mp survived
  exact ⟨WAL.Boundary.encode count, count, same.symm ▸ active, WAL.Boundary.decode_encode _, Nat.le_refl _⟩

/-- Once lock acquisition, required reads, and the aligned sync succeed on
the threaded state, a settled strict writer recovers its exact WAL, run
map and generation, with canonical table refinement and fresh pins. -/
theorem LockedMarkedReopenFailureTrace.completesSettled {directory : DiskDirectory}
    {state : ObservedMarkedState} {initialOwners : LockOwners} {after : LockedReopenState}
    (retry : LockedMarkedReopenFailureTrace directory state.durable ⟨state.writer.image, initialOwners⟩ after)
    (valid : state.VersionedReady) (integrity : state.HasIntegrityManifest)
    (reports : IntegrityLockedOpenReports after.image state.durable)
    (sameDirectory : reports.directory = directory) (sameOwners : reports.owners = after.owners)
    (aligned : reports.aligned = .success) :
    ∃ next : ObservedMarkedState,
      reports.Returned next ∧ after.owners (directory.file .lock) = none ∧
      reports.toIntegrityOpenPaths.heldOwners.Owns directory reports.descriptor ∧
      next.VersionedReady ∧ next.HasIntegrityManifest ∧
      next.writer.history = state.writer.history ∧ next.writer.walBytes = (WAL.encode state.writer.history).size ∧
      next.writer.image.directory.active.manifest = state.writer.image.directory.active.manifest ∧
      next.generation = state.generation ∧ next.writer.table.pins.active = [] := by
  have attempts := retry.toAttempts (.start : MarkedReopenAttempts state.writer.image state.writer.image)
    (markerBound_of_ready valid.ready)
  obtain ⟨next, installed, available, held, observed, ready, strict, history, files, pins, manifest, generation⟩ :=
    valid.reopenWithLock integrity attempts reports.acquisition reports.observes
      reports.manifestRead reports.runReads reports.markerRead reports.walRead reports.repair reports.unlock reports.cause
  have result : reports.Returned next := by
    refine ⟨?_, observed, files⟩
    unfold IntegrityLockedOpenReports.run
    rw [aligned]
    exact installed
  have byteCount : next.writer.walBytes = (WAL.encode state.writer.history).size := by
    rw [ready.ready.length, history]
  have terminalOwner : reports.toIntegrityOpenPaths.heldOwners.Owns directory reports.descriptor := by
    rw [← sameDirectory]
    exact held
  exact ⟨next, result, by simpa only [sameOwners, sameDirectory] using available,
    terminalOwner, ready, strict, history, byteCount, manifest, generation, pins⟩

/-- Start the locked retry from the file image of the reported v2 checkpoint
failure. A final healthy reopen selects its old or proposed checkpoint and
preserves the acknowledged WAL, using the ownership left by the actual retries. -/
theorem LockedMarkedReopenFailureTrace.completesInterruptedCheckpoint {directory : DiskDirectory}
    {state : ObservedMarkedState} (prepared : CheckpointPreparation state)
    (valid : state.VersionedReady) (integrity : state.HasIntegrityManifest)
    (byteLengthsFit : ∀ bytes ∈ prepared.runs.files, bytes.size < UInt64.size)
    {checkpointReport : CheckpointPublication.Step → CheckpointPublication.StepReport}
    {published : CheckpointPublication.Image}
    (failed : state.publicationInput.runVersionedWithReports (.integrity prepared.runs) checkpointReport =
      some (.error () published))
    {initialOwners : LockOwners} {after : LockedReopenState}
    (retry : LockedMarkedReopenFailureTrace directory published.durable
      ⟨published.markedReopenImage state.writer.image, initialOwners⟩ after)
    (reports : IntegrityLockedOpenReports after.image published.durable)
    (sameDirectory : reports.directory = directory) (sameOwners : reports.owners = after.owners)
    (aligned : reports.aligned = .success) :
    ∃ next : ObservedMarkedState,
      reports.Returned next ∧ after.owners (directory.file .lock) = none ∧
      reports.toIntegrityOpenPaths.heldOwners.Owns directory reports.descriptor ∧
      next.VersionedReady ∧ next.HasIntegrityManifest ∧
      next.writer.history = state.writer.history ∧ next.writer.walBytes = (WAL.encode state.writer.history).size ∧
      next.writer.table.pins.active = [] ∧
      (next.writer.image.directory.active.manifest = state.writer.image.directory.active.manifest ∨
        next.writer.image.directory.active.manifest =
          some (CheckpointPublication.VersionedRunSet.integrity prepared.runs).manifest.encode) ∧
      ∀ bytes, next.writer.image.directory.active.manifest = some bytes →
        ∃ manifest files,
          Manifest.IntegrityCheckpoint.decode bytes = .ok manifest ∧ next.generation = manifest.header.generation ∧
          (List.range manifest.header.runCount.toNat).mapM (published.durable manifest.header.generation) = some files ∧
          (List.range manifest.header.runCount.toNat).mapM
            (fun index => (reports.paths.readBin (directory.file (.run manifest.header.generation index))).mapError toString) =
              .ok files ∧ manifest.validateRuns files = true := by
  have attempts := retry.toAttempts .start (published.markedReopenBound valid.ready.settled)
  obtain ⟨next, installed, available, held, observed, ready, strict, history, files, pins, selected⟩ :=
    prepared.reopenAfterIntegrityCheckpointErrorWithLock valid integrity byteLengthsFit failed attempts
      reports.acquisition reports.observes reports.manifestRead reports.runReads
      reports.markerRead reports.walRead reports.repair reports.unlock reports.cause
  have result : reports.Returned next := by
    refine ⟨?_, observed, files⟩
    unfold IntegrityLockedOpenReports.run
    rw [aligned]
    exact installed
  have byteCount : next.writer.walBytes = (WAL.encode state.writer.history).size := by
    rw [ready.ready.length, history]
  have terminalOwner : reports.toIntegrityOpenPaths.heldOwners.Owns directory reports.descriptor := by
    rw [← sameDirectory]
    exact held
  have allowed := prepared.reportedManifestChoices valid failed
  have priorOrProposed : next.writer.image.directory.active.manifest = state.writer.image.directory.active.manifest ∨
      next.writer.image.directory.active.manifest =
        some (CheckpointPublication.VersionedRunSet.integrity prepared.runs).manifest.encode := by
    rw [selected]
    rcases published.markedReopenManifestChoice valid.ready.settled attempts with active | survived
    · exact active ▸ allowed.activeValid
    · exact allowed.crashValid _ survived
  refine ⟨next, result, by simpa only [sameOwners, sameDirectory] using available,
    terminalOwner, ready, strict, history, byteCount, pins, priorOrProposed, ?_⟩
  intro bytes visible
  obtain ⟨manifest, decoded⟩ := strict bytes visible
  have tagged := Manifest.VersionedCheckpoint.decode_integrity decoded
  have accepted := ready.selected
  rw [visible] at accepted
  obtain ⟨orderedRuns, stored, _, checked, _⟩ :=
    CheckpointPublication.Image.acceptsVersioned_runs accepted tagged
  change (List.range manifest.header.runCount.toNat).mapM (next.durable manifest.header.generation) =
    some orderedRuns at stored
  rw [files] at stored
  have actualManifest : after.image.directory.active.manifest = some bytes := selected.symm.trans visible
  have reads := VersionedCheckpointFileReads.ofLockedPaths_runs_success (selected := .integrity manifest)
    reports.toIntegrityOpenPaths.held reports.observes actualManifest tagged
    (reports.runReads bytes manifest actualManifest decoded) stored
  have observed : (List.range manifest.header.runCount.toNat).mapM
      (fun index => (reports.paths.readBin
        (reports.directory.file (.run manifest.header.generation index))).mapError toString) = .ok orderedRuns := reads
  have installed := ready.generationMatches
  rw [visible] at installed
  have generation : manifest.header.generation = next.generation := by
    simpa [Option.mapM, tagged, Functor.map, Except.map, Manifest.VersionedCheckpoint.header] using installed
  exact ⟨manifest, orderedRuns, decoded, generation.symm, stored,
    by simpa only [sameDirectory] using observed, checked⟩

end Alvoki.Storage.DiskSession
