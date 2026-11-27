import Alvoki.Storage.Disk.Proofs.Recovery.LockedMarkedRead
import Alvoki.Storage.Disk.Proofs.Recovery.LockedRecoveryCompletion
import Alvoki.Storage.Disk.Proofs.Recovery.MarkedDatabaseTrace

namespace Alvoki.WAL.Boundary

open Storage CheckpointPublication

/-- After a reported checkpoint failure and admitted retries, successful
reads at the canonical paths and a successful aligned sync yield the exact
inputs to the whole-file model's ready installer. The same open supplies
the next valid mixed-trace state, with the selected
generation and all prior WAL records. -/
theorem ObservedMarkedState.Valid.interruptedCheckpointFromLockedOpen
    {state : ObservedMarkedState} (valid : state.Valid) (prepared : CheckpointPreparation state)
    {published : Image} {checkpointReport : Step → StepReport}
    (failed : state.publicationInput.runWithReports prepared.runs checkpointReport = .error () published)
    {before : ReopenImage} (attempts : MarkedReopenAttempts (published.markedReopenImage state.writer.image) before)
    {directory : DiskDirectory} {descriptor : Nat} {owners : DiskSession.LockOwners}
    (acquisition : DiskSession.TryLockObserves owners directory (.ok true)) {reports : OpenPathReadReports}
    (observes : (owners.set (directory.file .lock) (some descriptor)).Owns directory descriptor →
      reports.Observes directory before published.durable)
    (manifestRead : ∃ value, reports.readOptional (directory.file .manifest) = .ok value)
    (runReads : ∀ bytes header, before.directory.active.manifest = some bytes →
      Manifest.decode bytes = .ok header → ∀ index, index < header.runCount.toNat →
        ∃ payload, reports.readBin (directory.file (.run header.generation index)) = .ok payload)
    (markerRead : ∃ value, reports.readOptional (directory.file .walBoundary) = .ok value)
    (walRead : ∃ value, reports.readOptional (directory.file .wal) = .ok value)
    (report : Publication.Step → RepairReport) (unlock : DiskSession.UnlockReport) (cause : String → IO.Error) :
    let acquiredOwners := owners.set (directory.file .lock) (some descriptor)
    let reads := RecoveryReads.ofLockedPaths
      (show acquiredOwners.Owns directory descriptor by simp [DiskSession.LockOwners.Owns,
        DiskSession.LockOwners.set, acquiredOwners]) observes manifestRead runReads markerRead walRead
    let reopened := runSharedMarkedOpen reads.checkpointReads.result reads.walReads.marker reads.walReads.wal
      report .success before
    ∃ (next : ObservedMarkedState) (installedOwners : DiskSession.LockOwners),
      DiskSession.runLockedMarkedOpen directory descriptor (.ok true) unlock cause reopened owners =
        .ok ((next.writer.table, next.generation, next.writer.walBytes), next.writer.image) installedOwners ∧
      installedOwners.Owns directory descriptor ∧
      next.writer.image.SettledFor before.directory.active.manifest state.writer.history ∧
      ((before.directory.active.manifest.mapM fun bytes => (Manifest.decode bytes).map (·.generation)).map
        (·.getD 0) : Except String UInt64) = .ok next.generation ∧
      next.writer.walBytes = (WAL.encode state.writer.history).size ∧ next.durable = published.durable ∧
      MarkedDatabaseStep state ⟨[], none⟩ next ∧ next.Valid ∧ next.writer.history = state.writer.history := by
  intro acquiredOwners reads reopened
  obtain ⟨fixed, durable, prior⟩ := valid
  obtain ⟨pending, split⟩ := prior.coveredPrefix
  obtain ⟨model, refines, represents⟩ := prior.live
  have input : fixed.publicationInput state.writer = state.publicationInput := by
    change Image.mk _ fixed.image.durable = Image.mk _ state.durable
    rw [durable]
  obtain ⟨healthy, cut⟩ := checkpointMarked_reported fixed prior.ready split prior.covered
    prior.generationMatches prepared.generationFits prepared.flushed refines represents prepared.runCountFits
    checkpointReport
  rw [input] at healthy
  change (match (fixed.publicationInput state.writer).runWithReports prepared.runs checkpointReport with
    | .ok _ after | .error _ after => _) at cut
  rw [input, failed] at cut
  have fits : (WAL.encode state.writer.history).size < UInt64.size := prior.ready.length ▸ prior.ready.fits
  have witness : ∀ header files, CheckpointRepresentsPrefix state.writer.history header files →
      ∃ checkpoint, CheckpointForRecovery (some (Manifest.encode header)) files checkpoint := by
    rintro _ _ ⟨checkpoint, _, written, _, _⟩
    exact ⟨checkpoint, written.legacy⟩
  have boundary : RecoveryBoundary (fun installed image => reopened = .ok installed image)
      before.directory.active.manifest (· = state.writer.history) :=
    .checkpoint reads prior.ready.settled rfl fits prior.ready.ordered healthy witness cut attempts report
  obtain ⟨execution, table, generation, after, events, installedOwners, corresponds, installed, held,
    settled, sameHistory, _⟩ := RecoveryBoundary.completesWithLock acquisition (fun _ => boundary) unlock cause
  change events = state.writer.history at sameHistory
  subst events
  have recovered := (DiskSession.runOpen_success acquisition installed).2.2.1
  have completed : execution.run = .ok ((table, generation, (WAL.encode state.writer.history).size), after) := by
    cases ran : execution.run with
    | error error => simp [ran, Except.mapError] at recovered
    | ok value => simpa [ran, Except.mapError] using recovered
  have opened := (corresponds _ _).mp completed
  have bound := published.markedReopenImage_markerBound prior.ready.settled (checkpoint_retry_valid healthy cut)
  obtain ⟨marker, _, present, _⟩ := (attempts.toRetry bound).markerBound bound
  have marked : before.directory.active.walBoundary ≠ none := by simp [present]
  let writer : MarkedWriterState := ⟨table, (WAL.encode state.writer.history).size, after, state.writer.history⟩
  have observed : MarkedWriterState.observeReopen table after = some writer := by
    simp [MarkedWriterState.observeReopen, settled.2.2.1, WAL.decodeOrdinals_encode _ prior.ready.ordered,
      Except.toOption, writer]
  let next : ObservedMarkedState := ⟨writer, generation, published.durable⟩
  have step : MarkedDatabaseStep state ⟨[], none⟩ next :=
    .interruptedCheckpointFromOpen prepared failed attempts marked reads.checkpointReads reads.walReads opened observed
  obtain ⟨_, nextValid, _, _⟩ := step.refines ⟨fixed, durable, prior⟩
  have installedGeneration :
      ((before.directory.active.manifest.mapM fun bytes => (Manifest.decode bytes).map (·.generation)).map
        (·.getD 0) : Except String UInt64) = .ok next.generation := by
    obtain ⟨selected, _, nextRefines⟩ := nextValid
    have sameActive := nextRefines.ready.settled.1.symm.trans settled.1
    have selectedManifest := congrArg DirectoryPublication.Bindings.manifest sameActive
    exact selectedManifest ▸ nextRefines.generationMatches
  refine ⟨next, installedOwners, ?_, held, settled, installedGeneration, rfl, rfl, step, nextValid, rfl⟩
  simpa only [DiskSession.runLockedMarkedOpen, opened, completed, Except.mapError] using installed

end Alvoki.WAL.Boundary
