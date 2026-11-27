import Alvoki.Storage.Disk.Proofs.Checkpoint.CheckpointCompletionHeldReopen
import Alvoki.Storage.Disk.Proofs.Filesystem.LockCensusTrace

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

variable {inventory : DescriptorInventory} {writer : Nat} {cached : DescriptorSlot}

/-- Process exit removes the issuing slots. An alias in another process
can still retain the writer lock in the same census. -/
theorem ReadyProcessExit.reachedCensus (exit : ReadyProcessExit inventory writer cached)
    {directory : DiskDirectory} {before : LockedFileState FileImage}
    (held : before.owners.Owns directory writer) :
    let reached := inventory.afterDrops [.exited exit.process]
    LockCensusTrace directory writer inventory before reached (exit.reached directory before) ∧
      exit.lock ∉ reached.slots ∧ cached ∉ reached.slots ∧
      (TryLockObserves (exit.reached directory before).owners directory (.ok true) ↔
        reached.references writer = []) := by
  intro reached
  have trace : LockCensusTrace directory writer inventory before reached (exit.reached directory before) := by
    simpa only [ReadyProcessExit.reached, DescriptorInventory.dropLockState, dite_eq_left exit.live] using
      (LockCensusTrace.drops (.start held exit.live) [.exited exit.process])
  refine ⟨trace, ?_, ?_, trace.freshFlockAllowed⟩
  · simp [reached, DescriptorInventory.afterDrops, LockReferenceDrop.removes, exit.lockProcess]
  · simp [reached, DescriptorInventory.afterDrops, LockReferenceDrop.removes, exit.cachedProcess]

/-- The exiting slots and canonical objects are observed at the actual
checkpoint return. The old handle identities come from that same census. -/
structure CheckpointCompletionReports.ProcessExit {image : Type} {directory : DiskDirectory}
    {before : SegmentedWriterState} {attempt : SegmentedCheckpointReport directory before}
    (reports : CheckpointCompletionReports (Cache CheckpointOpenHandle × image) attempt)
    (descriptors : image → DescriptorInventory) (captured : reports.CloseDirectory descriptors)
    (writer : Nat) where
  slots : ReadyProcessExit (descriptors reports.observed.completed.2) writer captured.slot
  bindings : image → FilePath → Option Nat
  lock : bindings reports.observed.completed.2 (directory.file .lock) =
    some ((descriptors reports.observed.completed.2).inode slots.lock.description)
  root : bindings reports.observed.completed.2 directory.path =
    some ((descriptors reports.observed.completed.2).inode captured.slot.description)

/-- The physical checkpoint return fixes the files used by the observed
exit. Only the descriptor and lock projection changes at this step. -/
theorem CheckpointCompletionReports.Completed.processExit
    {image : Type} {directory : DiskDirectory} {before checkpointed : SegmentedWriterState}
    {attempt : SegmentedCheckpointReport directory before}
    {reports : CheckpointCompletionReports (Cache CheckpointOpenHandle × image) attempt}
    {phase : Phase Installed} {writer : Nat}
    (completed : reports.Completed phase writer checkpointed) (ready : before.RetainedReady directory writer)
    (physical : reports.CloseFiles) {descriptors : image → DescriptorInventory}
    {captured : reports.CloseDirectory descriptors} (exit : reports.ProcessExit descriptors captured writer) :
    let inventory := descriptors reports.observed.completed.2
    let source := (⟨physical.files reports.observed.completed.2, before.owners⟩ : LockedFileState FileImage)
    let reached := inventory.afterDrops [.exited exit.slots.process]
    runCheckpointWithEffects (reports.callbacks.perform directory)
      (phase, ⟨reports.observed.atRun 0, before.owners⟩) =
        .ok () (.ready checkpointed.installed, ⟨reports.observed.completed, checkpointed.owners⟩) ∧
    source = ⟨checkpointed.files, checkpointed.owners⟩ ∧
    LockCensusTrace directory writer inventory source reached (exit.slots.reached directory source) ∧
    exit.slots.lock ∉ reached.slots ∧ captured.slot ∉ reached.slots ∧
    (TryLockObserves (exit.slots.reached directory source).owners directory (.ok true) ↔
      reached.references writer = []) := by
  intro inventory source reached
  have old : before.owners.Owns directory writer := completed.installed.owners ▸ completed.retained.held
  refine ⟨completed.returned, ?_, exit.slots.reachedCensus (before := source) old⟩
  simp only [source, completed.closeFiles physical ready, completed.installed.owners]

/-- Follow the actual returned checkpoint through process exit and a
reported retry prefix. The final held open reads the same physical
manifest and runs and continues both client ledgers. -/
theorem SegmentedClientReadTrace.checkpointThenProcessExitReopen {image : Type} {input : FilePath}
    {first : LockedFileState WalSegmentRotation.State} (bootstrap : BootstrapReady first.image)
    (held : first.owners.Owns directory initialDescriptor)
    (trace : SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads writer before)
    {attempt : SegmentedCheckpointReport directory before}
    (reports : CheckpointCompletionReports (Cache CheckpointOpenHandle × image) attempt)
    (session : SegmentedSession) (sameDirectory : session.directory = directory)
    (sameDescriptor : session.descriptor = writer) (phase : session.phase = .ready before.installed)
    (descriptors : image → DescriptorInventory) (physical : reports.CloseFiles)
    (captured : reports.CloseDirectory descriptors) (exit : reports.ProcessExit descriptors captured writer)
    {retry : LockedFileState FileImage}
    (attempts : ReportedReopenPrefix directory before.wal.active.first
      (exit.slots.reached directory ⟨physical.files reports.observed.completed.2, before.owners⟩) retry)
    (observe : ∀ checkpointed, reports.Completed session.phase writer checkpointed →
      ∀ selected : ClosedReadyReopenLayout checkpointed retry,
      ∃ opened : PrimitiveCheckpointHeldOpen input directory selected.layout checkpointed.published,
        opened.calls.bindings (directory.file .lock) = exit.bindings reports.observed.completed.2 (directory.file .lock) ∧
        opened.calls.slot.description ≠ writer ∧
        exit.bindings reports.observed.completed.2 directory.path =
          some (opened.held.lifetime.namespaceView.modelObject opened.held.lifetime.root)) :
    let inventory := descriptors reports.observed.completed.2
    let source := (⟨physical.files reports.observed.completed.2, before.owners⟩ : LockedFileState FileImage)
    let reached := inventory.afterDrops [.exited exit.slots.process]
    ∃ checkpointed, reports.Completed session.phase writer checkpointed ∧
      source = ⟨checkpointed.files, checkpointed.owners⟩ ∧
      LockCensusTrace directory writer inventory source reached (exit.slots.reached directory source) ∧
      exit.slots.lock ∉ reached.slots ∧ captured.slot ∉ reached.slots ∧
      (TryLockObserves (exit.slots.reached directory source).owners directory (.ok true) ↔
        reached.references writer = []) ∧
      BoundedReopenTrace directory (· = checkpointed.target) (exit.slots.reached directory source) retry ∧
      ∃ (selected : ClosedReadyReopenLayout checkpointed retry)
        (opened : PrimitiveCheckpointHeldOpen input directory selected.layout checkpointed.published)
        (after : SegmentedWriterState) (reopened : SegmentedSession) (final : LockedFileState FileImage),
        ReadyReopenInstallation opened.toHeldOpen.chunkReports opened.admission after ∧
        opened.wal.operations.runWithAdmission opened.admission = .ok reopened final ∧
        reopened.directory = directory ∧ reopened.descriptor = opened.calls.slot.description ∧
        reopened.phase = .ready after.installed ∧ reopened.sessionRef ∉ opened.calls.liveRefs ∧
        final.owners.Owns directory reopened.descriptor ∧ after.files = final.image ∧ after.owners = final.owners ∧
        opened.calls.descriptors.inode opened.calls.slot.description = inventory.inode exit.slots.lock.description ∧
        opened.calls.descriptors.inode opened.held.lifetime.directorySlot.description = inventory.inode captured.slot.description ∧
        final.image.directory.active.manifest = (reports.manifest reports.observed.completed).active ∧
        opened.wal.operations.reported.inventory.reports.readOptional (directory.file .manifest) =
          .ok (reports.manifest reports.observed.completed).active ∧
        opened.wal.operations.reads.ObservesSelected directory (reports.manifest reports.observed.completed).active
          (reports.runs reports.observed.completed).guaranteed ∧
        SelectedIntegrityCheckpoint (reports.runs reports.observed.completed).guaranteed
          final.image.directory.active.manifest after.checkpoint ∧
        SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
          allowCollection log reads opened.calls.slot.description after ∧ GuardedClientReplay log reads after reopened := by
  intro inventory source reached
  obtain ⟨checkpointed, completed, _, _, continued, _⟩ :=
    trace.checkpointFromObservedSteps bootstrap held reports session sameDirectory sameDescriptor phase
  have ready := (trace.writes.preservesRetained (bootstrap.writerReady held).toRetained).1
  obtain ⟨_, projected, dropped, lockDropped, directoryDropped, vacancy⟩ := completed.processExit ready physical exit
  have projectedSource : source = ⟨checkpointed.files, checkpointed.owners⟩ := projected
  have keeper : checkpointed.wal.active.first = before.wal.active.first := by
    rw [completed.installed.wal]
    rfl
  change ReportedReopenPrefix directory before.wal.active.first (exit.slots.reached directory source) retry at attempts
  rw [projectedSource, ← keeper] at attempts
  have boundedLayout := completed.retained.refinesReadyReopenPrefix
    (owners := (exit.slots.reached directory ⟨checkpointed.files, checkpointed.owners⟩).owners) attempts
  obtain ⟨bounded, pair, kept, ⟨selected⟩, _⟩ := boundedLayout
  obtain ⟨opened, binding, distinct, root⟩ := observe checkpointed completed selected
  have sameLock := Option.some.inj (opened.calls.lockObject.symm.trans (binding.trans exit.lock))
  have sameRoot := opened.held.lifetime.identifiesDirectory.symm.trans (Option.some.inj (root.symm.trans exit.root))
  obtain ⟨after, installed⟩ := completed.retained.admitsReadyReopenAt selected kept opened.toHeldOpen.chunkReports
    opened.admission
  obtain ⟨reopened, final, returned, path, description, nextPhase, fresh, files, owners⟩ := installed.reopenEffect
  have nextHeld : final.owners.Owns directory reopened.descriptor :=
    description.symm ▸ owners ▸ installed.writer.retained.held
  obtain ⟨manifest, manifestRead, selectedRuns, selectedCheckpoint⟩ :=
    completed.openedPhysicalCheckpoint opened.toHeldOpen installed (congrArg DirectoryPublication.Bindings.manifest pair) files
  have continuedTrace : SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads opened.calls.slot.description after := by
    change SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads opened.toHeldOpen.chunkReports.slot.description after
    simpa only [List.append_nil] using continued.advance
      (.readyProcessExit .start exit.slots bounded sameLock distinct installed)
  exact ⟨checkpointed, completed, projectedSource, dropped, lockDropped, directoryDropped, vacancy,
    congrArg (exit.slots.reached directory) projectedSource ▸ bounded,
    selected, opened, after, reopened, final, installed, returned, path, description, nextPhase, fresh,
    nextHeld, files, owners, sameLock, sameRoot, manifest, manifestRead, selectedRuns, selectedCheckpoint,
    continuedTrace, continuedTrace.guardedReplay bootstrap held nextPhase⟩

end Alvoki.Storage.DiskSession
