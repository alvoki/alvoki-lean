import Alvoki.Storage.Disk.CheckpointCompletionClientTrace
import Alvoki.Storage.Disk.CheckpointRunDirectoryClose
import Alvoki.Storage.Disk.CleanCachedClose
import Alvoki.Storage.Disk.MaintainedRecoveryWork

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair

/-- Carry the checkpoint callback's reached cache and image directly into
explicit close. Read the issuing census from that same reached image. -/
def CheckpointCompletionReports.closeState {image : Type} {directory : DiskDirectory} {before : SegmentedWriterState}
    {attempt : SegmentedCheckpointReport directory before}
    (reports : CheckpointCompletionReports (Cache CheckpointOpenHandle × image) attempt)
    (descriptors : image → DescriptorInventory) : CachedCloseState CheckpointOpenHandle image :=
  ⟨.ready attempt.prepared, ⟨reports.observed.completed, before.owners⟩, descriptors reports.observed.completed.2⟩

/-- The directory description stored by the native checkpoint remains
live when the close reads the reached cache. -/
structure CheckpointCompletionReports.CloseDirectory {image : Type} {directory : DiskDirectory}
    {before : SegmentedWriterState} {attempt : SegmentedCheckpointReport directory before}
    (reports : CheckpointCompletionReports (Cache CheckpointOpenHandle × image) attempt)
    (descriptors : image → DescriptorInventory) where
  slot : DescriptorSlot
  captured : DescriptorInventory
  ticket : Nat
  cache : reports.observed.completed.1.directory = some (captured, slot, ticket)
  live : slot ∈ (reports.closeState descriptors).descriptors.slots

/-- Close starts at the exact returned phase and physical files of the
completed checkpoint. -/
theorem CheckpointCompletionReports.Completed.returnedToClose
    {image : Type} {directory : DiskDirectory} {before : SegmentedWriterState}
    {attempt : SegmentedCheckpointReport directory before}
    {reports : CheckpointCompletionReports (Cache CheckpointOpenHandle × image) attempt}
    {phase : Phase Installed} {writer : Nat} {after : SegmentedWriterState}
    (completed : reports.Completed phase writer after) (descriptors : image → DescriptorInventory) :
    runCheckpointWithEffects (reports.callbacks.perform directory)
      (phase, ⟨reports.observed.atRun 0, before.owners⟩) =
      .ok () ((reports.closeState descriptors).phase, (reports.closeState descriptors).files) := by
  simpa only [completed.installed.installed, completed.installed.owners, CheckpointCompletionReports.closeState] using
    completed.returned

/-- The physical manifest selects exactly the run indices covered by the
completion report, using its own decoded generation and count. -/
theorem CheckpointCompletionReports.Completed.selectedRuns
    {state : Type} {directory : DiskDirectory} {before : SegmentedWriterState}
    {attempt : SegmentedCheckpointReport directory before} {reports : CheckpointCompletionReports state attempt}
    {phase : Phase Installed} {writer : Nat} {after : SegmentedWriterState}
    (completed : reports.Completed phase writer after) :
    SelectedRunsAgree (reports.manifest reports.observed.completed).active
      (reports.runs reports.observed.completed).guaranteed after.published.durable := by
  intro bytes metadata found decoded index inside
  have binding : bytes = attempt.manifest := by
    rw [completed.manifest, completed.installed.settled] at found
    exact (Option.some.inj found).symm
  subst bytes
  have header := Except.ok.inj (decoded.symm.trans completed.installed.decodedManifest)
  subst metadata
  have count : attempt.table.runs.length.toUInt64.toNat = attempt.table.runs.length :=
    UInt64.toNat_ofNat_of_lt' reports.preflight.preparedFacts.2.2.1
  change index < attempt.table.runs.length.toUInt64.toNat at inside
  rw [count] at inside
  simpa only [Manifest.IntegrityCheckpoint.fromRuns, checkpointHeader, completed.installed.installed,
    SegmentedCheckpointReport.prepared] using completed.runs index inside

/-- With the lock held across publication and up to explicit close, the
same checkpoint files reach the next admitted marked opener. The
callback reports connect the original captured directory to that opener. -/
theorem SegmentedClientReadTrace.checkpointCloseAndReopen {image : Type} {input : FilePath}
    {first : LockedFileState WalSegmentRotation.State} (bootstrap : BootstrapReady first.image)
    (held : first.owners.Owns directory initialDescriptor)
    (trace : SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads writer before)
    {attempt : SegmentedCheckpointReport directory before}
    (reports : CheckpointCompletionReports (Cache CheckpointOpenHandle × image) attempt)
    (session : SegmentedSession) (sameDirectory : session.directory = directory)
    (sameDescriptor : session.descriptor = writer) (phase : session.phase = .ready before.installed)
    (descriptors : image → DescriptorInventory)
    (close : CachedCloseReports directory writer (reports.closeState descriptors))
    (unlocked : close.result = .ok ())
    (reachedDirectory : reports.CloseDirectory descriptors)
    (observe : ∀ checkpointed, reports.Completed session.phase writer checkpointed →
      (close.cleanUnlock unlocked).HeldReopenObservations (before := checkpointed) input
        (fun opened => opened.held.lifetime.namespaceView.modelObject opened.held.lifetime.root =
          (reports.closeState descriptors).descriptors.inode reachedDirectory.slot.description)) :
    ∃ checkpointed, reports.Completed session.phase writer checkpointed ∧
      (runCheckpointWithEffects (reports.callbacks.perform directory)
          (session.phase, ⟨reports.observed.atRun 0, before.owners⟩) =
            .ok () ((reports.closeState descriptors).phase, (reports.closeState descriptors).files) ∧
        close.run = .ok () close.finished ∧ close.finished.phase = .closed ∧
        close.finished.files = ⟨(⟨none, none, []⟩, reports.observed.completed.2), checkpointed.owners.set (directory.file .lock) none⟩ ∧
        close.finished.descriptors = (reports.closeState descriptors).descriptors.afterDrops
          (close.drops .active ++ close.drops .pending ++ close.drops .directory)) ∧
      ∃ (layout : CanonicalKeeperLayout (SegmentedCleanReopenReport.released directory checkpointed).image checkpointed.history)
        (opened : CheckpointHeldOpen input directory layout checkpointed.published)
        (after : SegmentedWriterState) (reopened : SegmentedSession) (final : LockedFileState FileImage),
        AdmittedCleanReopen (close.cleanUnlock unlocked) opened.chunkReports opened.admission after ∧
        opened.wal.operations.runWithAdmission opened.admission = .ok reopened final ∧
        reopened.directory = directory ∧ reopened.descriptor = opened.calls.slot.description ∧
        reopened.phase = .ready after.installed ∧ reopened.sessionRef ∉ opened.calls.liveRefs ∧
        final.owners.Owns directory reopened.descriptor ∧ after.files = final.image ∧ after.owners = final.owners ∧
        opened.wal.operations.descriptors.inode opened.held.lifetime.directorySlot.description =
          (reports.closeState descriptors).descriptors.inode reachedDirectory.slot.description ∧
        final.image.directory.active.manifest = (reports.manifest reports.observed.completed).active ∧
        opened.wal.operations.reported.inventory.reports.readOptional (directory.file .manifest) =
          .ok (reports.manifest reports.observed.completed).active ∧
        opened.wal.operations.reads.ObservesSelected directory (reports.manifest reports.observed.completed).active
          (reports.runs reports.observed.completed).guaranteed ∧
        SelectedIntegrityCheckpoint (reports.runs reports.observed.completed).guaranteed
          final.image.directory.active.manifest after.checkpoint ∧
        SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
          allowCollection log reads opened.calls.slot.description after ∧
        GuardedClientReplay log reads after reopened := by
  obtain ⟨checkpointed, completed, _, _, continued, _⟩ :=
    trace.checkpointFromObservedSteps bootstrap held reports session sameDirectory sameDescriptor phase
  have checkpointHeld : before.owners.Owns directory writer := completed.installed.owners ▸ completed.retained.held
  have ran := close.outcome_open (by simp [CheckpointCompletionReports.closeState])
  rw [unlocked] at ran
  have cleared := close.finishedFiles checkpointHeld
  obtain ⟨layout, opened, after, endpoint, root⟩ := completed.retained.closeWithHeldEvidence
    (close.cleanUnlock unlocked) _ (observe checkpointed completed)
  obtain ⟨reopened, final, returned, dir, slot, ready, fresh, files, owners⟩ := endpoint.reopenEffect
  have reopenedBinding : final.image.directory.active.manifest = checkpointed.target.pair.manifest := by
    rw [← files, endpoint.writer.retained.resumed.ready.selected, endpoint.target]
  have physicalBinding : (reports.manifest reports.observed.completed).active = checkpointed.target.pair.manifest := by
    rw [completed.manifest, completed.retained.manifestFiles]
    exact congrArg DirectoryPublication.Bindings.manifest completed.retained.resumed.ready.selected
  have reopenedHeld : final.owners.Owns directory reopened.descriptor :=
    slot.symm ▸ owners ▸ endpoint.writer.retained.held
  have physicalManifest := reopenedBinding.trans physicalBinding.symm
  have releasedBinding : (SegmentedCleanReopenReport.released directory checkpointed).image.directory.active.manifest =
      (reports.manifest reports.observed.completed).active :=
    (congrArg DirectoryPublication.Bindings.manifest completed.retained.resumed.ready.selected).trans physicalBinding.symm
  have manifestRead := opened.metadata.callbackMetadata.manifestRead.trans (congrArg Except.ok releasedBinding)
  have runsRead : opened.wal.operations.reads.ObservesSelected directory (reports.manifest reports.observed.completed).active
      (reports.runs reports.observed.completed).guaranteed := by
    intro bytes metadata found decoded index within payload stored
    exact opened.held.chunkReads bytes metadata (releasedBinding.trans found) decoded index within payload
      ((completed.selectedRuns bytes metadata found decoded index within).symm.trans stored)
  have selected : SelectedIntegrityCheckpoint (reports.runs reports.observed.completed).guaranteed
      final.image.directory.active.manifest after.checkpoint := by
    have previous := completed.retained.resumed.selected
    rw [← endpoint.checkpoint, ← reopenedBinding] at previous
    exact SelectedIntegrityCheckpoint.withRunMap previous (physicalManifest ▸ completed.selectedRuns.symm)
  have resumed : SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads opened.calls.slot.description after := by
    change SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads opened.chunkReports.slot.description after
    simpa only [List.append_nil] using continued.advance
      (.cleanReopenObserved .start (close.cleanUnlock unlocked) endpoint)
  have clearedFiles : close.finished.files =
      ⟨(⟨none, none, []⟩, reports.observed.completed.2), checkpointed.owners.set (directory.file .lock) none⟩ := by
    rw [cleared, completed.installed.owners]
    rfl
  exact ⟨checkpointed, completed, ⟨completed.returnedToClose descriptors, ran, rfl, clearedFiles, close.finishedDescriptors⟩,
    layout, opened, after, reopened, final, endpoint, returned,
    dir, slot, ready, fresh, reopenedHeld, files, owners, opened.held.lifetime.identifiesDirectory.symm.trans root,
    physicalManifest, manifestRead, runsRead, selected, resumed, resumed.guardedReplay bootstrap held ready⟩

end Alvoki.Storage.DiskSession
