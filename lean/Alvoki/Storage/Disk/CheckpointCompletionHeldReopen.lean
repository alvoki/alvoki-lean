import Alvoki.Storage.Disk.CheckpointCompletionClientTrace
import Alvoki.Storage.Disk.CheckpointRunDirectoryClose
import Alvoki.Storage.Disk.CleanCachedClose
import Alvoki.Storage.Disk.ClosedReadyReopen
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

/-- The WAL data and visible marker that checkpoint publication preserves. -/
structure CheckpointWalView where
  kept : Nat → Option ByteArray
  keeper : Publication.Image
  later : LaterNames
  marker : Option ByteArray
  stagedMarker : Option (ByteArray × Bool)

def CheckpointWalView.ofFiles (files : FileImage) : CheckpointWalView :=
  ⟨files.kept, files.keeper, files.later, files.directory.active.walBoundary, files.directory.staged .walBoundary⟩

/-- The raw observations project the WAL fields of each reached successful
callback and settle the directory at the last callback. The manifest
projection uses the same physical states as the checkpoint reports. -/
structure CheckpointCompletionReports.CloseFiles {image : Type} {directory : DiskDirectory}
    {before : SegmentedWriterState} {attempt : SegmentedCheckpointReport directory before}
    (reports : CheckpointCompletionReports (Cache CheckpointOpenHandle × image) attempt) where
  files : image → FileImage
  initial : files (reports.observed.atRun 0).2 = before.files
  manifest : ∀ state, (files state.2).directory.project .manifest = reports.manifest state
  frame : ∀ (done : List CheckpointPublication.Step) step todo prior reached,
    steps attempt.table.runs.length = done ++ step :: todo →
    (done.forM (reports.callbacks.perform directory attempt.prepared attempt.manifest))
      (reports.observed.atRun 0) = .ok () prior →
    reports.callbacks.perform directory attempt.prepared attempt.manifest step prior = .ok () reached →
    CheckpointWalView.ofFiles (files reached.2) = CheckpointWalView.ofFiles (files prior.2)
  finalDirectory : (files reports.observed.completed.2).directory =
    (files reports.observed.renamed.2).directory.syncDirectory

/-- Compose reached local frames over the exact returned checkpoint
callback prefix. Each premise concerns a callback at its reached state. -/
theorem _root_.Alvoki.Storage.CheckpointPublication.successfulFrame {state view : Type}
    (perform : CheckpointPublication.Step → EStateM IO.Error state Unit) (project : state → view)
    {actions : List CheckpointPublication.Step} {initial final : state} (ran : (actions.forM perform) initial = .ok () final)
    (frame : ∀ (done : List CheckpointPublication.Step) step todo prior reached, actions = done ++ step :: todo →
      (done.forM perform) initial = .ok () prior →
      perform step prior = .ok () reached → project reached = project prior) :
    project final = project initial := by
  induction actions generalizing initial with
  | nil => cases ran; rfl
  | cons step rest ih =>
    change EStateM.bind (perform step) (fun _ => rest.forM perform) initial = _ at ran
    cases next : perform step initial with
    | error cause reached => simp only [EStateM.bind, next] at ran; cases ran
    | ok value reached =>
      cases value
      simp only [EStateM.bind, next] at ran
      have tail : project final = project reached := ih ran (by
        intro done action todo prior later order earlier returned
        apply frame (step :: done) action todo prior later (congrArg (List.cons step) order) ?_ returned
        change EStateM.bind (perform step) (fun _ => done.forM perform) initial = _
        simpa only [EStateM.bind, next] using earlier)
      exact tail.trans (frame [] step rest initial reached rfl rfl next)

private theorem checkpointFilesEq {left right : FileImage}
    (wal : CheckpointWalView.ofFiles left = CheckpointWalView.ofFiles right)
    (manifest : left.directory.project .manifest = right.directory.project .manifest)
    (leftSettled : left.directory.crashImages = [left.directory.active])
    (rightSettled : right.directory.crashImages = [right.directory.active]) :
    left = right := by
  have binding : left.directory.active.manifest = right.directory.active.manifest :=
    congrArg Publication.Image.active manifest
  have staged : left.directory.staged .manifest = right.directory.staged .manifest :=
    congrArg Publication.Image.staged manifest
  have marker := congrArg CheckpointWalView.marker wal
  have samePair : left.directory.active = right.directory.active := by
    cases l : left.directory.active
    cases r : right.directory.active
    simpa [l, r, CheckpointWalView.ofFiles] using
      And.intro binding (show left.directory.active.walBoundary = right.directory.active.walBoundary from marker)
  have surviving := leftSettled.trans ((congrArg (fun pair => [pair]) samePair).trans rightSettled.symm)
  have sameStage : left.directory.staged = right.directory.staged := by
    funext entry
    cases entry
    · exact staged
    · exact congrArg CheckpointWalView.stagedMarker wal
  have sameDir : left.directory = right.directory := by
    cases l : left.directory
    cases r : right.directory
    simp_all
  have kept : left.kept = right.kept := congrArg CheckpointWalView.kept wal
  have keeper : left.keeper = right.keeper := congrArg CheckpointWalView.keeper wal
  have later : left.later = right.later := congrArg CheckpointWalView.later wal
  cases left
  cases right
  simp_all

/-- The completed raw callback states project to the installed writer's
files. WAL identity follows from the per-callback frame, and the settled
manifest supplies the new binding. -/
theorem CheckpointCompletionReports.Completed.closeFiles
    {image : Type} {directory : DiskDirectory} {before : SegmentedWriterState}
    {attempt : SegmentedCheckpointReport directory before}
    {reports : CheckpointCompletionReports (Cache CheckpointOpenHandle × image) attempt}
    {phase : Phase Installed} {writer : Nat} {after : SegmentedWriterState}
    (completed : reports.Completed phase writer after) (observed : reports.CloseFiles)
    (ready : before.RetainedReady directory writer) :
    observed.files reports.observed.completed.2 = after.files := by
  have frame := successfulFrame (reports.callbacks.perform directory attempt.prepared attempt.manifest)
    (fun state => CheckpointWalView.ofFiles (observed.files state.2)) reports.observed.returns observed.frame
  change CheckpointWalView.ofFiles (observed.files reports.observed.completed.2) =
    CheckpointWalView.ofFiles (observed.files (reports.observed.atRun 0).2) at frame
  rw [observed.initial] at frame
  have carriesWal : CheckpointWalView.ofFiles after.files = CheckpointWalView.ofFiles before.files := by
    rw [completed.installed.files, completed.installed.wal]
    simp only [CheckpointWalView.ofFiles, Image.segmentedCheckpointView, Image.markedReopenImage]
    rw [← ready.directoryFiles]
    rfl
  have manifest := (observed.manifest reports.observed.completed).trans completed.manifest
  have physicalSettled : (observed.files reports.observed.completed.2).directory.crashImages =
      [(observed.files reports.observed.completed.2).directory.active] := by
    rw [observed.finalDirectory]
    rfl
  have logicalSettled := completed.retained.resumed.ready.settled.trans
    (congrArg (fun pair => [pair]) completed.retained.resumed.ready.selected.symm)
  exact checkpointFilesEq (frame.trans carriesWal.symm) (manifest.trans completed.retained.manifestFiles)
    physicalSettled logicalSettled

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

/-- Transport the held manifest and run reads to the physical files
reported at successful checkpoint completion. -/
theorem CheckpointCompletionReports.Completed.openedPhysicalCheckpoint
    {state : Type} {directory : DiskDirectory} {before : SegmentedWriterState}
    {attempt : SegmentedCheckpointReport directory before} {reports : CheckpointCompletionReports state attempt}
    {phase : Phase Installed} {writer : Nat} {checkpointed : SegmentedWriterState}
    (completed : reports.Completed phase writer checkpointed)
    {input : FilePath} {retry : LockedFileState FileImage}
    {layout : CanonicalKeeperLayout retry.image checkpointed.history}
    (opened : CheckpointHeldOpen input directory layout checkpointed.published)
    {after : SegmentedWriterState}
    (endpoint : ReadyReopenInstallation opened.chunkReports opened.admission after)
    (binding : retry.image.directory.active.manifest = checkpointed.target.pair.manifest)
    {final : LockedFileState FileImage} (files : after.files = final.image) :
    final.image.directory.active.manifest = (reports.manifest reports.observed.completed).active ∧
    opened.wal.operations.reported.inventory.reports.readOptional (directory.file .manifest) =
      .ok (reports.manifest reports.observed.completed).active ∧
    opened.wal.operations.reads.ObservesSelected directory (reports.manifest reports.observed.completed).active
      (reports.runs reports.observed.completed).guaranteed ∧
    SelectedIntegrityCheckpoint (reports.runs reports.observed.completed).guaranteed
      final.image.directory.active.manifest after.checkpoint := by
  have reopenedBinding : final.image.directory.active.manifest = checkpointed.target.pair.manifest := by
    rw [← files, endpoint.writer.retained.resumed.ready.selected, endpoint.target]
  have physicalBinding : (reports.manifest reports.observed.completed).active = checkpointed.target.pair.manifest := by
    rw [completed.manifest, completed.retained.manifestFiles]
    exact congrArg DirectoryPublication.Bindings.manifest completed.retained.resumed.ready.selected
  have physicalManifest := reopenedBinding.trans physicalBinding.symm
  have retryManifest := binding.trans physicalBinding.symm
  have manifestRead := opened.metadata.callbackMetadata.manifestRead.trans (congrArg Except.ok retryManifest)
  have runsRead : opened.wal.operations.reads.ObservesSelected directory (reports.manifest reports.observed.completed).active
      (reports.runs reports.observed.completed).guaranteed := by
    intro bytes metadata found decoded index within payload stored
    exact opened.held.chunkReads bytes metadata (retryManifest.trans found) decoded index within payload
      ((completed.selectedRuns bytes metadata found decoded index within).symm.trans stored)
  have previous := completed.retained.resumed.selected
  rw [← endpoint.checkpoint, ← reopenedBinding] at previous
  exact ⟨physicalManifest, manifestRead, runsRead,
    SelectedIntegrityCheckpoint.withRunMap previous (physicalManifest ▸ completed.selectedRuns.symm)⟩

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
  have reopenedHeld : final.owners.Owns directory reopened.descriptor :=
    slot.symm ▸ owners ▸ endpoint.writer.retained.held
  obtain ⟨physicalManifest, manifestRead, runsRead, selected⟩ :=
    completed.openedPhysicalCheckpoint opened endpoint.toReadyReopenInstallation
      (congrArg DirectoryPublication.Bindings.manifest completed.retained.resumed.ready.selected) files
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

/-- The actual completed checkpoint and cached close supply the origin of
the failed reopen attempts. A later held admission uses the selected bytes
of that physical checkpoint and continues the same client trace. -/
theorem SegmentedClientReadTrace.checkpointCloseAndReopenAfterRetries {image : Type} {input : FilePath}
    {first : LockedFileState WalSegmentRotation.State} (bootstrap : BootstrapReady first.image)
    (held : first.owners.Owns directory initialDescriptor)
    (trace : SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads writer before)
    {attempt : SegmentedCheckpointReport directory before}
    (reports : CheckpointCompletionReports (Cache CheckpointOpenHandle × image) attempt)
    (session : SegmentedSession) (sameDirectory : session.directory = directory)
    (sameDescriptor : session.descriptor = writer) (phase : session.phase = .ready before.installed)
    (descriptors : image → DescriptorInventory) (physical : reports.CloseFiles)
    (close : CachedCloseReports directory writer (reports.closeState descriptors)) (unlocked : close.result = .ok ())
    (reachedDirectory : reports.CloseDirectory descriptors) {retry : LockedFileState FileImage}
    (attempts : ReportedReopenPrefix directory before.wal.active.first
      ⟨physical.files close.finished.files.image.2, close.finished.files.owners⟩ retry)
    (observe : ∀ checkpointed, reports.Completed session.phase writer checkpointed →
      ∀ selected : ClosedReadyReopenLayout checkpointed retry,
      ∃ opened : PrimitiveCheckpointHeldOpen input directory selected.layout checkpointed.published,
        opened.calls.bindings (directory.file .lock) = close.bindings (directory.file .lock) ∧
        opened.calls.slot.description ≠ writer ∧
        opened.held.lifetime.namespaceView.modelObject opened.held.lifetime.root =
          (reports.closeState descriptors).descriptors.inode reachedDirectory.slot.description) :
    ∃ checkpointed, reports.Completed session.phase writer checkpointed ∧
      (runCheckpointWithEffects (reports.callbacks.perform directory)
          (session.phase, ⟨reports.observed.atRun 0, before.owners⟩) =
            .ok () ((reports.closeState descriptors).phase, (reports.closeState descriptors).files) ∧
        close.run = .ok () close.finished ∧ close.finished.phase = .closed ∧
        close.finished.files.image.1 = ⟨none, none, []⟩ ∧
        (⟨physical.files close.finished.files.image.2, close.finished.files.owners⟩ : LockedFileState FileImage) =
          SegmentedCleanReopenReport.released directory checkpointed ∧
        close.finished.descriptors = (reports.closeState descriptors).descriptors.afterDrops
          (close.drops .active ++ close.drops .pending ++ close.drops .directory)) ∧
      ∃ (selected : ClosedReadyReopenLayout checkpointed retry)
        (opened : PrimitiveCheckpointHeldOpen input directory selected.layout checkpointed.published)
        (after : SegmentedWriterState) (reopened : SegmentedSession) (final : LockedFileState FileImage),
        AdmittedCleanReopen (close.cleanUnlock unlocked) opened.toHeldOpen.chunkReports opened.admission after ∧
        opened.wal.operations.runWithAdmission opened.admission = .ok reopened final ∧
        reopened.directory = directory ∧ reopened.descriptor = opened.calls.slot.description ∧
        reopened.phase = .ready after.installed ∧ reopened.sessionRef ∉ opened.calls.liveRefs ∧
        final.owners.Owns directory reopened.descriptor ∧ after.files = final.image ∧ after.owners = final.owners ∧
        opened.calls.descriptors.inode opened.held.lifetime.directorySlot.description =
          (reports.closeState descriptors).descriptors.inode reachedDirectory.slot.description ∧
        final.image.directory.active.manifest = (reports.manifest reports.observed.completed).active ∧
        opened.wal.operations.reported.inventory.reports.readOptional (directory.file .manifest) =
          .ok (reports.manifest reports.observed.completed).active ∧
        opened.wal.operations.reads.ObservesSelected directory (reports.manifest reports.observed.completed).active
          (reports.runs reports.observed.completed).guaranteed ∧
        SelectedIntegrityCheckpoint (reports.runs reports.observed.completed).guaranteed
          final.image.directory.active.manifest after.checkpoint ∧
        SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
          allowCollection log reads opened.calls.slot.description after ∧ GuardedClientReplay log reads after reopened := by
  obtain ⟨checkpointed, completed, _, _, continued, _⟩ :=
    trace.checkpointFromObservedSteps bootstrap held reports session sameDirectory sameDescriptor phase
  have priorReady := (trace.writes.preservesRetained (bootstrap.writerReady held).toRetained).1
  have closeHeld : before.owners.Owns directory writer := completed.installed.owners ▸ completed.retained.held
  have closed := close.reaches (by simp [CheckpointCompletionReports.closeState]) closeHeld
  simp only [CachedCloseReports.Reached, unlocked] at closed
  obtain ⟨closedReturn, closedPhase, cleared, census, _⟩ := closed
  have released : (⟨physical.files close.finished.files.image.2, close.finished.files.owners⟩ : LockedFileState FileImage) =
      SegmentedCleanReopenReport.released directory checkpointed := by
    rw [cleared, SegmentedCleanReopenReport.released, completed.installed.owners]
    exact congrArg (fun files => (⟨files, before.owners.set (directory.file .lock) none⟩ : LockedFileState FileImage))
      (completed.closeFiles physical priorReady)
  have keeper : checkpointed.wal.active.first = before.wal.active.first := by
    rw [completed.installed.wal]
    rfl
  rw [released, ← keeper] at attempts
  obtain ⟨bounded, pair, _, ⟨selected⟩, _⟩ := completed.retained.refinesClosedReopenPrefix attempts
  obtain ⟨opened, lock, distinct, root⟩ := observe checkpointed completed selected
  obtain ⟨after, endpoint⟩ := completed.retained.admitsCleanReopenAt (close.cleanUnlock unlocked) bounded selected
    opened.toHeldOpen.chunkReports opened.admission lock distinct
  obtain ⟨reopened, final, returned, path, description, nextPhase, fresh, files, owners⟩ := endpoint.reopenEffect
  have reopenedHeld : final.owners.Owns directory reopened.descriptor :=
    description.symm ▸ owners ▸ endpoint.writer.retained.held
  obtain ⟨manifest, manifestRead, selectedRuns, selectedCheckpoint⟩ :=
    completed.openedPhysicalCheckpoint opened.toHeldOpen endpoint.toReadyReopenInstallation (congrArg DirectoryPublication.Bindings.manifest pair) files
  have resumed : SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads opened.calls.slot.description after := by
    change SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads opened.toHeldOpen.chunkReports.slot.description after
    simpa only [List.append_nil] using continued.advance (.cleanReopenObserved .start (close.cleanUnlock unlocked) endpoint)
  exact ⟨checkpointed, completed, ⟨completed.returnedToClose descriptors, closedReturn, closedPhase,
    congrArg (fun state => state.image.1) cleared, released, census⟩,
    selected, opened, after, reopened, final, endpoint, returned, path, description, nextPhase, fresh, reopenedHeld, files, owners,
    opened.held.lifetime.identifiesDirectory.symm.trans root, manifest, manifestRead, selectedRuns, selectedCheckpoint,
    resumed, resumed.guardedReplay bootstrap held nextPhase⟩

end Alvoki.Storage.DiskSession
