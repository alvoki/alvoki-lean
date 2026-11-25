import Alvoki.Storage.Disk.CheckpointRunOpenFailure
import Alvoki.Storage.Disk.StagedHandleCustody

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting
open WAL.Boundary (WalInodeImage)

private abbrev Handle := DescriptorInventory × DescriptorSlot
private abbrev Files := Cache Handle × WalInodeImage
private abbrev FileIO := EStateM IO.Error WalInodeImage

variable {directory : DiskDirectory} {before : SegmentedWriterState}
  {attempt : SegmentedCheckpointReport directory before}

private theorem dispatchWrite (runs : ObservedCheckpointRunPrefix attempt) :
    runs.perform (.writeRun runs.index) (runs.atRun runs.index) =
    runs.writeRun runs.path runs.run.run.bytes (runs.atRun runs.index) := by
  change performCheckpointFileStep directory (SegmentedCheckpointReport.generation before)
    attempt.table.runs.toArray (directory.file .stagedManifest) attempt.manifest
    (fun found => match found with
      | some run => pure run
      | none => throw (IO.userError "checkpoint run index is out of bounds"))
    runs.writeRun runs.writeStage (SyncPathGroup.run (sync directory.path runs.openRead runs.fsync)) runs.rename
    (.writeRun runs.index) (runs.atRun runs.index) = _
  simp [performCheckpointFileStep, runs.selected, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

/-- The reached data call has no return report. Issuing flush requires the
write on this same description to have returned successfully. -/
inductive RunDataIssue (write : Handle → ByteArray → FileIO Unit) (flush : Handle → FileIO Unit)
    (handle : Handle) (bytes : ByteArray) (opened : WalInodeImage) :
    FileIO Unit → WalInodeImage → Prop where
  | write : RunDataIssue write flush handle bytes opened (write handle bytes) opened
  | flush (written : write handle bytes opened = .ok () buffered) :
      RunDataIssue write flush handle bytes opened (flush handle) buffered

/-- The actual guarded write dispatch reaches a raw write or flush on the
opened inode. Its partial target contents and crash names are observed. -/
structure CheckpointRunDataInterruption (runs : ObservedCheckpointRunPrefix attempt) where
  lookup : FilePath → FileIO (Except IO.Error IO.FS.Metadata)
  openWrite : FilePath → FileIO Handle
  write : Handle → ByteArray → FileIO Unit
  flush : Handle → FileIO Unit
  guard : AcceptedRunGuard lookup runs.path (runs.atRun runs.index).2
  handle : Handle
  drops : List LockReferenceDrop
  live : handle.2.reference ∈ (handle.1.afterDrops drops).references handle.2.description
  afterOpen : WalInodeImage
  opened : openWrite runs.path (runs.atRun runs.index).2 = .ok handle afterOpen
  openView : RunDirectoryInodeView directory afterOpen (runs.runs ((runs.atRun runs.index).1, afterOpen))
  truncated : RunOpenTruncation (path := runs.path) lookup (runs.view runs.index) openView
    (handle.1.inode handle.2.description)
  projected : runs.writeRun runs.path runs.run.run.bytes (runs.atRun runs.index) =
    stageFreshWithCache runs.path runs.run.run.bytes
      (fun path bytes => writeCheckpointRunWith lookup openWrite write flush path bytes pure) (runs.atRun runs.index)
  operation : FileIO Unit
  atIssue : WalInodeImage
  issued : RunDataIssue write flush handle runs.run.run.bytes afterOpen operation atIssue
  stopped : WalInodeImage
  view : RunDirectoryInodeView directory stopped (runs.runs ((runs.atRun runs.index).1, stopped))
  frame : RunWriteInodeFrame runs.path (handle.1.inode handle.2.description) stopped openView view

/-- The selected write has returned and installed its pending handle.
An issued fsync can change crash choices for that inode only. -/
structure CheckpointRunSyncInterruption (runs : ObservedCheckpointRunPrefix attempt) where
  handle : Handle
  flushed : WalInodeImage
  writes : RunWriteReports runs.path runs.run.run.bytes (runs.atRun runs.index).2 flushed handle
  projected : runs.writeRun runs.path runs.run.run.bytes (runs.atRun runs.index) =
    stageFreshWithCache runs.path runs.run.run.bytes (fun path bytes =>
      writeCheckpointRunWith writes.lookup writes.openWrite writes.write writes.flush path bytes pure)
      (runs.atRun runs.index)
  links : RunOpenLinkReports writes (runs.view runs.index).visible (handle.1.inode handle.2.description)
  drops : List LockReferenceDrop
  live : handle.2.reference ∈ (handle.1.afterDrops drops).references handle.2.description
  outcomes : List ByteArray
  view : RunDirectoryInodeView directory (flushed.reportFileSync (handle.1.inode handle.2.description) outcomes)
    (runs.runs ((runs.atRun runs.index).1.consume runs.path,
      flushed.reportFileSync (handle.1.inode handle.2.description) outcomes))
  frame : RunWriteInodeFrame runs.path (handle.1.inode handle.2.description) flushed (runs.view runs.index) view

namespace CheckpointRunDataInterruption

variable {runs : ObservedCheckpointRunPrefix attempt}

/-- The shared run callback selects the exact reported path and data
continuation. In execution it can stop during either reported issue. -/
theorem reaches (observed : CheckpointRunDataInterruption runs) :
    runs.perform (.writeRun runs.index) (runs.atRun runs.index) =
    stageFreshWithCache runs.path runs.run.run.bytes (fun path bytes =>
      writeCheckpointRunWith observed.lookup observed.openWrite observed.write observed.flush path bytes pure)
      (runs.atRun runs.index) ∧
    writeCheckpointRunWith observed.lookup observed.openWrite observed.write observed.flush runs.path runs.run.run.bytes
      pure (runs.atRun runs.index).2 =
      (observed.write observed.handle runs.run.run.bytes >>= fun _ =>
        observed.flush observed.handle >>= fun _ => pure observed.handle) observed.afterOpen ∧
    RunDataIssue observed.write observed.flush observed.handle runs.run.run.bytes
      observed.afterOpen observed.operation observed.atIssue := by
  refine ⟨(dispatchWrite runs).trans observed.projected, ?_, observed.issued⟩
  rcases observed.guard with ⟨_, _, absent⟩ | ⟨metadata, present, regular, privateFile⟩
  · simp [writeCheckpointRunWith, optionalMetadataWith, absent, observed.opened, Bind.bind, EStateM.bind,
      Pure.pure, EStateM.pure]
  · have fileKind : (IO.FS.FileType.file == .file) = true := rfl
    simp [writeCheckpointRunWith, optionalMetadataWith, checkPrivateRegularWith, present, regular, privateFile,
      fileKind, observed.opened, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

end CheckpointRunDataInterruption

namespace CheckpointRunSyncInterruption

variable {runs : ObservedCheckpointRunPrefix attempt}

def atStep (observed : CheckpointRunSyncInterruption runs) : Files :=
  ((runs.atRun runs.index).1.remember runs.path observed.handle, observed.flushed)

theorem wrote (observed : CheckpointRunSyncInterruption runs) :
    runs.perform (.writeRun runs.index) (runs.atRun runs.index) = .ok () observed.atStep := by
  rw [dispatchWrite, observed.projected, stageFreshWithCache, observed.writes.captures]
  rfl

/-- The shared barrier uses the captured pending handle. The equality
identifies its fsync and does not impose a return for that call. -/
theorem reaches (observed : CheckpointRunSyncInterruption runs) :
    runs.perform (.syncRun runs.index) =
      SyncPathGroup.run (sync directory.path runs.openRead runs.fsync) #[runs.path] ∧
    observed.atStep.1.resolve directory.path runs.path runs.openRead observed.atStep.2 =
      .ok observed.handle ((runs.atRun runs.index).1.consume runs.path, observed.flushed) := by
  refine ⟨rfl, ?_⟩
  have separate : (runs.path == directory.path) = false :=
    beq_eq_false_iff_ne.mpr (runPath_ne_directory directory (SegmentedCheckpointReport.generation before) runs.index)
  simp [atStep, Cache.resolve, Cache.remember, Cache.consume, pushPending, separate]

end CheckpointRunSyncInterruption

/-- No directory barrier has been issued. A private run can have partial
data or durable bytes while its directory name remains unsettled. -/
inductive CheckpointRunInterruption (runs : ObservedCheckpointRunPrefix attempt) where
  | data (observed : CheckpointRunDataInterruption runs)
  | sync (observed : CheckpointRunSyncInterruption runs)

namespace CheckpointRunInterruption

variable {runs : ObservedCheckpointRunPrefix attempt}

def completed : CheckpointRunInterruption runs → List Step
  | .data _ => runSteps runs.index
  | .sync _ => runSteps runs.index ++ [.writeRun runs.index]

def current : CheckpointRunInterruption runs → Step
  | .data _ => .writeRun runs.index
  | .sync _ => .syncRun runs.index

def atStep : CheckpointRunInterruption runs → Files
  | .data _ => runs.atRun runs.index
  | .sync observed => observed.atStep

def reached : CheckpointRunInterruption runs → Files
  | .data observed => ((runs.atRun runs.index).1, observed.stopped)
  | .sync observed => ((runs.atRun runs.index).1.consume runs.path,
      observed.flushed.reportFileSync (observed.handle.1.inode observed.handle.2.description) observed.outcomes)

def view (observed : CheckpointRunInterruption runs) :
    RunDirectoryInodeView directory observed.reached.2 (runs.runs observed.reached) :=
  match observed with
  | .data report => report.view
  | .sync report => report.view

/-- The prepared checkpoint's actual callbacks return precisely the
observed prefix before issuing the interrupted operation. -/
theorem reaches (observed : CheckpointRunInterruption runs) :
    CheckpointPreflight (.ready before.installed) (.ok (attempt.prepared, attempt.manifest)) ∧
    (∃ later, steps attempt.table.runs.length = observed.completed ++ observed.current :: later) ∧
    (observed.completed.forM runs.perform) (runs.atRun 0) = .ok () observed.atStep := by
  have past := runSteps_returned runs.perform runs.index runs.atRun (fun i earlier =>
    let ⟨pair⟩ := runs.prefixPairs i earlier
    pair.returned)
  obtain ⟨later, ordered⟩ := steps_atRunPair runs.within
  refine ⟨attempt.preflight runs.flushedTable runs.generationFits runs.runCountFits runs.encoded, ?_⟩
  cases observed with
  | data => exact ⟨⟨.syncRun runs.index :: later, by simpa [completed, current, List.append_assoc] using ordered⟩, past⟩
  | sync observed =>
    refine ⟨⟨later, by simpa [completed, current, List.append_assoc] using ordered⟩, ?_⟩
    change ((runSteps runs.index ++ [Step.writeRun runs.index]).forM runs.perform) (runs.atRun 0) = .ok () observed.atStep
    rw [List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM]
    change EStateM.bind ((runSteps runs.index).forM runs.perform) (fun _ => [Step.writeRun runs.index].forM runs.perform)
      (runs.atRun 0) = _
    simp only [EStateM.bind, past]
    simp [List.forM_eq_forM, List.forM_cons, List.forM_nil, Bind.bind, EStateM.bind, observed.wrote, Pure.pure, EStateM.pure]

/-- Irrespective of whether the issued operation counts as a complete
effect, the logical publication still selects the prior checkpoint. -/
theorem projection (observed : CheckpointRunInterruption runs) (effective : Bool) :
    before.published.executeVersioned attempt.plan
      (observed.completed.length + (if effective then 1 else 0)) = some before.published := by
  apply Image.executeVersioned_beforeRunDirectory
  have count : attempt.plan.files.length = attempt.table.runs.length := by
    simp [SegmentedCheckpointReport.plan, VersionedRunSet.integrity]
  rw [count]
  obtain ⟨later, split⟩ := runSteps_atRunPair runs.within
  cases observed <;> cases effective <;>
    simp [completed, split] <;> omega

/-- Carry the same old inode and bytes across both the returned prefix
and the partial effect of the currently issued operation. -/
theorem priorStable (observed : CheckpointRunInterruption runs) {writer : Nat}
    (ready : before.RetainedReady directory writer)
    (entry : CheckpointRunPrefix.EntrySelection before (runs.view 0))
    {raw : ByteArray} {metadata : Manifest.IntegrityCheckpoint}
    (binding : before.wal.directory.active.manifest = some raw)
    (decoded : Manifest.IntegrityCheckpoint.decode raw = .ok metadata)
    {index : Nat} (within : index < metadata.header.runCount.toNat) :
    let path := directory.file (.run metadata.header.generation index)
    ∃ payload inode, before.published.durable metadata.header.generation index = some payload ∧
      (runs.view 0).Stable path inode payload ∧ observed.view.Stable path inode payload := by
  obtain ⟨payload, inode, stored, captured, stable, separate⟩ :=
    runs.priorStableFromEntry ready entry binding decoded within
  refine ⟨payload, inode, stored, captured, ?_⟩
  cases observed with
  | data observed =>
    have privateAtEntry := observed.truncated.links.privateBinding observed.guard
    have privateAfterOpen : ∀ other, observed.openView.visible other = some (observed.handle.1.inode observed.handle.2.description) →
        other = runs.path := by
      intro other bound
      by_cases same : other = runs.path
      · exact same
      · exact privateAtEntry other ((observed.truncated.frame.visibleNames other same).symm.trans bound)
    have opened := observed.truncated.frame.keepsStableOnSyncError (effective := false) rfl privateAtEntry separate stable
    exact observed.frame.keepsStableOnSyncError (effective := false) rfl privateAfterOpen separate opened
  | sync observed =>
    let target := observed.handle.1.inode observed.handle.2.description
    have effect : RunWriteInodeFrame runs.path target (observed.flushed.reportFileSync target observed.outcomes)
        (runs.view runs.index) observed.view := by
      refine ⟨observed.frame.visibleNames, observed.frame.crashNames, observed.frame.visibleBytes, ?_⟩
      intro other different
      simp [WalInodeImage.reportFileSync, different, observed.frame.crashBytes other different]
    exact effect.keepsStableOnSyncError (effective := false) rfl observed.links.privateBinding separate stable

/-- Every observed crash survivor still selects the prior checkpoint
with its exact physical run bytes. This is a safety claim at the cut. -/
theorem selectsPrior (observed : CheckpointRunInterruption runs) {writer : Nat}
    (ready : before.RetainedReady directory writer)
    (entry : CheckpointRunPrefix.EntrySelection before (runs.view 0))
    {manifest : Files → Publication.Image} (frames : RunPrefixManifestFrames runs observed.reached manifest)
    {binding : Option ByteArray} (survives : binding ∈ (manifest observed.reached).crashImages)
    {files : RunFiles} (runSurvives : files ∈ (runs.runs observed.reached).crashImages) :
    binding = before.wal.directory.active.manifest ∧
    SelectedRunsAgree binding files before.published.durable ∧
    SelectedIntegrityCheckpoint files binding before.checkpoint := by
  have choices : (manifest observed.reached).crashImages = [before.wal.directory.active.manifest] := by
    rw [frames.preserves, ready.manifestFiles, ready.directoryFiles]
    simp [DirectoryPublication.Image.project, DirectoryPublication.Bindings.get, ready.walDirectorySettled]
  rw [choices] at survives
  have same := List.mem_singleton.mp survives
  have agrees : SelectedRunsAgree binding files before.published.durable := by
    intro raw metadata found decoded index within
    obtain ⟨payload, inode, stored, _, stable⟩ := observed.priorStable ready entry (same.symm.trans found) decoded within
    obtain ⟨names, possible, project⟩ := observed.view.crashProjects files runSurvives
    have read := project metadata.header.generation index inode (stable.crashBinding names possible)
    have bytes : files metadata.header.generation index = some payload := by
      simpa [stable.crashBytes] using read
    exact bytes.trans stored.symm
  have selected := ready.resumed.selected
  rw [← ready.walPair, ← same] at selected
  exact ⟨same, agrees, SelectedIntegrityCheckpoint.withRunMap selected agrees.symm⟩

end CheckpointRunInterruption
end Alvoki.Storage.DiskSession
