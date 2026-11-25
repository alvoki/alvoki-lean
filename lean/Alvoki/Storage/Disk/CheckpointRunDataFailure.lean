import Alvoki.Storage.Disk.CheckpointRunOpenFailure
import Alvoki.Storage.Disk.StagedHandleCustody

namespace Alvoki.Storage.CheckpointPublication

open System SyncHandleRouting

/-- A returned file-data error occurs either in a write, or in the
flush reached after that same handle's write succeeds. The precise
intermediate physical state and the partial target effects are reported. -/
inductive RunDataWriteFailure {handle state : Type} (write : handle → ByteArray → EStateM IO.Error state Unit)
    (flush : handle → EStateM IO.Error state Unit) (descriptor : handle) (bytes : ByteArray)
    (opened : state) (cause : IO.Error) : state → Prop where
  | writeError (failed : write descriptor bytes opened = .error cause reached) :
    RunDataWriteFailure write flush descriptor bytes opened cause reached
  | flushError (written : write descriptor bytes opened = .ok () buffered)
      (failed : flush descriptor buffered = .error cause reached) :
    RunDataWriteFailure write flush descriptor bytes opened cause reached

/-- The error branch drops the unretained handle. In the pinned runtime
its finalizer calls `fclose`; the finalizer's status does not override
the earlier callback error. Retain its reported reached file effects. -/
abbrev runDataDropImage {handle state : Type} (drop : handle → EStateM IO.Error state Unit) (descriptor : handle)
    (reached : state) : state := dataErrorDropState drop descriptor reached

abbrev dropHandleOnDataError {handle state : Type} (drop : handle → EStateM IO.Error state Unit)
    (descriptor : handle) (action : EStateM IO.Error state Unit) : EStateM IO.Error state Unit :=
  withDataErrorDrop drop descriptor action

/-- Project the reached primitive error and the error branch's local
handle drop onto the actual checked write/flush/retain schedule. -/
theorem RunDataWriteFailure.returns {handle state : Type}
    {lookup : FilePath → EStateM IO.Error state (Except IO.Error IO.FS.Metadata)} {path : FilePath} {before opened : state}
    (guard : AcceptedRunGuard lookup path before)
    {openWrite : FilePath → EStateM IO.Error state handle} {descriptor : handle}
    (openedFile : openWrite path before = .ok descriptor opened)
    {write : handle → ByteArray → EStateM IO.Error state Unit} {flush : handle → EStateM IO.Error state Unit}
    {bytes : ByteArray} {cause : IO.Error} {reached : state}
    (failure : RunDataWriteFailure write flush descriptor bytes opened cause reached)
    (drop : handle → EStateM IO.Error state Unit) :
    writeCheckpointRunWith lookup openWrite
      (fun h payload => dropHandleOnDataError drop h (write h payload))
      (fun h => dropHandleOnDataError drop h (flush h)) path bytes pure before =
      .error cause (runDataDropImage drop descriptor reached) := by
  have data :
      (dropHandleOnDataError drop descriptor (write descriptor bytes) >>= fun _ =>
        dropHandleOnDataError drop descriptor (flush descriptor) >>= fun _ => pure descriptor) opened =
      .error cause (runDataDropImage drop descriptor reached) := by
    cases failure with
    | writeError failed => simp only [Bind.bind, EStateM.bind, dropHandleOnDataError, withDataErrorDrop, failed]
    | flushError written failed => simp only [Bind.bind, EStateM.bind, dropHandleOnDataError, withDataErrorDrop, written, failed]
  rcases guard with ⟨_, _, absent⟩ | ⟨metadata, present, regular, privateFile⟩
  · simpa [writeCheckpointRunWith, optionalMetadataWith, absent, openedFile, Bind.bind, EStateM.bind, Pure.pure,
      EStateM.pure] using data
  · have fileKind : (IO.FS.FileType.file == .file) = true := rfl
    simpa [writeCheckpointRunWith, optionalMetadataWith, checkPrivateRegularWith, present, regular, privateFile, fileKind,
      openedFile, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure] using data

end Alvoki.Storage.CheckpointPublication

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

private abbrev Handle := DescriptorInventory × DescriptorSlot
private abbrev State := Cache Handle × WalInodeImage
private abbrev RunIO := EStateM IO.Error WalInodeImage

variable {directory : DiskDirectory} {before : SegmentedWriterState}
  {attempt : SegmentedCheckpointReport directory before}

/-- The selected callback uses the admitted private path and the exact
handle returned by its successful write-open. Operation and finalizer
reports permit arbitrary reached bytes on that inode. The callback
adds a cache entry only after write and flush succeed. -/
structure ObservedCheckpointRunDataFailure (runs : ObservedCheckpointRunPrefix attempt) where
  lookup : FilePath → RunIO (Except IO.Error IO.FS.Metadata)
  openWrite : FilePath → RunIO Handle
  write : Handle → ByteArray → RunIO Unit
  flush : Handle → RunIO Unit
  drop : Handle → RunIO Unit
  guard : AcceptedRunGuard lookup runs.path (runs.atRun runs.index).2
  inventory : DescriptorInventory
  slot : DescriptorSlot
  live : slot.reference ∈ inventory.references slot.description
  afterOpen : WalInodeImage
  opened : openWrite runs.path (runs.atRun runs.index).2 = .ok (inventory, slot) afterOpen
  openView : RunDirectoryInodeView directory afterOpen (runs.runs ((runs.atRun runs.index).1, afterOpen))
  truncated : RunOpenTruncation (path := runs.path) lookup (runs.view runs.index) openView (inventory.inode slot.description)
  cause : IO.Error
  stopped : WalInodeImage
  failed : RunDataWriteFailure write flush (inventory, slot) runs.run.run.bytes afterOpen cause stopped
  view : let reached := runDataDropImage drop (inventory, slot) stopped
    RunDirectoryInodeView directory reached (runs.runs ((runs.atRun runs.index).1, reached))
  sameVisibleNames : view.visible = openView.visible
  frame : RunWriteInodeFrame runs.path (inventory.inode slot.description)
    (runDataDropImage drop (inventory, slot) stopped) openView view
  projected : runs.writeRun runs.path runs.run.run.bytes (runs.atRun runs.index) =
    stageFreshWithCache runs.path runs.run.run.bytes
      (fun path bytes => writeCheckpointRunWith lookup openWrite
        (fun h payload => dropHandleOnDataError drop h (write h payload))
        (fun h => dropHandleOnDataError drop h (flush h)) path bytes pure)
      (runs.atRun runs.index)

namespace ObservedCheckpointRunDataFailure

variable {runs : ObservedCheckpointRunPrefix attempt}

def reached (failure : ObservedCheckpointRunDataFailure runs) : State :=
  ((runs.atRun runs.index).1, runDataDropImage failure.drop (failure.inventory, failure.slot) failure.stopped)

/-- The original data error used the live opened description at the
selected path. That path still names the same inode after the drop. -/
theorem reachedBinding (failure : ObservedCheckpointRunDataFailure runs) :
    failure.slot.reference ∈ failure.inventory.references failure.slot.description ∧
    failure.view.visible runs.path = some (failure.inventory.inode failure.slot.description) := by
  refine ⟨failure.live, ?_⟩
  rw [failure.sameVisibleNames]
  exact failure.truncated.bound

/-- The checked run dispatch returns the precise post-finalization
state and original error without remembering a pending handle. -/
theorem returnsWrite (failure : ObservedCheckpointRunDataFailure runs) :
    runs.perform (.writeRun runs.index) (runs.atRun runs.index) = .error failure.cause failure.reached := by
  have exact : runs.writeRun runs.path runs.run.run.bytes (runs.atRun runs.index) =
      .error failure.cause failure.reached := by
    rw [failure.projected]
    exact stageFreshWithCache_error _ _ _ _ (failure.failed.returns failure.guard failure.opened failure.drop)
  change performCheckpointFileStep directory (SegmentedCheckpointReport.generation before)
    attempt.table.runs.toArray (directory.file .stagedManifest) attempt.manifest
    (fun found => match found with
      | some run => pure run
      | none => throw (IO.userError "checkpoint run index is out of bounds"))
    runs.writeRun runs.writeStage (SyncPathGroup.run (sync directory.path runs.openRead runs.fsync)) runs.rename
    (.writeRun runs.index) (runs.atRun runs.index) = _
  simpa only [performCheckpointFileStep, runs.selected, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure] using exact

/-- The selected run's own file sync and the remaining checkpoint steps
are unreachable after either data callback fails. -/
theorem returns (failure : ObservedCheckpointRunDataFailure runs) :
    CheckpointPublication.run attempt.table.runs.length runs.perform (runs.atRun 0) =
      .error failure.cause failure.reached := by
  apply runs.returnsError
  simp only [Bind.bind, EStateM.bind, failure.returnsWrite]

/-- Preserve each prior run through the private create or truncate,
then through the reported failed write/flush and local handle drop. -/
theorem priorRuns (failure : ObservedCheckpointRunDataFailure runs) {writer : Nat}
    (ready : before.RetainedReady directory writer)
    (entry : CheckpointRunPrefix.EntrySelection before (runs.view 0)) :
    SelectedRunsAgree before.wal.directory.active.manifest (runs.runs failure.reached).guaranteed
      before.published.durable := by
  intro raw metadata binding decoded index within
  obtain ⟨_, _, stored, stable, separated⟩ := runs.priorStable ready entry binding decoded within
  have privateAtEntry := failure.truncated.links.privateBinding failure.guard
  have privateAfterOpen : ∀ other, failure.openView.visible other = some (failure.inventory.inode failure.slot.description) →
      other = runs.path := by
    intro other bound
    by_cases same : other = runs.path
    · exact same
    · exact privateAtEntry other ((failure.truncated.frame.visibleNames other same).symm.trans bound)
  have opened := failure.truncated.frame.keepsStableOnSyncError (effective := false) rfl privateAtEntry separated stable
  have retained := failure.frame.keepsStableOnSyncError (effective := false) rfl privateAfterOpen separated opened
  exact retained.guaranteed.trans stored.symm

/-- Once the exact poisoned writer releases the lock, the reported
admitted retry recovers the prior checkpoint and unchanged WAL, for
either error and any admitted local data and finalizer effects. -/
theorem reopens {input : FilePath} {writer : Nat}
    (failure : ObservedCheckpointRunDataFailure runs)
    (ready : before.RetainedReady directory writer)
    (entry : CheckpointRunPrefix.EntrySelection before (runs.view 0))
    {manifest : State → Publication.Image} (frames : RunPrefixManifestFrames runs failure.reached manifest)
    (release : SegmentedFailureRelease writer) (retry : LockedFileState FileImage) :
    let publication := (runs.runs failure.reached).project (manifest failure.reached)
    BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
      ⟨CheckpointPowerCut.physical before publication, before.owners.set (directory.file .lock) none⟩ retry →
    CheckpointHeldOpen.Reports input directory before retry publication publication →
    ∃ (layout : CanonicalKeeperLayout retry.image before.history)
      (opened : CheckpointHeldOpen input directory layout publication)
      (session : SegmentedSession) (final : LockedFileState FileImage) (after : SegmentedWriterState),
      runPreparedCheckpoint attempt.prepared runs.perform (.ready before.installed, ⟨runs.atRun 0, before.owners⟩) =
        .error failure.cause (.poisoned, ⟨failure.reached, before.owners⟩) ∧
      release.Observed (directory := directory) (.poisoned, ⟨failure.reached, before.owners⟩)
        ⟨failure.reached, before.owners.set (directory.file .lock) none⟩ ∧
      PriorCheckpointReopened opened session final after :=
  runs.reopensPrior failure.returns ready frames (failure.priorRuns ready entry) release retry

end ObservedCheckpointRunDataFailure

end Alvoki.Storage.DiskSession
