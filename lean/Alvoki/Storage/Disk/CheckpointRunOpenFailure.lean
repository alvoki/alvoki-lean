import Alvoki.Storage.Disk.CheckpointRunFileSyncFailureReopen

namespace Alvoki.Storage.CheckpointPublication

open System DiskSession
open WAL.Boundary (WalInodeImage)

/-- A reported no-follow admission reaches the write-open. Its returned
error stops before writing, flushing, or retaining a Lean handle. -/
theorem AcceptedRunGuard.returnsOpenError {state handle : Type} {path : FilePath} {before reached : state}
    {lookup : FilePath → EStateM IO.Error state (Except IO.Error IO.FS.Metadata)}
    (guard : AcceptedRunGuard lookup path before)
    {openWrite : FilePath → EStateM IO.Error state handle} {cause : IO.Error}
    (failed : openWrite path before = .error cause reached)
    (write : handle → ByteArray → EStateM IO.Error state Unit) (flush : handle → EStateM IO.Error state Unit)
    (bytes : ByteArray) :
    writeCheckpointRunWith lookup openWrite write flush path bytes pure before = .error cause reached := by
  rcases guard with ⟨_, _, absent⟩ | ⟨metadata, present, regular, privateFile⟩
  · simp [writeCheckpointRunWith, optionalMetadataWith, absent, failed, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  · have fileKind : (IO.FS.FileType.file == .file) = true := rfl
    simp [writeCheckpointRunWith, optionalMetadataWith, checkPrivateRegularWith, present, regular, privateFile, fileKind,
      failed, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

/-- A successful raw write-open makes the selected inode visible with
zero bytes before its Lean handle is wrapped. The complete link census
uses the same no-follow lookup as the guard. A reported missing name
at entry was absent from the same namespace, while a reported present
name is a link to this inode. Its surviving bytes and name still come
from the physical report. -/
structure RunOpenTruncation {directory : DiskDirectory} {before reached : WalInodeImage}
    {oldRuns newRuns : RunUnlinkImage} {path : FilePath}
    (lookup : FilePath → EStateM IO.Error WalInodeImage (Except IO.Error IO.FS.Metadata))
    (entry : RunDirectoryInodeView directory before oldRuns)
    (after : RunDirectoryInodeView directory reached newRuns) (inode : Nat) where
  links : RunOpenLinkCensus (path := path) (before := before) lookup entry.visible inode
  absent : ∀ name message,
    lookup path before = .ok (.error (.noFileOrDirectory name 2 message)) before → entry.visible path = none
  bound : after.visible path = some inode
  emptied : reached.visible inode = ByteArray.empty
  frame : RunWriteInodeFrame path inode reached entry after

theorem RunOpenTruncation.priorBinding {directory : DiskDirectory} {before reached : WalInodeImage}
    {oldRuns newRuns : RunUnlinkImage} {path : FilePath}
    {lookup : FilePath → EStateM IO.Error WalInodeImage (Except IO.Error IO.FS.Metadata)}
    {entry : RunDirectoryInodeView directory before oldRuns}
    {after : RunDirectoryInodeView directory reached newRuns} {inode : Nat}
    (effects : RunOpenTruncation (path := path) lookup entry after inode)
    (guard : AcceptedRunGuard lookup path before) :
    entry.visible path = none ∨ entry.visible path = some inode := by
  rcases guard with ⟨name, message, absent⟩ | ⟨metadata, found, _, _⟩
  · exact .inl (effects.absent name message absent)
  · exact .inr ((effects.links.complete path).mp (effects.links.counted metadata found).1)

end Alvoki.Storage.CheckpointPublication

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

private abbrev Handle := DescriptorInventory × DescriptorSlot
private abbrev State := Cache Handle × WalInodeImage
private abbrev NativeWriteState := DescriptorInventory × WalInodeImage
private abbrev Lookup := FilePath → EStateM IO.Error WalInodeImage (Except IO.Error IO.FS.Metadata)

variable {directory : DiskDirectory} {before : SegmentedWriterState}
  {attempt : SegmentedCheckpointReport directory before}

/-- The two reported Linux write-open errors have different effects.
A no-effect raw error leaves the whole reached prefix alone. A successful
raw create or truncate followed by a failed wrapper leaves a fresh
close-on-exec descriptor live, with its effects at the selected path. -/
inductive RunWriteOpenError (runs : ObservedCheckpointRunPrefix attempt) (lookup : Lookup)
    (initial : DescriptorInventory) : (reached : WalInodeImage) →
    RunDirectoryInodeView directory reached (runs.runs ((runs.atRun runs.index).1, reached)) →
    DescriptorInventory → Prop where
  | rawOpenFailed : RunWriteOpenError runs lookup initial (runs.atRun runs.index).2 (runs.view runs.index) initial
  | handleWrapFailed {reached : WalInodeImage}
      {view : RunDirectoryInodeView directory reached (runs.runs ((runs.atRun runs.index).1, reached))}
      (raw : DescriptorSlot) (free : ∀ previous ∈ initial.slots, previous.address ≠ raw.address)
      (fresh : initial.references raw.description = []) (closeOnExec : raw.reference.closeOnExec = true)
      (truncated : RunOpenTruncation (path := runs.path) lookup (runs.view runs.index) view (initial.inode raw.description)) :
      RunWriteOpenError runs lookup initial reached view (initial.insert raw free)

namespace RunWriteOpenError

variable {runs : ObservedCheckpointRunPrefix attempt} {lookup : Lookup}
  {initial census : DescriptorInventory} {reached : WalInodeImage}
  {view : RunDirectoryInodeView directory reached (runs.runs ((runs.atRun runs.index).1, reached))}

/-- Opening a new file description does not add a reference to any
previously live description, including the one that owns the lock. -/
theorem keepsReferences (effect : RunWriteOpenError runs lookup initial reached view census)
    {description : Nat} (live : initial.references description ≠ []) :
    census.references description = initial.references description := by
  cases effect with
  | rawOpenFailed => rfl
  | handleWrapFailed raw free fresh _ _ =>
    have distinct : raw.description ≠ description := by
      intro same
      exact live (same ▸ fresh)
    rw [DescriptorInventory.references_insert, ite_eq_right distinct]

/-- Either raw open made no change, or exactly one fresh raw reference
is added by the successful create or truncate. The failed wrapper does
not register a Lean handle and does not close the raw slot. -/
theorem reachedRawSlot (effect : RunWriteOpenError runs lookup initial reached view census)
    (guard : AcceptedRunGuard lookup runs.path (runs.atRun runs.index).2) :
    (reached = (runs.atRun runs.index).2 ∧ census = initial) ∨
    ∃ raw : DescriptorSlot,
      initial.references raw.description = [] ∧ census.references raw.description = [raw.reference] ∧
      raw.reference.closeOnExec = true ∧
      ((runs.view runs.index).visible runs.path = none ∨
        (runs.view runs.index).visible runs.path = some (initial.inode raw.description)) ∧
      view.visible runs.path = some (initial.inode raw.description) ∧
      reached.visible (initial.inode raw.description) = ByteArray.empty := by
  cases effect with
  | rawOpenFailed => exact .inl ⟨rfl, rfl⟩
  | handleWrapFailed raw free fresh closeOnExec truncated =>
    exact .inr ⟨raw, fresh, by simp [DescriptorInventory.references_insert, fresh], closeOnExec,
      truncated.priorBinding guard, truncated.bound, truncated.emptied⟩

/-- The reported namespace and inode effects preserve the previously
selected run at any other path. -/
theorem keepsStable (effect : RunWriteOpenError runs lookup initial reached view census)
    (guard : AcceptedRunGuard lookup runs.path (runs.atRun runs.index).2)
    {path : FilePath} {inode : Nat} {bytes : ByteArray} (separate : path ≠ runs.path)
    (prior : (runs.view runs.index).Stable path inode bytes) : view.Stable path inode bytes := by
  cases effect with
  | rawOpenFailed => exact prior
  | handleWrapFailed _ _ _ _ truncated =>
    exact truncated.frame.keepsStableOnSyncError (effective := false) rfl
      (truncated.links.privateBinding guard) separate prior

end RunWriteOpenError

private def projectWriteOpen (initial : DescriptorInventory)
    (native : FilePath → EStateM IO.Error NativeWriteState Handle) : FilePath → EStateM IO.Error WalInodeImage Handle :=
  fun path image => match native path (initial, image) with
    | .ok descriptor reached => .ok descriptor reached.2
    | .error cause reached => .error cause reached.2

/-- The selected checked run reports a returned write-open error from
the admitted guard. The actual callback projection preserves the
reached file image and exposes the raw census from the same error. -/
structure ObservedCheckpointRunOpenFailure (runs : ObservedCheckpointRunPrefix attempt) where
  lookup : Lookup
  write : Handle → ByteArray → EStateM IO.Error WalInodeImage Unit
  flush : Handle → EStateM IO.Error WalInodeImage Unit
  guard : AcceptedRunGuard lookup runs.path (runs.atRun runs.index).2
  initial : DescriptorInventory
  openWrite : FilePath → EStateM IO.Error NativeWriteState Handle
  cause : IO.Error
  reached : NativeWriteState
  report : openWrite runs.path (initial, (runs.atRun runs.index).2) = .error cause reached
  view : RunDirectoryInodeView directory reached.2 (runs.runs ((runs.atRun runs.index).1, reached.2))
  effect : RunWriteOpenError runs lookup initial reached.2 view reached.1
  projected : runs.writeRun runs.path runs.run.run.bytes (runs.atRun runs.index) =
    stageFreshWithCache runs.path runs.run.run.bytes
      (fun path bytes => writeCheckpointRunWith lookup (projectWriteOpen initial openWrite) write flush path bytes pure)
      (runs.atRun runs.index)

namespace ObservedCheckpointRunOpenFailure

variable {runs : ObservedCheckpointRunPrefix attempt}

def reachedFiles (failure : ObservedCheckpointRunOpenFailure runs) : State :=
  ((runs.atRun runs.index).1, failure.reached.2)

/-- The failed actual write-open never remembers a pending handle and
returns the precise file image where it stopped. -/
theorem returnsWrite (failure : ObservedCheckpointRunOpenFailure runs) :
    runs.perform (.writeRun runs.index) (runs.atRun runs.index) = .error failure.cause failure.reachedFiles := by
  have failed : projectWriteOpen failure.initial failure.openWrite runs.path (runs.atRun runs.index).2 =
      .error failure.cause failure.reached.2 := by
    simp only [projectWriteOpen, failure.report]
  have exact : runs.writeRun runs.path runs.run.run.bytes (runs.atRun runs.index) =
      .error failure.cause failure.reachedFiles := by
    rw [failure.projected]
    exact stageFreshWithCache_error _ _ _ _ (failure.guard.returnsOpenError failed failure.write failure.flush _)
  change performCheckpointFileStep directory (SegmentedCheckpointReport.generation before)
    attempt.table.runs.toArray (directory.file .stagedManifest) attempt.manifest
    (fun found => match found with
      | some run => pure run
      | none => throw (IO.userError "checkpoint run index is out of bounds"))
    runs.writeRun runs.writeStage (SyncPathGroup.run (sync directory.path runs.openRead runs.fsync)) runs.rename
    (.writeRun runs.index) (runs.atRun runs.index) = _
  simpa only [performCheckpointFileStep, runs.selected, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure] using exact

theorem returns (failure : ObservedCheckpointRunOpenFailure runs) :
    CheckpointPublication.run attempt.table.runs.length runs.perform (runs.atRun 0) =
      .error failure.cause failure.reachedFiles := by
  apply runs.returnsError
  simp only [Bind.bind, EStateM.bind, failure.returnsWrite]

/-- Both reported write-open errors preserve the manifest-selected runs
even when the next generation's private inode was created or truncated. -/
theorem priorRuns (failure : ObservedCheckpointRunOpenFailure runs) {writer : Nat}
    (ready : before.RetainedReady directory writer)
    (entry : CheckpointRunPrefix.EntrySelection before (runs.view 0)) :
    SelectedRunsAgree before.wal.directory.active.manifest (runs.runs failure.reachedFiles).guaranteed
      before.published.durable := by
  intro raw metadata binding decoded index within
  obtain ⟨_, _, stored, stable, separated⟩ := runs.priorStable ready entry binding decoded within
  have retained := failure.effect.keepsStable failure.guard separated stable
  exact retained.guaranteed.trans stored.symm

/-- From this exact poisoned worker's released file image, the same
reported admitted open returns the prior physical checkpoint and WAL.
The raw census above is kept separately, with no availability premise
for retry beyond the reported admission and lock release. -/
theorem reopens {input : FilePath} {writer : Nat}
    (failure : ObservedCheckpointRunOpenFailure runs)
    (ready : before.RetainedReady directory writer)
    (entry : CheckpointRunPrefix.EntrySelection before (runs.view 0))
    {manifest : State → Publication.Image} (frames : RunPrefixManifestFrames runs failure.reachedFiles manifest)
    (release : SegmentedFailureRelease writer) (retry : LockedFileState FileImage) :
    let reached := failure.reachedFiles
    let publication := (runs.runs reached).project (manifest reached)
    BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
      ⟨CheckpointPowerCut.physical before publication, before.owners.set (directory.file .lock) none⟩ retry →
    CheckpointHeldOpen.Reports input directory before retry publication publication →
    ∃ (layout : CanonicalKeeperLayout retry.image before.history)
      (opened : CheckpointHeldOpen input directory layout publication)
      (session : SegmentedSession) (final : LockedFileState FileImage) (after : SegmentedWriterState),
      runPreparedCheckpoint attempt.prepared runs.perform (.ready before.installed, ⟨runs.atRun 0, before.owners⟩) =
        .error failure.cause (.poisoned, ⟨reached, before.owners⟩) ∧
      release.Observed (directory := directory) (.poisoned, ⟨reached, before.owners⟩)
        ⟨reached, before.owners.set (directory.file .lock) none⟩ ∧
      PriorCheckpointReopened opened session final after :=
  runs.reopensPrior failure.returns ready frames (failure.priorRuns ready entry) release retry

end ObservedCheckpointRunOpenFailure

end Alvoki.Storage.DiskSession
