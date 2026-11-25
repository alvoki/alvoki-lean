import Alvoki.Storage.Disk.CheckpointRunFileSyncFailureReopen

namespace Alvoki.Storage.CheckpointPublication

open System
open WAL.Boundary (WalInodeImage)

/-- Only ENOENT admits an absent run name. A reported present entry must
be a single-link regular file before any write-open is reached. -/
inductive RejectedRunGuard (lookup : FilePath → EStateM IO.Error WalInodeImage (Except IO.Error IO.FS.Metadata))
    (path : FilePath) (initial : WalInodeImage) : IO.Error → Prop where
  | lookupError
      (observed : lookup path initial = .ok (.error cause) initial)
      (reported : ∀ name message, cause ≠ .noFileOrDirectory name 2 message) :
      RejectedRunGuard lookup path initial cause
  | unprivate
      (observed : lookup path initial = .ok (.ok metadata) initial)
      (rejected : (metadata.type == .file && metadata.numLinks == 1) = false) :
      RejectedRunGuard lookup path initial (IO.userError s!"expected a regular database file with one link: '{path}'")

/-- The actual run callback returns directly from its read-only guard,
with the original cause on a failed lookup and the exact guard error
for a reported unsuitable entry. -/
theorem RejectedRunGuard.returns
    {lookup : FilePath → EStateM IO.Error WalInodeImage (Except IO.Error IO.FS.Metadata)}
    {path : FilePath} {initial : WalInodeImage} {cause : IO.Error}
    (rejected : RejectedRunGuard lookup path initial cause) {handle : Type}
    (openWrite : FilePath → EStateM IO.Error WalInodeImage handle)
    (write : handle → ByteArray → EStateM IO.Error WalInodeImage Unit)
    (flush : handle → EStateM IO.Error WalInodeImage Unit) (bytes : ByteArray) :
    writeCheckpointRunWith lookup openWrite write flush path bytes pure initial = .error cause initial := by
  cases rejected with
  | lookupError observed reported =>
    simp only [writeCheckpointRunWith, optionalMetadataWith, Bind.bind, EStateM.bind, observed]
    rfl
  | unprivate observed rejected =>
    simp [writeCheckpointRunWith, optionalMetadataWith, checkPrivateRegularWith, observed, rejected, Bind.bind,
      EStateM.bind, Pure.pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

end Alvoki.Storage.CheckpointPublication

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

private abbrev Handle := DescriptorInventory × DescriptorSlot
private abbrev State := Cache Handle × WalInodeImage

variable {directory : DiskDirectory} {before : SegmentedWriterState}
  {attempt : SegmentedCheckpointReport directory before}

/-- The guarded write callback uses these reached no-follow observations
at the selected new run. No write handle was acquired by this branch. -/
structure ObservedCheckpointRunGuardFailure (runs : ObservedCheckpointRunPrefix attempt) where
  lookup : FilePath → EStateM IO.Error WalInodeImage (Except IO.Error IO.FS.Metadata)
  openWrite : FilePath → EStateM IO.Error WalInodeImage Handle
  write : Handle → ByteArray → EStateM IO.Error WalInodeImage Unit
  flush : Handle → EStateM IO.Error WalInodeImage Unit
  cause : IO.Error
  rejected : RejectedRunGuard lookup runs.path (runs.atRun runs.index).2 cause
  projected : runs.writeRun runs.path runs.run.run.bytes (runs.atRun runs.index) =
    stageFreshWithCache runs.path runs.run.run.bytes
      (fun path bytes => writeCheckpointRunWith lookup openWrite write flush path bytes pure) (runs.atRun runs.index)

namespace ObservedCheckpointRunGuardFailure

variable {runs : ObservedCheckpointRunPrefix attempt}

/-- The same checked run dispatch fails before the own file sync and
preserves the reached cache and inode state of the prior successful pairs. -/
theorem returnsWrite (failure : ObservedCheckpointRunGuardFailure runs) :
    runs.perform (.writeRun runs.index) (runs.atRun runs.index) =
      .error failure.cause (runs.atRun runs.index) := by
  have exact : runs.writeRun runs.path runs.run.run.bytes (runs.atRun runs.index) =
      .error failure.cause (runs.atRun runs.index) := by
    rw [failure.projected]
    exact stageFreshWithCache_error _ _ _ _ (failure.rejected.returns failure.openWrite failure.write failure.flush _)
  change performCheckpointFileStep directory (SegmentedCheckpointReport.generation before)
    attempt.table.runs.toArray (directory.file .stagedManifest) attempt.manifest
    (fun found => match found with
      | some run => pure run
      | none => throw (IO.userError "checkpoint run index is out of bounds"))
    runs.writeRun runs.writeStage (SyncPathGroup.run (sync directory.path runs.openRead runs.fsync)) runs.rename
    (.writeRun runs.index) (runs.atRun runs.index) = _
  simpa only [performCheckpointFileStep, runs.selected, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure] using exact

theorem returns (failure : ObservedCheckpointRunGuardFailure runs) :
    CheckpointPublication.run attempt.table.runs.length runs.perform (runs.atRun 0) =
      .error failure.cause (runs.atRun runs.index) := by
  apply runs.returnsError
  simp only [Bind.bind, EStateM.bind, failure.returnsWrite]

/-- A rejected run name cannot disturb the old checkpoint. Once the
writer is released, the same reported admitted retry observes the
original selected runs and WAL from that exact reached image. -/
theorem reopens {input : FilePath} {writer : Nat}
    (failure : ObservedCheckpointRunGuardFailure runs)
    (ready : before.RetainedReady directory writer)
    (entry : CheckpointRunPrefix.EntrySelection before (runs.view 0))
    {manifest : State → Publication.Image}
    (entryManifest : manifest (runs.atRun 0) = before.published.manifest)
    (earlierManifest : ∀ index < runs.index, manifest (runs.atRun (index + 1)) = manifest (runs.atRun index))
    (release : SegmentedFailureRelease writer) (retry : LockedFileState FileImage) :
    let reached := runs.atRun runs.index
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
      PriorCheckpointReopened opened session final after := by
  have selected : SelectedRunsAgree before.wal.directory.active.manifest (runs.runs (runs.atRun runs.index)).guaranteed
      before.published.durable := by
    intro bytes metadata visible decoded index inside
    obtain ⟨_, _, stored, stable, _⟩ := runs.priorStable ready entry visible decoded inside
    exact stable.guaranteed.trans stored.symm
  exact runs.reopensPrior failure.returns ready ⟨entryManifest, earlierManifest, rfl⟩ selected release retry

end ObservedCheckpointRunGuardFailure

end Alvoki.Storage.DiskSession
