import Alvoki.Storage.Disk.Proofs.Recovery.ListedStagedKeeperRepair
import Alvoki.Storage.Disk.Proofs.Filesystem.StagedHandleCustody

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

private abbrev Handle := DescriptorInventory × DescriptorSlot × Nat
private abbrev Files := LockedFileState FileImage
private abbrev Staging := EStateM IO.Error Files

/-- Reports for the native staged-file callback. A write or flush error
drops the unretained handle and preserves the original error. -/
structure StageWriteCallbacks where
  tryCreate : FilePath → Staging (Except IO.Error Handle)
  stat : FilePath → Staging (Except IO.Error IO.FS.Metadata)
  unlink : FilePath → Staging (Except IO.Error Unit)
  create : FilePath → Staging Handle
  write : Handle → ByteArray → Staging Unit
  flush : Handle → Staging Unit
  drop : Handle → Staging Unit

namespace StageWriteCallbacks

noncomputable def detach (callbacks : StageWriteCallbacks) : FilePath → Staging Unit :=
  removeStaleStagingWith callbacks.stat callbacks.unlink

noncomputable def run (callbacks : StageWriteCallbacks) : FilePath → ByteArray → Staging Handle :=
  writeFreshStagedWith callbacks.tryCreate callbacks.detach callbacks.create
    (fun handle bytes => withDataErrorDrop callbacks.drop handle (callbacks.write handle bytes))
    (fun handle => withDataErrorDrop callbacks.drop handle (callbacks.flush handle))

/-- The opening phase is reached through the first exclusive create, or
through the exact EEXIST branch and its stale-name cleanup. -/
inductive Opening (callbacks : StageWriteCallbacks) (path : FilePath) (initial : Files) :
    EStateM.Result IO.Error Files Handle → Prop where
  | opened
      (returned : callbacks.tryCreate path initial = .ok (.ok handle) reached) :
      Opening callbacks path initial (.ok handle reached)
  | rejected
      (returned : callbacks.tryCreate path initial = .ok (.error cause) reached)
      (direct : ∀ filename details, cause ≠ .alreadyExists filename 17 details) :
      Opening callbacks path initial (.error cause reached)
  | detachFailed
      (conflict : callbacks.tryCreate path initial = .ok (.error (.alreadyExists filename 17 details)) collided)
      (returned : callbacks.detach path collided = .error cause reached) :
      Opening callbacks path initial (.error cause reached)
  | retried
      (conflict : callbacks.tryCreate path initial = .ok (.error (.alreadyExists filename 17 details)) collided)
      (detached : callbacks.detach path collided = .ok () ready)
      (returned : callbacks.create path ready = result) :
      Opening callbacks path initial result

private theorem Opening.uses {callbacks : StageWriteCallbacks} {path : FilePath} {initial : Files}
    {result : EStateM.Result IO.Error Files Handle} (opening : callbacks.Opening path initial result)
    (use : Handle → Staging α) :
    withFreshStaging callbacks.tryCreate callbacks.detach callbacks.create path use initial =
      match result with
      | .ok handle reached => use handle reached
      | .error cause reached => .error cause reached := by
  cases opening with
  | opened returned =>
    simp [withFreshStaging, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, returned]
  | @rejected cause reached returned direct =>
    simp only [withFreshStaging, Bind.bind, EStateM.bind, returned]
    rfl
  | detachFailed conflict returned =>
    simp [withFreshStaging, Bind.bind, EStateM.bind, conflict, returned]
  | retried conflict detached returned =>
    simp only [withFreshStaging, Bind.bind, EStateM.bind, conflict, detached, returned]
    cases result <;> rfl

end StageWriteCallbacks

private def scratchFiles (initial : Files) (value : Option (ByteArray × Bool)) : Files :=
  { initial with image := initial.image.withScratch value }

private def stagePrefix (initial : Files) (bytes : ByteArray) (count : Nat) : Files :=
  scratchFiles initial (some (bytes.extract 0 count, false))

/-- An opening failure can retain the original scratch, leave the
reserved path absent, or report a newly created empty scratch. -/
inductive FailedStageOpening (callbacks : StageWriteCallbacks) (path : FilePath) (initial : Files)
    (cause : IO.Error) : Files → Prop where
  | retained (opening : callbacks.Opening path initial (.error cause initial)) :
      FailedStageOpening callbacks path initial cause initial
  | absent (opening : callbacks.Opening path initial (.error cause (scratchFiles initial none))) :
      FailedStageOpening callbacks path initial cause (scratchFiles initial none)
  | created (opening : callbacks.Opening path initial (.error cause (stagePrefix initial ByteArray.empty 0))) :
      FailedStageOpening callbacks path initial cause (stagePrefix initial ByteArray.empty 0)

/-- Write, flush and the local `fclose` use the same unretained handle.
The report identifies the scratch bytes after finalization, which can
still flush buffered data. The staged-file sync has yet to take place. -/
inductive StageWriteFailure (callbacks : StageWriteCallbacks) (path : FilePath) (bytes : ByteArray)
    (initial : Files) (cause : IO.Error) : Files → Prop where
  | opening (failed : FailedStageOpening callbacks path initial cause reached) :
      StageWriteFailure callbacks path bytes initial cause reached
  | write
      (opening : callbacks.Opening path initial (.ok handle (stagePrefix initial bytes 0)))
      (failed : callbacks.write handle bytes (stagePrefix initial bytes 0) =
        .error cause stopped)
      (bounded : count ≤ bytes.size)
      (finalized : dataErrorDropState callbacks.drop handle stopped = stagePrefix initial bytes count) :
      StageWriteFailure callbacks path bytes initial cause (stagePrefix initial bytes count)
  | flush
      (opening : callbacks.Opening path initial (.ok handle (stagePrefix initial bytes 0)))
      (buffered : bufferedCount ≤ bytes.size)
      (written : callbacks.write handle bytes (stagePrefix initial bytes 0) =
        .ok () (stagePrefix initial bytes bufferedCount))
      (failed : callbacks.flush handle (stagePrefix initial bytes bufferedCount) =
        .error cause stopped)
      (bounded : count ≤ bytes.size)
      (finalized : dataErrorDropState callbacks.drop handle stopped = stagePrefix initial bytes count) :
      StageWriteFailure callbacks path bytes initial cause (stagePrefix initial bytes count)

namespace StageWriteFailure

/-- The fresh-write schedule returns the original error with the reached
image after any reported local handle finalization. -/
theorem returns {callbacks : StageWriteCallbacks} {path : FilePath} {bytes : ByteArray}
    {initial reached : Files} {cause : IO.Error} (failure : StageWriteFailure callbacks path bytes initial cause reached) :
    callbacks.run path bytes initial = .error cause reached := by
  unfold StageWriteCallbacks.run writeFreshStagedWith
  cases failure with
  | opening failed =>
    cases failed <;> exact StageWriteCallbacks.Opening.uses ‹_› _
  | write opening failed bounded finalized =>
    rw [opening.uses]
    simp [Bind.bind, EStateM.bind, withDataErrorDrop, failed, finalized]
  | flush opening buffered written failed bounded finalized =>
    rw [opening.uses]
    simp [Bind.bind, EStateM.bind, withDataErrorDrop, written, failed, finalized]

/-- Failed staging changes at most the reserved scratch field and
keeps the reached owner map. -/
theorem onlyScratch {callbacks : StageWriteCallbacks} {path : FilePath} {bytes : ByteArray}
    {initial reached : Files} {cause : IO.Error} (failure : StageWriteFailure callbacks path bytes initial cause reached) :
    reached.owners = initial.owners ∧ reached.image = initial.image.withScratch reached.image.keeper.staged := by
  cases failure with
  | opening failed => cases failed <;> exact ⟨rfl, rfl⟩
  | write | flush => exact ⟨rfl, rfl⟩

end StageWriteFailure

variable {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout before.image history}
  {operations : MarkedRetryChunkOperations (Cache Handle) directory layout}
  {published : CheckpointPublication.Image}
  {held : HeldDirectoryMarkedRetryReports operations published}
  {authorization : ListedDirectoryAuthorization held}

/-- The bounded worker consumes the same failed native-shaped staged
write over the exact reached suffix-settlement state. -/
structure ListedStagedWriteFailure (pruning : LongKeeperPruning authorization) where
  callbacks : StageWriteCallbacks
  cause : IO.Error
  reached : Files
  failed : StageWriteFailure callbacks (directory.file .stagedWal) layout.keeper.bytes pruning.stageInput cause reached
  projection :
    operations.write operations.cache (directory.file .stagedWal) layout.keeper.bytes pruning.stageInput.image =
      projectDirectorySync (stageFreshWithCache (directory.file .stagedWal) layout.keeper.bytes callbacks.run
        (operations.cache, pruning.stageInput))

namespace ListedStagedWriteFailure

variable {pruning : LongKeeperPruning authorization}

/-- Failure never remembers a staged descriptor in the pending cache.
The native-shaped callback and the bounded worker agree on the exact
filesystem image and original error. -/
theorem stageError (failure : ListedStagedWriteFailure pruning) :
    let path := directory.file .stagedWal
    stageFreshWithCache path layout.keeper.bytes failure.callbacks.run (operations.cache, pruning.stageInput) =
      .error failure.cause (operations.cache, failure.reached) ∧
    operations.write operations.cache path layout.keeper.bytes pruning.stageInput.image =
      .error failure.cause failure.reached.image := by
  intro path
  have cached := stageFreshWithCache_error operations.cache path layout.keeper.bytes failure.callbacks.run
    failure.failed.returns
  exact ⟨cached, by rw [failure.projection, cached]; rfl⟩

/-- The bounded finisher stops before the staged-file sync, rename and
final directory barrier on either successful suffix-pruning route. -/
theorem finishError (failure : ListedStagedWriteFailure pruning) :
    finishBoundedMarkedOpen directory layout.boundedPlan authorization.keeper.metadata.byteSize.toNat
      operations.removeFile (operations.write operations.cache) (operations.sync operations.cache)
      operations.renameFile before.image = .error failure.cause failure.reached.image := by
  have bytes := layout.boundedPlan_extractKeeper
  rw [pruning.finishAfterPrune]
  simp only [performPaths, Publication.performReplacement, Bind.bind, EStateM.bind, bytes, failure.stageError.2]

/-- The already authorized keeper, checkpoint and sealed WAL choices
remain usable after failed staging. The reached scratch can be discarded
by the next retry. -/
theorem preservesRepair (failure : ListedStagedWriteFailure pruning) :
    EffectTrace layout.target before.image failure.reached.image := by
  rw [failure.failed.onlyScratch.2]
  exact .scratch pruning.stageInputEffects.1

end ListedStagedWriteFailure

end Alvoki.Storage.DiskSession
