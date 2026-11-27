import Alvoki.Storage.Disk.RetainedWriterReopen
import Alvoki.Storage.Disk.Proofs.Collection.SegmentedCollectionRetry
import Alvoki.Storage.Disk.SegmentedRetryTrace

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- Bounded reads see the visible namespace. Keep the physical image
alongside this projection until a directory barrier or a crash. -/
def LockedFileState.collectionReopenFiles (pending : LockedFileState WalSealedUnlinkImage)
    (scratch : Option (ByteArray × Bool)) : LockedFileState FileImage :=
  let wal := pending.image.visible
  ⟨wal.checkpointReopenFiles wal.directory scratch, pending.owners⟩

/-- Closing the live description releases the lock and carries the entire
pending sealed namespace, including the still-admitted crash lists. -/
theorem SegmentedCollectionErrors.close {directory before reached descriptor}
    (_failed : SegmentedCollectionErrors directory before reached)
    (ready : before.RetainedReady directory descriptor)
    {phase : Phase Installed} (live : phase ≠ .closed) :
    runCloseWithFiles directory descriptor .success (phase, ⟨reached, before.owners⟩) =
      .ok () (.closed, ⟨reached, before.owners.set (directory.file .lock) none⟩) :=
  runCloseWithFiles_success live ready.held

/-- A denied lock acquisition or read-only preparation error leaves the
pending namespace intact. The returned ownership map includes the actual
unlock result. File-image equality alone would not establish this for a
directory-sync error that may already have taken effect. -/
theorem BoundedReopenAttempt.keepsPendingCollectionBeforeBarrier {directory : DiskDirectory}
    (attempt : BoundedReopenAttempt) (pending : LockedFileState WalSealedUnlinkImage)
    (scratch : Option (ByteArray × Bool))
    (early : attempt.acquired ≠ .ok true ∨ ∃ cause, attempt.prepare directory = .error cause)
    {cause : IO.Error} {after : LockedFileState FileImage}
    (returned : attempt.run directory (pending.collectionReopenFiles scratch) = .error cause after) :
    let next := { pending with owners := after.owners }
    next.collectionReopenFiles scratch = after ∧ next.image = pending.image := by
  intro next
  let before := pending.collectionReopenFiles scratch
  have unchanged : after.image = before.image := by
    rcases early with denied | ⟨error, preparation⟩
    · obtain ⟨_, refused⟩ := runOpenWithImage_notAcquired directory attempt.descriptor attempt.acquired
        attempt.unlock (attempt.recover directory) before denied
      change attempt.run directory before = _ at returned
      rw [BoundedReopenAttempt.run, runOpenWithInstallation_outcome, refused] at returned
      exact congrArg LockedFileState.image (EStateM.Result.error.inj returned).2.symm
    · have observed := runOpenWithInstallation_boundedPreparationError directory attempt.descriptor attempt.nextRef
        attempt.acquired attempt.unlock attempt.readOptional attempt.list attempt.lstat attempt.readBin attempt.readPrefix
        attempt.removeFile attempt.write attempt.sync attempt.renameFile before (fun _ => preparation)
      change attempt.run directory before = _ at observed
      rw [returned] at observed
      cases lockReport : attempt.acquired with
      | error lockError =>
        rw [lockReport] at observed
        exact congrArg LockedFileState.image (EStateM.Result.error.inj observed).2
      | ok acquired =>
        cases acquired with
        | false =>
          rw [lockReport] at observed
          exact congrArg LockedFileState.image (EStateM.Result.error.inj observed).2
        | true =>
          rw [lockReport] at observed
          cases unlock : attempt.unlock <;> rw [unlock] at observed <;>
            exact (congrArg LockedFileState.image (EStateM.Result.error.inj observed).2 : _)
  exact ⟨by cases after; simp_all [next, before, LockedFileState.collectionReopenFiles], rfl⟩

/-- The bounded worker's projection of the observed full barrier result.
The full callback also records the sealed namespace, even when the
directory sync leaves the worker's file-image projection equal. -/
def projectCollectionBarrier
    (result : EStateM.Result IO.Error (FileImage × WalSealedUnlinkImage) Unit) :
    EStateM.Result IO.Error FileImage Unit :=
  match result with
  | .ok () (files, _) => .ok () files
  | .error cause (files, _) => .error cause files

/-- After close, or after an early failed open, the actual bounded worker
uses the still-visible sealed files. Its successful directory barrier
makes that exact list durable before the keeper barrier and installation. -/
theorem SegmentedCollectionErrors.openAfterRelease {directory before reached descriptor}
    (failed : SegmentedCollectionErrors directory before reached)
    (ready : before.RetainedReady directory descriptor)
    {current : WalSealedUnlinkImage} (attempted : current = reached ∨ current = reached.syncDirectory)
    {owners : LockOwners} {scratch : Option (ByteArray × Bool)} (attempt : BoundedReopenAttempt)
    (acquired : attempt.acquired = .ok true) (acquisition : TryLockObserves owners directory attempt.acquired)
    (raw : HealthyBoundedWalReports directory (owners.set (directory.file .lock) (some attempt.descriptor))
      attempt.descriptor current.visible current.visible.directory.active before.target.range.watermark
      before.published.durable ByteArray.empty)
    (exactReads : attempt.recover directory =
      raw.reopen attempt.removeFile attempt.write attempt.sync attempt.renameFile)
    (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < attempt.nextRef)
    (syncWithNamespace : Array FilePath → EStateM IO.Error (FileImage × WalSealedUnlinkImage) Unit) :
    let pending : LockedFileState WalSealedUnlinkImage := ⟨current, owners⟩
    let files := pending.collectionReopenFiles scratch
    let barrier := syncWithNamespace #[directory.path] (files.image, pending.image)
    attempt.sync #[directory.path] files.image = projectCollectionBarrier barrier →
    barrier = .ok () (files.image.syncDirectory, pending.image.syncDirectory) →
    attempt.sync #[directory.file (.walSegment current.visible.active.first)] files.image.syncDirectory =
      .ok () files.image.syncDirectory.syncKeeper →
    WalSealedUnlinkTrace before.wal pending.image.syncDirectory ∧
    ∃ session final, ∃ next : SegmentedWriterState,
      attempt.run directory files = .ok session final ∧
      session.directory = directory ∧ session.descriptor = attempt.descriptor ∧
      session.phase = .ready next.installed ∧ next.files = final.image ∧ next.owners = final.owners ∧
      next.wal.sealed = pending.image.syncDirectory.visible.sealed ∧
      pending.image.syncDirectory.crashSealed = [next.wal.sealed] ∧
      next.target.pair = before.target.pair ∧ next.history = before.history ∧ next.checkpoint = before.checkpoint ∧
      next.RetainedReady directory attempt.descriptor ∧
      next.wal = { pending.image.syncDirectory.visible with directory := final.image.directory } ∧
      next.published.durable = before.published.durable := by
  intro pending files barrier sameBarrier observedBarrier syncKeeper
  have syncDirectory : attempt.sync #[directory.path] files.image = .ok () files.image.syncDirectory :=
    sameBarrier.trans (congrArg projectCollectionBarrier observedBarrier)
  have initial := (failed.keepsNamespace ready).1
  have trace : WalSealedUnlinkTrace before.wal current := by
    rcases attempted with rfl | rfl
    · exact initial
    · exact initial.sync
  have retry := (trace.projects ready.layout).1
  obtain ⟨session, final, next, returned, path, descriptor, phase, image, owners, wal, pair, history, _, durable, nextReady⟩ :=
    ready.openAfterCollection retry raw scratch liveRefs fresh
      (acquired ▸ acquisition) attempt.unlock attempt.removeFile attempt.write attempt.sync attempt.renameFile
      syncDirectory syncKeeper
  have actual : attempt.run directory files = .ok session final := by
    rw [BoundedReopenAttempt.run, acquired, exactReads]
    exact returned
  have originalPair : current.visible.directory.active = before.target.pair :=
    (retry.keepsSettledPair ready.walDirectorySettled).1.trans ready.walPair
  have selectedNext := nextReady.resumed.selected
  rw [durable, pair, ← originalPair] at selectedNext
  have selectedPrior : SelectedIntegrityCheckpoint before.published.durable current.visible.directory.active.manifest
      before.checkpoint := originalPair.symm ▸ ready.resumed.selected
  have checkpoint := Except.ok.inj ((raw.readCheckpoint selectedNext).symm.trans (raw.readCheckpoint selectedPrior))
  have sealed : next.wal.sealed = current.visible.sealed := by rw [wal]
  exact ⟨trace.sync, session, final, next, actual, path, descriptor, phase, image, owners, sealed, by rw [sealed]; rfl,
    pair, history, checkpoint, nextReady, wal, durable⟩

end Alvoki.Storage.DiskSession
