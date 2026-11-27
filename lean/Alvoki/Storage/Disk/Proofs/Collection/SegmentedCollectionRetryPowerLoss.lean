import Alvoki.Storage.Disk.Proofs.Collection.SegmentedCollectionLiveReopen
import Alvoki.Storage.Disk.Proofs.Collection.SegmentedCollectionPowerLoss

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

private theorem BoundedReopenAttempt.failedKeepsOtherOwner {directory : DiskDirectory}
    (attempt : BoundedReopenAttempt) {before after : LockedFileState FileImage} {cause : IO.Error}
    (returned : attempt.run directory before = .error cause after) {path : FilePath}
    (other : path ≠ directory.file .lock) : after.owners path = before.owners path := by
  rw [BoundedReopenAttempt.run, runOpenWithInstallation_outcome] at returned
  by_cases acquired : attempt.acquired = .ok true
  · rw [acquired, runOpenWithImage_acquired] at returned
    cases ran : attempt.recover directory before.image with
    | ok _ _ =>
      rw [ran] at returned
      contradiction
    | error _ _ =>
      rw [ran] at returned
      cases cleanup : attempt.unlock <;>
        rw [cleanup] at returned <;>
          obtain ⟨_, rfl⟩ := EStateM.Result.error.inj returned <;>
          simp [LockOwners.set, other]
  · obtain ⟨_, denied⟩ := runOpenWithImage_notAcquired directory attempt.descriptor attempt.acquired attempt.unlock
      (attempt.recover directory) before acquired
    rw [denied] at returned
    rw [← (EStateM.Result.error.inj returned).2]

/-- Reopen attempts and reference drops may change the reached owner of
this directory, while every other lock keeps its original owner. -/
theorem PendingCollectionOpenTrace.keepsOtherOwner {directory initialScratch initial after scratch}
    (attempts : PendingCollectionOpenTrace directory initialScratch initial after scratch)
    {path : FilePath} (other : path ≠ directory.file .lock) :
    after.owners path = initial.owners path := by
  induction attempts with
  | start => rfl
  | earlyFailure _ attempt _ _ _ returned ih =>
    exact (attempt.failedKeepsOtherOwner returned other).trans ih
  | barrierFailure _ report ih =>
    simpa [PendingCollectionBarrierFailure.after, LockOwners.set, other] using ih
  | keeperFailure _ report ih =>
    simpa [PendingCollectionKeeperFailure.after, LockOwners.set, other] using ih
  | @referenceDrops before scratch description _ references drops ih =>
    change (if (references.remaining drops).isEmpty then
      before.owners.release (directory.file .lock) description else before.owners) path = _
    split
    · unfold LockOwners.release
      split <;> simpa [LockOwners.set, other] using ih
    · exact ih

/-- After the poisoned writer closes, power loss clears whichever owner the
last failed reopen left behind. The selected physical survivors, with the
scratch binding discarded, are the actual input to the next bounded open. -/
theorem SegmentedCollectionPowerLossReport.installsAfterPending {directory before writer descriptor}
    (report : SegmentedCollectionPowerLossReport directory before writer descriptor)
    (observed : report.Valid) (ready : before.RetainedReady directory writer)
    {reached : WalSealedUnlinkImage} (failed : SegmentedCollectionErrors directory before reached)
    {pending : LockedFileState WalSealedUnlinkImage} {scratch : Option (ByteArray × Bool)}
    (attempts : PendingCollectionOpenTrace directory before.files.keeper.staged
      ⟨reached, before.owners.set (directory.file .lock) none⟩ pending scratch)
    (exactCut : report.cut = pending.image) :
    let lock := directory.file .lock
    let released : LockedFileState WalSealedUnlinkImage := ⟨reached, before.owners.set lock none⟩
    let survived := pending.image.crash report.pair report.sealed
    let crashed : LockedFileState WalSealedUnlinkImage := ⟨survived, pending.owners.set lock none⟩
    runCloseWithFiles directory writer .success ((.poisoned : Phase Installed), ⟨reached, before.owners⟩) =
      .ok () (.closed, released) ∧
    WalSealedUnlinkTrace before.wal survived ∧
    ∃ after, report.Installs after ∧ after.RetainedReady directory descriptor ∧
      after.history = before.history ∧ after.checkpoint = before.checkpoint ∧
      ∃ session final,
        report.reopen.run directory (crashed.collectionReopenFiles none) = .ok session final ∧
        session.phase = .ready after.installed ∧ after.files = final.image ∧ after.owners = final.owners := by
  intro lock released survived crashed
  have physical : WalSealedUnlinkTrace before.wal survived :=
    ((attempts.continues (failed.keepsNamespace ready).1).powerLoss
      (exactCut ▸ report.pairSurvives) (exactCut ▸ report.sealedSurvives))
  have owners : crashed.owners = before.owners.release lock writer := by
    change pending.owners.set (directory.file .lock) none = before.owners.release (directory.file .lock) writer
    rw [LockOwners.release_owned ready.held]
    funext path
    by_cases same : path = directory.file .lock
    · simp [LockOwners.set, same]
    · simpa [LockOwners.set, same] using attempts.keepsOtherOwner same
  have exactFiles : crashed.collectionReopenFiles none = report.crashed := by
    unfold SegmentedCollectionPowerLossReport.crashed
    rw [← owners]
    simp [LockedFileState.collectionReopenFiles, crashed, survived,
      SegmentedCollectionPowerLossReport.survivors, exactCut]
  obtain ⟨after, installed, next⟩ := report.installs observed ready
  refine ⟨failed.close ready (phase := .poisoned) (by simp), physical, after, installed, next, installed.history, ?_⟩
  obtain ⟨session, final, _, returned, phase, rfl⟩ := installed.opened
  exact ⟨rfl, session, final, exactFiles.symm ▸ returned, phase, rfl, rfl⟩

end Alvoki.Storage.DiskSession
