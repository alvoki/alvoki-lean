import Alvoki.Storage.Disk.Proofs.Collection.SegmentedCollectionBarrierError

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- A reported keeper fsync error after the aligned opener's successful
directory barrier preserves the settled sealed names. The keeper effect
report admits either public outcome, and the exact returned image also
carries any scratch state reported by that callback. -/
theorem BoundedReopenAttempt.errorAtCollectionKeeper {directory : DiskDirectory}
    (attempt : BoundedReopenAttempt) (pending : LockedFileState WalSealedUnlinkImage)
    (scratch : Option (ByteArray × Bool)) (acquired : attempt.acquired = .ok true)
    (acquisition : TryLockObserves pending.owners directory attempt.acquired)
    {plan : Plan} {opened : Reopened} {target : Target}
    (prepared : attempt.prepare directory = .ok (plan, opened, plan.keeperSize))
    (valid : plan.valid = true) (prefixSize : plan.keeperBytes.size = plan.keeperSize) (noPrune : plan.newer = [])
    (keeper : plan.keeper = pending.image.visible.active.first)
    (syncWithNamespace : Array FilePath → EStateM IO.Error (FileImage × WalSealedUnlinkImage) Unit)
    {cause : IO.Error} {nextFiles : FileImage} :
    let files := pending.collectionReopenFiles scratch
    let barrier := syncWithNamespace #[directory.path] (files.image, pending.image)
    let keeperPath := directory.file (.walSegment pending.image.visible.active.first)
    attempt.sync #[directory.path] files.image = projectCollectionBarrier barrier →
    barrier = .ok () (files.image.syncDirectory, pending.image.syncDirectory) →
    attempt.sync #[keeperPath] files.image.syncDirectory = .error cause nextFiles →
    EffectReports target files.image.syncDirectory [.syncKeeper]
      (performPaths directory plan attempt.removeFile throw attempt.write attempt.sync attempt.renameFile) →
    let lock := directory.file .lock
    let outcome := attempt.collectionBarrierCleanup cause
    let next : LockedFileState WalSealedUnlinkImage := ⟨pending.image.syncDirectory, pending.owners.set lock outcome.2⟩
    pending.owners lock = none ∧
      attempt.run directory files = .error outcome.1 (next.collectionReopenFiles nextFiles.keeper.staged) ∧
      (next.collectionReopenFiles nextFiles.keeper.staged).image = nextFiles ∧
      next.image.crashSealed = [pending.image.visible.sealed] ∧
      nextFiles.keeper.active = some pending.image.visible.active.bytes ∧
      nextFiles.keeper.crashImages = [some pending.image.visible.active.bytes] := by
  intro files barrier keeperPath projecting observed directoryKeeperError effects lock outcome next
  have directorySync : attempt.sync #[directory.path] files.image = .ok () files.image.syncDirectory :=
    projecting.trans (congrArg projectCollectionBarrier observed)
  have keeperError : attempt.sync #[directory.file (.walSegment plan.keeper)] files.image.syncDirectory =
      .error cause nextFiles := by
    rw [keeper]
    exact directoryKeeperError
  have head : ReachesAction target files.image.syncDirectory [.syncKeeper] .syncKeeper files.image.syncDirectory :=
    ⟨[], [], rfl, rfl⟩
  have keeperEffect := effects .syncKeeper files.image.syncDirectory head
  simp only [performPaths, keeperError] at keeperEffect
  obtain ⟨publicResult, reportedEffect, exactImage⟩ := keeperEffect
  have durable : files.image.syncDirectory.syncKeeper = files.image.syncDirectory := rfl
  have publicImage : publicResult = files.image.syncDirectory := by
    rcases reportedEffect with unchanged | applied
    · exact unchanged
    · exact (Option.some.inj applied).symm.trans durable
  have reached : nextFiles = files.image.syncDirectory.withScratch nextFiles.keeper.staged := by
    rw [publicImage] at exactImage
    exact exactImage
  have sameFiles : (next.collectionReopenFiles nextFiles.keeper.staged).image = nextFiles := by
    calc
      _ = files.image.syncDirectory.withScratch nextFiles.keeper.staged := rfl
      _ = nextFiles := reached.symm
  have finish : finishBoundedMarkedOpen directory plan plan.keeperSize attempt.removeFile
      attempt.write attempt.sync attempt.renameFile files.image = .error cause nextFiles := by
    simp [finishBoundedMarkedOpen, valid, prefixSize, noPrune, Bind.bind, EStateM.bind, directorySync, keeperError]
  have reads : prepareBoundedMarkedWith directory attempt.readOptional attempt.list attempt.lstat attempt.readBin
      attempt.readPrefix = .ok (plan, opened, plan.keeperSize) := prepared
  have recovered : attempt.recover directory files.image = .error cause nextFiles := by
    unfold BoundedReopenAttempt.recover
    rw [reopenMarkedBoundedWith_readOutcome, reads]
    simp only [finish]
  have returned : attempt.run directory files = .error outcome.1 (next.collectionReopenFiles nextFiles.keeper.staged) := by
    rw [BoundedReopenAttempt.run, acquired, runOpenWithInstallation_outcome, runOpenWithImage_acquired, recovered, ← sameFiles]
    cases unlock : attempt.unlock <;>
      simp [unlock, outcome, next, files, lock, BoundedReopenAttempt.collectionBarrierCleanup,
        LockedFileState.collectionReopenFiles, WalSegmentImage.checkpointReopenFiles]
  exact ⟨acquisition acquired, returned, sameFiles, rfl,
    congrArg (fun image : FileImage => image.keeper.active) reached,
    congrArg (fun image : FileImage => image.keeper.crashImages) reached⟩

/-- A keeper error records the successful directory effect and the exact
file image reported by the subsequent sync. In particular, the scratch
binding for the next open comes from that image. -/
structure PendingCollectionKeeperFailure (directory : DiskDirectory) (scratch : Option (ByteArray × Bool))
    (prior : LockedFileState WalSealedUnlinkImage) where
  attempt : BoundedReopenAttempt
  acquired : attempt.acquired = .ok true
  acquisition : TryLockObserves prior.owners directory attempt.acquired
  localUnlock : attempt.unlock.LocalFlock
  plan : Plan
  reopened : Reopened
  target : Target
  prepared : attempt.prepare directory = .ok (plan, reopened, plan.keeperSize)
  valid : plan.valid = true
  prefixSize : plan.keeperBytes.size = plan.keeperSize
  noPrune : plan.newer = []
  keeper : plan.keeper = prior.image.visible.active.first
  syncWithNamespace : Array FilePath → EStateM IO.Error (FileImage × WalSealedUnlinkImage) Unit
  directoryProjection : let files := (prior.collectionReopenFiles scratch).image
    attempt.sync #[directory.path] files =
      projectCollectionBarrier (syncWithNamespace #[directory.path] (files, prior.image))
  directoryEffect : let files := (prior.collectionReopenFiles scratch).image
    syncWithNamespace #[directory.path] (files, prior.image) =
      .ok () (files.syncDirectory, prior.image.syncDirectory)
  cause : IO.Error
  nextFiles : FileImage
  keeperError : attempt.sync #[directory.file (.walSegment prior.image.visible.active.first)]
      (prior.collectionReopenFiles scratch).image.syncDirectory = .error cause nextFiles
  effects : EffectReports target (prior.collectionReopenFiles scratch).image.syncDirectory [.syncKeeper]
    (performPaths directory plan attempt.removeFile throw attempt.write attempt.sync attempt.renameFile)

namespace PendingCollectionKeeperFailure

variable {directory : DiskDirectory} {scratch : Option (ByteArray × Bool)} {prior : LockedFileState WalSealedUnlinkImage}

def after (report : PendingCollectionKeeperFailure directory scratch prior) : LockedFileState WalSealedUnlinkImage :=
  ⟨prior.image.syncDirectory, prior.owners.set (directory.file .lock)
    (report.attempt.collectionBarrierCleanup report.cause).2⟩

/-- The actual error and cleanup owner determine the next state. Projecting
that state with the returned scratch binding recovers the full file image. -/
theorem returned (report : PendingCollectionKeeperFailure directory scratch prior) :
    report.attempt.run directory (prior.collectionReopenFiles scratch) =
      .error (report.attempt.collectionBarrierCleanup report.cause).1
        (report.after.collectionReopenFiles report.nextFiles.keeper.staged) ∧
    (report.after.collectionReopenFiles report.nextFiles.keeper.staged).image = report.nextFiles := by
  obtain ⟨_, failed, sameFiles, _⟩ :=
    report.attempt.errorAtCollectionKeeper prior scratch report.acquired report.acquisition
      report.prepared report.valid report.prefixSize report.noPrune report.keeper report.syncWithNamespace
      report.directoryProjection report.directoryEffect report.keeperError report.effects
  exact ⟨failed, sameFiles⟩

end PendingCollectionKeeperFailure

end Alvoki.Storage.DiskSession
