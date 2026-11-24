import Alvoki.Storage.Disk.SegmentedCollectionLockHandoff

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- A failing singleton directory barrier may leave the full namespace
unchanged or settle the visible sealed names before reporting the error.
Keeping both components in the report matters when the visible file
projection is identical in both cases. -/
inductive CollectionBarrierErrorEffect (files : FileImage) (pending : WalSealedUnlinkImage) :
    FileImage → WalSealedUnlinkImage → Prop where
  | beforeEffect : CollectionBarrierErrorEffect files pending files pending
  | afterEffect : CollectionBarrierErrorEffect files pending files.syncDirectory pending.syncDirectory

theorem CollectionBarrierErrorEffect.reaches {initial : WalSegmentImage} {pending after : WalSealedUnlinkImage} {files next : FileImage}
    (effect : CollectionBarrierErrorEffect files pending next after)
    (prior : WalSealedUnlinkTrace initial pending) : WalSealedUnlinkTrace initial after := by
  cases effect with
  | beforeEffect => exact prior
  | afterEffect => exact prior.sync

/-- Once the metadata pair is settled, the reported barrier can change
the crash alternatives without changing the visible WAL catalog. -/
theorem CollectionBarrierErrorEffect.keepsVisible {pending after : WalSealedUnlinkImage} {files next : FileImage}
    (effect : CollectionBarrierErrorEffect files pending next after)
    (settled : pending.visible.directory.crashImages = [pending.visible.directory.active]) :
    after.visible = pending.visible := by
  cases effect with
  | beforeEffect => rfl
  | afterEffect =>
    have same : pending.visible.directory.syncDirectory = pending.visible.directory := by
      cases directory : pending.visible.directory
      rw [directory] at settled
      simp only [DirectoryPublication.Image.syncDirectory, DirectoryPublication.Image.mk.injEq, true_and, and_true]
      exact settled.symm
    unfold WalSealedUnlinkImage.syncDirectory WalSealedUnlinkImage.start WalSegmentImage.applyCollectionStep
    rw [same]

private theorem CollectionBarrierErrorEffect.projectFiles {pending : LockedFileState WalSealedUnlinkImage}
    {scratch : Option (ByteArray × Bool)} {after : WalSealedUnlinkImage} {next : FileImage}
    (effect : CollectionBarrierErrorEffect (pending.collectionReopenFiles scratch).image pending.image next after)
    (owners : LockOwners) :
    ((⟨after, owners⟩ : LockedFileState WalSealedUnlinkImage).collectionReopenFiles scratch).image = next := by
  cases effect <;> rfl

/-- The observed full error of the actual first barrier in an aligned
bounded open determines the next pending namespace. The native caller's
unlock report determines which error is returned and which owner remains.
The keeper sync and ready installation are never reached on this path. -/
theorem BoundedReopenAttempt.errorAtCollectionBarrier {directory : DiskDirectory}
    (attempt : BoundedReopenAttempt) (pending : LockedFileState WalSealedUnlinkImage)
    (scratch : Option (ByteArray × Bool)) (acquired : attempt.acquired = .ok true)
    (acquisition : TryLockObserves pending.owners directory attempt.acquired)
    {plan : Plan} {opened : Reopened}
    (prepared : attempt.prepare directory = .ok (plan, opened, plan.keeperSize))
    (valid : plan.valid = true) (prefixSize : plan.keeperBytes.size = plan.keeperSize) (noPrune : plan.newer = [])
    (syncWithNamespace : Array FilePath → EStateM IO.Error (FileImage × WalSealedUnlinkImage) Unit)
    {cause : IO.Error} {nextFiles : FileImage} {nextNamespace : WalSealedUnlinkImage} :
    let files := pending.collectionReopenFiles scratch
    let barrier := syncWithNamespace #[directory.path] (files.image, pending.image)
    attempt.sync #[directory.path] files.image = projectCollectionBarrier barrier →
    barrier = .error cause (nextFiles, nextNamespace) →
    CollectionBarrierErrorEffect files.image pending.image nextFiles nextNamespace →
    let lock := directory.file .lock
    let outcome := match attempt.unlock with
      | .success => (cause, none)
      | .failure cleanup released => (cleanup, if released then none else some attempt.descriptor)
    let next : LockedFileState WalSealedUnlinkImage := ⟨nextNamespace, pending.owners.set lock outcome.2⟩
    pending.owners lock = none ∧
      attempt.run directory files = .error outcome.1 (next.collectionReopenFiles scratch) := by
  intro files barrier projecting observed effect lock outcome next
  have syncError : attempt.sync #[directory.path] files.image = .error cause nextFiles :=
    projecting.trans (congrArg projectCollectionBarrier observed)
  have finish : finishBoundedMarkedOpen directory plan plan.keeperSize attempt.removeFile
      attempt.write attempt.sync attempt.renameFile files.image = .error cause nextFiles := by
    simp [finishBoundedMarkedOpen, valid, prefixSize, noPrune, Bind.bind, EStateM.bind, syncError]
  have reads : prepareBoundedMarkedWith directory attempt.readOptional attempt.list attempt.lstat attempt.readBin
      attempt.readPrefix = .ok (plan, opened, plan.keeperSize) := prepared
  have recovered : attempt.recover directory files.image = .error cause nextFiles := by
    unfold BoundedReopenAttempt.recover
    rw [reopenMarkedBoundedWith_readOutcome, reads]
    simp only [finish]
  have sameFiles : (next.collectionReopenFiles scratch).image = nextFiles := effect.projectFiles next.owners
  refine ⟨acquisition acquired, ?_⟩
  rw [BoundedReopenAttempt.run, acquired, runOpenWithInstallation_outcome, runOpenWithImage_acquired, recovered, ← sameFiles]
  cases unlock : attempt.unlock <;>
    simp [unlock, outcome, next, files, lock, LockedFileState.collectionReopenFiles]

end Alvoki.Storage.DiskSession
