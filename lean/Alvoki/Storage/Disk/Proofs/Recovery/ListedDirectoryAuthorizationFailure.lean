import Alvoki.Storage.Disk.Proofs.Recovery.ListedDirectoryAuthorization
import Alvoki.Storage.Disk.SegmentedRetryTrace

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

variable {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout before.image history}
  {operations : MarkedRetryChunkOperations (Cache (DescriptorInventory × DescriptorSlot × Nat)) directory layout}
  {published : CheckpointPublication.Image}
  {report : HeldDirectoryMarkedRetryReports operations published}

def MarkedRetryChunkOperations.cachedAttempt
    (operations : MarkedRetryChunkOperations files directory layout) (localUnlock : operations.unlock.LocalFlock) :
    CachedOpenAttempt directory before :=
  operations.reported.withReaders (m := EStateM IO.Error FileImage) operations.reads.readPrefix
    fun optional runSize runPrefix list lstat readSeal readKeeper =>
      { descriptor := operations.slot.description
        nextRef := operations.nextRef
        acquisition := operations.acquired ▸ operations.acquisition
        unlock := operations.unlock
        localUnlock := localUnlock
        readOptional := optional
        readRunSize := runSize
        readRunPrefix := runPrefix
        list := list
        lstat := lstat
        readSeal := readSeal
        readKeeper := readKeeper
        removeFile := operations.removeFile
        write := operations.write operations.cache
        sync := operations.sync operations.cache
        renameFile := operations.renameFile }

theorem MarkedRetryChunkOperations.runWithAdmission_eq_cached
    (operations : MarkedRetryChunkOperations files directory layout) {input : FilePath}
    (admission : OpenAdmissionReports input directory operations.slot) (localUnlock : operations.unlock.LocalFlock)
    (markerPresent : operations.MarkerPresent) :
    operations.runWithAdmission admission = (operations.cachedAttempt localUnlock).run := by
  rw [operations.runWithAdmission_eq admission, operations.run_selectsMarked markerPresent]
  simp only [MarkedRetryChunkOperations.markedAt, operations.keeperReads]
  rfl

/-- Exact checkpoint and marker reads from the held directory supply the
cached attempt's checked preparation without modifying the file image. -/
theorem HeldMarkedMetadata.cachedAttemptPrepared (metadata : HeldMarkedMetadata report)
    (localUnlock : operations.unlock.LocalFlock)
    (laterValid : before.image.later.Beyond layout.range.through)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      before.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history) :
    ∃ opened, (operations.cachedAttempt localUnlock).prepare before.image =
      .ok (layout.boundedPlan, opened, layout.plan.keeperBytes.size) before.image := by
  obtain ⟨watermark, _, _, count, _, _, absolute⟩ := DirectoryPublication.Bindings.walRange_accounting layout.decoded
  have byteCount : (WAL.encode history).size = count.toNat := by
    rw [absolute, layout.through, WAL.encode_size, Nat.mul_comm]
  obtain ⟨checkpoint, _, _, selected, _, _, _, _, _, _⟩ :=
    selectedCheckpoint_replays watermark accepted (byteCount ▸ count.toNat_lt_size) ordered
  let sizes := SizedCheckpointRunReports.ofChunkReads (checkpoint := checkpoint) selected operations.reads
    operations.metadata report.chunkReads
  have reads := metadata.callbackMetadata
  obtain ⟨opened, _, _, prepared, _⟩ :=
    operations.reported.prepares before.image laterValid following accepted ordered sizes reads.manifestRead
      reads.markerRead
  exact ⟨opened, prepared⟩

/-- Exact read preparation and a reported finisher error determine the
admitted result, its cleanup, and the next state of the bounded retry. -/
theorem HeldMarkedMetadata.continuesAfterRepairError {input : FilePath} {source : LockedFileState FileImage}
    {admits : Target → Prop} (metadata : HeldMarkedMetadata report)
    (admission : OpenAdmissionReports input directory operations.slot)
    (localUnlock : operations.unlock.LocalFlock)
    (keeperValid : before.image.keeper.Valid layout.target.Accepts)
    (laterValid : before.image.later.Beyond layout.range.through)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      before.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    {cause : IO.Error} {reached : FileImage}
    (finish : finishBoundedMarkedOpen directory layout.boundedPlan layout.plan.keeperBytes.size
      operations.removeFile (operations.write operations.cache) (operations.sync operations.cache)
      operations.renameFile before.image = .error cause reached)
    (effects : EffectTrace layout.target before.image reached)
    (prior : BoundedReopenTrace directory admits source before) (admitted : admits layout.target) :
    let cleanup := (operations.cachedAttempt localUnlock).cleanupError cause reached
    operations.runWithAdmission admission = .error cleanup.1 cleanup.2 ∧
    BoundedReopenTrace directory admits source cleanup.2 ∧ cleanup.2.image = reached ∧
    match operations.unlock with
    | .success => cleanup.1 = cause ∧ cleanup.2.owners (directory.file .lock) = none
    | .failure unlockError _ =>
      cleanup.1 = unlockError ∧ cleanup.2.owners (directory.file .lock) = some operations.slot.description := by
  intro cleanup
  let attempt := operations.cachedAttempt localUnlock
  obtain ⟨opened, preparedRead⟩ := metadata.cachedAttemptPrepared localUnlock laterValid following accepted ordered
  have ran := attempt.run_repairError preparedRead finish
  have prepared : Prepared before.image layout.target layout.plan :=
    ⟨rfl, keeperValid, laterValid, rfl, rfl, rfl, layout.visible⟩
  exact ⟨(operations.runWithAdmission_eq_cached admission localUnlock metadata.callbackMetadata.markerPresent).trans ran,
    .cachedRepairFailed prior attempt admitted prepared effects ran,
    attempt.cleanupError_keepsFiles _ _, by
      cases reported : operations.unlock <;>
        simp [cleanup, MarkedRetryChunkOperations.cachedAttempt, CachedOpenAttempt.cleanupError,
          CachedRetryReadReports.withReaders, reported, LockOwners.set]⟩

namespace ListedDirectoryAuthorization

/-- A reported failure of the first grouped directory barrier returns
through the actual admitted marked schedule. The sync observation
determines the reached image before cleanup. Cleanup can replace the
reported sync error with its own error and retain the acquired owner.
This same failed attempt extends the retry lineage. -/
theorem continuesAfterError {input : FilePath} {source : LockedFileState FileImage} {admits : Target → Prop}
    (observed : ListedDirectoryAuthorization report) (metadata : HeldMarkedMetadata report)
    (failed : observed.outcome ≠ .completed)
    (admission : OpenAdmissionReports input directory operations.slot)
    (localUnlock : operations.unlock.LocalFlock)
    (keeperValid : before.image.keeper.Valid layout.target.Accepts)
    (laterValid : before.image.later.Beyond layout.range.through)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      before.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (prior : BoundedReopenTrace directory admits source before) (admitted : admits layout.target) :
    ∃ failure : CachedOpenAuthorizationFailure directory before,
      operations.runWithAdmission admission = .error failure.error failure.after ∧
      failure.attempt.descriptor = operations.slot.description ∧ failure.attempt.unlock = operations.unlock ∧
      BoundedReopenTrace directory admits source failure.after ∧
      (match observed.outcome with
      | .completed => False
      | .errorBeforeEffect cause =>
        failure.cause = IO.userError s!"sync failed for '{directory.path}': {cause}" ∧
        failure.after.image = before.image
      | .errorAfterEffect cause =>
        failure.cause = IO.userError s!"sync failed for '{directory.path}': {cause}" ∧
        failure.after.image = before.image.syncDirectory) := by
  let attempt := operations.cachedAttempt localUnlock
  obtain ⟨opened, preparedRead⟩ := metadata.cachedAttemptPrepared localUnlock laterValid following accepted ordered
  rw [layout.boundedPlan_eq_extract] at preparedRead
  have valid : Prepared before.image layout.target layout.plan :=
    ⟨rfl, keeperValid, laterValid, rfl, rfl, rfl, layout.visible⟩
  have cleanup {cause : IO.Error} {reached : FileImage}
      (edge : attempt.sync #[directory.path] before.image = .error cause reached)
      (timing : reached = before.image ∨ reached = before.image.syncDirectory) :
      ∃ failure : CachedOpenAuthorizationFailure directory before,
        operations.runWithAdmission admission = .error failure.error failure.after ∧
        failure.attempt.descriptor = operations.slot.description ∧ failure.attempt.unlock = operations.unlock ∧
        BoundedReopenTrace directory admits source failure.after ∧ failure.cause = cause ∧
        failure.after.image = reached := by
    have reported : MetadataReport before.image (attempt.sync #[directory.path]) := by
      unfold MetadataReport
      rw [edge]
      exact timing
    let failure : CachedOpenAuthorizationFailure directory before :=
      ⟨attempt, layout.target, layout.plan, opened, valid, preparedRead, cause, reached, edge, reported⟩
    exact ⟨failure, (operations.runWithAdmission_eq_cached admission localUnlock metadata.callbackMetadata.markerPresent).trans failure.run_error,
      rfl, rfl, .cachedAuthorizationFailed prior failure admitted, rfl, attempt.cleanupError_keepsFiles cause reached⟩
  have sync := observed.syncResult
  change attempt.sync #[directory.path] before.image = _ at sync
  cases effect : observed.outcome with
  | completed => exact False.elim (failed effect)
  | errorBeforeEffect cause =>
    rw [effect] at sync
    obtain ⟨failure, result, descriptor, unlock, retries, exactCause, image⟩ := cleanup sync (.inl rfl)
    exact ⟨failure, result, descriptor, unlock, retries, exactCause, image⟩
  | errorAfterEffect cause =>
    rw [effect] at sync
    obtain ⟨failure, result, descriptor, unlock, retries, exactCause, image⟩ := cleanup sync (.inr rfl)
    exact ⟨failure, result, descriptor, unlock, retries, exactCause, image⟩

end ListedDirectoryAuthorization
end Alvoki.Storage.DiskSession
