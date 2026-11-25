import Alvoki.Storage.Disk.HeldLaterWalPrune
import Alvoki.Storage.Disk.ListedDirectoryAuthorizationFailure

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

variable {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout before.image history}
  {operations : MarkedRetryChunkOperations (Cache (DescriptorInventory × DescriptorSlot × Nat)) directory layout}
  {published : CheckpointPublication.Image}
  {held : HeldDirectoryMarkedRetryReports operations published}
  {authorization : ListedDirectoryAuthorization held}

private theorem unlinkEffects {initial reached : FileImage} {target : Target}
    (prior : EffectTrace target initial reached) (names : List Nat)
    (later : ∀ first ∈ names, target.range.through < first) :
    EffectTrace target initial (names.foldl FileImage.unlinkLater reached) := by
  induction names generalizing reached with
  | nil => exact prior
  | cons first more ih =>
    exact ih (prior.unlink (later first List.mem_cons_self))
      (fun first listed => later first (List.mem_cons_of_mem _ listed))

/-- A propagated unlink error carries the reached ordered prefix and
the failed unlink's own effect into the same admitted open cleanup. The
native result determines the next retry image and the unlock result
determines the returned error and owner. -/
theorem ListedDirectoryAuthorization.continuesAfterUnlinkError
    (authorization : ListedDirectoryAuthorization held)
    {input : FilePath} {source : LockedFileState FileImage} {admits : Target → Prop}
    (metadata : HeldMarkedMetadata held) (completed : authorization.outcome = .completed)
    (long : layout.keeper.bytes.size < authorization.keeper.metadata.byteSize.toNat)
    {earlier rest : List Nat} {first : Nat} {bindings final : FilePath → Option Nat}
    (order : before.image.later.visible = earlier ++ first :: rest)
    (passed : HeldLaterWalUnlinks held before.image.syncDirectory bindings earlier final)
    (failed : HeldLaterWalUnlinkFailure held first (earlier.foldl FileImage.unlinkLater before.image.syncDirectory))
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
    let cleanup := (operations.cachedAttempt localUnlock).cleanupError failed.cause failed.reached
    operations.runWithAdmission admission = .error cleanup.1 cleanup.2 ∧
    BoundedReopenTrace directory admits source cleanup.2 ∧ cleanup.2.image = failed.reached ∧
    match operations.unlock with
    | .success => cleanup.1 = failed.cause ∧ cleanup.2.owners (directory.file .lock) = none
    | .failure unlockError _ =>
      cleanup.1 = unlockError ∧ cleanup.2.owners (directory.file .lock) = some operations.slot.description := by
  have later : ∀ first ∈ before.image.later.visible, layout.range.through < first :=
    laterValid _ List.mem_cons_self
  have prefixTrace : EffectTrace layout.target before.image
      (earlier.foldl FileImage.unlinkLater before.image.syncDirectory) :=
    unlinkEffects .authorized earlier (fun first listed => later first (order ▸ List.mem_append_left _ listed))
  have effect : EffectTrace layout.target before.image failed.reached := by
    rcases failed.effect with unchanged | removed
    · rw [unchanged]
      exact prefixTrace
    · rw [removed]
      exact prefixTrace.unlink (later first (order ▸ List.mem_append_right _ List.mem_cons_self))
  have finish := authorization.finishAfterUnlinkError completed long later order passed failed
  have physical : authorization.keeper.metadata.byteSize.toNat = layout.plan.keeperBytes.size :=
    authorization.keeper.extent
  rw [physical] at finish
  exact metadata.continuesAfterRepairError admission localUnlock keeperValid laterValid following accepted ordered
    finish effect prior admitted

private abbrev afterUnlinks : FileImage := before.image.unlinkVisibleSuffix

private def heldImage (image : FileImage) : LockedFileState FileImage :=
  ⟨image, before.owners.set (directory.file .lock) (some operations.slot.description)⟩

private abbrev remembered (authorization : ListedDirectoryAuthorization held) :=
  operations.cache.captureKeeper (directory.file (.walSegment layout.keeper.first))
    (authorization.keeper.inventory, authorization.keeper.slot, 0)
    layout.keeper.bytes.size authorization.keeper.metadata.byteSize.toNat

/-- The error path has completed every unlink but the suffix barrier
reports an error. The reached drop and binding observations retain the
same directory handle and lock until the failed syscall. -/
structure HeldLaterWalBarrierFailure (authorization : ListedDirectoryAuthorization held) where
  completed : authorization.outcome = .completed
  bindings : FilePath → Option Nat
  listedBindings : ∀ first ∈ before.image.later.visible,
    bindings (directory.file (.walSegment first)) =
      (held.lifetime.namespaceView.child held.lifetime.root (renderWalSegmentName first)).map
        held.lifetime.namespaceView.modelObject
  reached : FilePath → Option Nat
  unlinks : HeldLaterWalUnlinks held before.image.syncDirectory bindings before.image.later.visible reached
  afterAuthorization : List LockReferenceDrop
  directoryRetained : held.lifetime.directorySlot ∈
    (held.listing.afterClose.afterDrops (authorization.afterListing ++ afterAuthorization)).slots
  lockRetained : operations.slot ∈
    (held.listing.afterClose.afterDrops (authorization.afterListing ++ afterAuthorization)).slots
  directoryBound : reached directory.path = some (operations.descriptors.inode held.lifetime.directorySlot.description)
  lockBound : reached (directory.file .lock) = some (operations.descriptors.inode operations.slot.description)
  cause : IO.Error
  effective : Bool
  effect :
    let image := afterUnlinks (before := before)
    authorization.fsync (operations.descriptors, held.lifetime.directorySlot, 0) (heldImage (operations := operations) image) =
      .error cause (heldImage (operations := operations) (if effective then image.syncDirectory else image))
  projection : ∀ cache,
    readWalKeeperWithChunks operations.reads (directory.file (.walSegment layout.keeper.first))
      layout.keeper.bytes.size authorization.keeper.metadata.byteSize.toNat
      (operations.cache, heldImage (operations := operations) before.image) =
      .ok layout.keeper.bytes (cache, heldImage (operations := operations) before.image) →
    operations.sync operations.cache #[directory.path] (afterUnlinks (before := before)) =
      projectDirectorySync (SyncPathGroup.run (sync directory.path authorization.openRead authorization.fsync)
        #[directory.path] (cache, heldImage (operations := operations) (afterUnlinks (before := before))))

namespace HeldLaterWalBarrierFailure

/-- The reported barrier uses the original directory inode and lock slot
after the completed unlink prefix. The grouped callback keeps the exact
reported state and wraps its syscall error. -/
theorem barrierError (failure : HeldLaterWalBarrierFailure authorization) :
    let atBarrier := held.listing.afterClose.afterDrops (authorization.afterListing ++ failure.afterAuthorization)
    let image := afterUnlinks (before := before)
    held.lifetime.directorySlot ∈ atBarrier.slots ∧ operations.slot ∈ atBarrier.slots ∧
    failure.reached directory.path = some (atBarrier.inode held.lifetime.directorySlot.description) ∧
    failure.reached (directory.file .lock) = some (atBarrier.inode operations.slot.description) ∧
    operations.sync operations.cache #[directory.path] image =
      .error (IO.userError s!"sync failed for '{directory.path}': {failure.cause}")
        (if failure.effective then image.syncDirectory else image) := by
  intro atBarrier image
  refine ⟨failure.directoryRetained, failure.lockRetained, ?_, ?_, ?_⟩
  · simpa only [atBarrier, DescriptorInventory.afterDrops, held.listing.afterClose_eq] using failure.directoryBound
  · simpa only [atBarrier, DescriptorInventory.afterDrops, held.listing.afterClose_eq] using failure.lockBound
  · have read := (held.keeperRead_syncListedDirectory authorization.keeper authorization.fits
      authorization.afterListing authorization.directoryRetained authorization.bindings authorization.bound
      authorization.outcome (heldImage (operations := operations) before.image)
      authorization.openRead authorization.fsync authorization.effect).1
    have captured : (remembered authorization).directory = some (operations.descriptors, held.lifetime.directorySlot, 0) := by
      simp only [remembered, Cache.captureKeeper]
      split <;> exact held.capturedDirectory
    let reached := heldImage (operations := operations) image
    have routed : sync directory.path authorization.openRead authorization.fsync directory.path
        (remembered authorization, reached) =
        withCache (remembered authorization)
          (authorization.fsync (operations.descriptors, held.lifetime.directorySlot, 0) reached) := by
      simp [sync, Cache.resolve, captured]
    rw [failure.projection _ read, SyncPathGroup.run_single, routed, failure.effect]
    rfl

/-- The bounded finisher stops at the failed suffix barrier after the
whole ordered unlink pass. Neither staging nor keeper publication runs. -/
theorem finishError (failure : HeldLaterWalBarrierFailure authorization)
    (long : layout.keeper.bytes.size < authorization.keeper.metadata.byteSize.toNat)
    (later : ∀ first ∈ before.image.later.visible, layout.range.through < first) :
    let image := afterUnlinks (before := before)
    finishBoundedMarkedOpen directory layout.boundedPlan layout.plan.keeperBytes.size
      operations.removeFile (operations.write operations.cache) (operations.sync operations.cache)
      operations.renameFile before.image =
    .error (IO.userError s!"sync failed for '{directory.path}': {failure.cause}")
      (if failure.effective then image.syncDirectory else image) := by
  intro image
  let run := performPaths directory layout.boundedPlan operations.removeFile throw
    (operations.write operations.cache) (operations.sync operations.cache) operations.renameFile
  have size : layout.boundedPlan.keeperBytes.size = layout.boundedPlan.keeperSize := layout.target.trimmedSize
  have valid : layout.boundedPlan.valid = true :=
    (Plan.valid_iff layout.boundedPlan).mpr ⟨layout.target.firstCovered, Nat.le_of_eq size.symm, later⟩
  have physical : authorization.keeper.metadata.byteSize.toNat = layout.plan.keeperBytes.size :=
    authorization.keeper.extent
  have larger : layout.boundedPlan.keeperSize < layout.plan.keeperBytes.size := size ▸ (physical ▸ long)
  have unlinks : ((layout.boundedPlan.newer.map Step.unlink).forM run) before.image.syncDirectory = .ok () image :=
    failure.unlinks.returned layout.boundedPlan
  have barrier : run .syncPruned image =
      .error (IO.userError s!"sync failed for '{directory.path}': {failure.cause}")
        (if failure.effective then image.syncDirectory else image) := failure.barrierError.2.2.2.2
  have failed : (((layout.boundedPlan.newer.map Step.unlink) ++ [Step.syncPruned]).forM run)
      before.image.syncDirectory =
      .error (IO.userError s!"sync failed for '{directory.path}': {failure.cause}")
        (if failure.effective then image.syncDirectory else image) := by
    rw [List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM]
    simp only [Bind.bind, EStateM.bind, unlinks, List.forM_eq_forM, List.forM_cons, barrier]
  have unfoldFinish := congrFun
    (finishBoundedMarkedOpen_long directory layout.boundedPlan layout.plan.keeperBytes.size
      operations.removeFile (operations.write operations.cache) (operations.sync operations.cache)
      operations.renameFile valid size larger) before.image
  rw [unfoldFinish]
  change (do
    operations.sync operations.cache #[directory.path]
    ((layout.boundedPlan.newer.map Step.unlink) ++ [Step.syncPruned]).forM run
    run (.replace .writeStaged)
    run (.replace .syncStaged)
    run (.replace .renameStaged)
    run (.replace .syncDirectory)
    pure () : EStateM IO.Error FileImage Unit) before.image = _
  simp only [authorization.settles failure.completed, Bind.bind, EStateM.bind, failed]

/-- Both failed suffix-barrier timings continue the same admitted retry.
A reported sync effect settles the already absent later names. -/
theorem continuesAfterError {input : FilePath} {source : LockedFileState FileImage} {admits : Target → Prop}
    (failure : HeldLaterWalBarrierFailure authorization) (metadata : HeldMarkedMetadata held)
    (long : layout.keeper.bytes.size < authorization.keeper.metadata.byteSize.toNat)
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
    let image := afterUnlinks (before := before)
    let reached := if failure.effective then image.syncDirectory else image
    let cause := IO.userError s!"sync failed for '{directory.path}': {failure.cause}"
    let cleanup := (operations.cachedAttempt localUnlock).cleanupError cause reached
    operations.runWithAdmission admission = .error cleanup.1 cleanup.2 ∧
    BoundedReopenTrace directory admits source cleanup.2 ∧ cleanup.2.image = reached ∧
    match operations.unlock with
    | .success => cleanup.1 = cause ∧ cleanup.2.owners (directory.file .lock) = none
    | .failure unlockError _ =>
      cleanup.1 = unlockError ∧ cleanup.2.owners (directory.file .lock) = some operations.slot.description := by
  have later : ∀ first ∈ before.image.later.visible, layout.range.through < first := laterValid _ List.mem_cons_self
  have unlinks : EffectTrace layout.target before.image (afterUnlinks (before := before)) :=
    unlinkEffects .authorized _ later
  have reached : EffectTrace layout.target before.image
      (if failure.effective then (afterUnlinks (before := before)).syncDirectory else afterUnlinks (before := before)) := by
    cases effective : failure.effective
    · simpa only [effective, Bool.false_eq_true, ite_false] using unlinks
    · simpa only [effective, ite_true] using unlinks.syncPruned
  exact metadata.continuesAfterRepairError admission localUnlock keeperValid laterValid following accepted ordered
    (failure.finishError long later) reached prior admitted

end HeldLaterWalBarrierFailure
end Alvoki.Storage.DiskSession
