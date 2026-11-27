import Alvoki.Storage.Disk.Proofs.Recovery.ListedPrunedAlignedKeeper
import Alvoki.Storage.Disk.Proofs.Recovery.ListedDirectoryAuthorizationFailure

namespace Alvoki.Storage.DiskSession.ListedPrunedAlignedKeeper

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

variable {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout before.image history}
  {operations : MarkedRetryChunkOperations (Cache (DescriptorInventory × DescriptorSlot × Nat)) directory layout}
  {published : CheckpointPublication.Image}
  {held : HeldDirectoryMarkedRetryReports operations published}
  {authorization : ListedDirectoryAuthorization held}
  {prune : ListedLaterWalPrune authorization}

private abbrev settledSuffix : FileImage := before.image.unlinkVisibleSuffix.syncDirectory

private def acquired (operations : MarkedRetryChunkOperations (Cache (DescriptorInventory × DescriptorSlot × Nat))
    directory layout) : LockedFileState FileImage :=
  ⟨settledSuffix (before := before), before.owners.set (directory.file .lock) (some operations.slot.description)⟩

/-- The bounded finisher propagates the grouped error from the exact
retained keeper descriptor. An effective error settles the keeper while
both outcomes retain the already settled suffix. -/
theorem finishError (repair : ListedPrunedAlignedKeeper prune)
    (later : ∀ first ∈ before.image.later.visible, layout.range.through < first)
    {cause : IO.Error} {nativeReached : LockedFileState FileImage}
    (failed : authorization.fsync (authorization.keeper.inventory, authorization.keeper.slot, 0)
      (acquired operations) = .error cause nativeReached) :
    let path := directory.file (.walSegment layout.keeper.first)
    let image := settledSuffix (before := before)
    finishBoundedMarkedOpen directory layout.boundedPlan layout.plan.keeperBytes.size
      operations.removeFile (operations.write operations.cache) (operations.sync operations.cache)
      operations.renameFile before.image =
    .error (IO.userError s!"sync failed for '{path}': {cause}")
      (if repair.effective then image.syncKeeper else image) := by
  intro path image
  have finish := repair.finishResult later
  rw [authorization.keeper.extent] at finish
  have projected := repair.syncResult
  change operations.sync operations.cache #[path] image =
    (match authorization.fsync (authorization.keeper.inventory, authorization.keeper.slot, 0) (acquired operations) with
    | .ok () _ => EStateM.Result.ok () image.syncKeeper
    | .error reported _ => EStateM.Result.error (IO.userError s!"sync failed for '{path}': {reported}")
        (if repair.effective then image.syncKeeper else image)) at projected
  rw [failed] at projected
  exact finish.trans projected

private theorem effects (repair : ListedPrunedAlignedKeeper prune)
    (later : ∀ first ∈ before.image.later.visible, layout.range.through < first) :
    let image := settledSuffix (before := before)
    EffectTrace layout.target before.image (if repair.effective then image.syncKeeper else image) := by
  intro image
  have pruned : EffectTrace layout.target before.image image :=
    ((EffectTrace.authorized (target := layout.target) (initial := before.image)).unlinks
      before.image.later.visible later).syncPruned
  by_cases effective : repair.effective = true
  · obtain ⟨gone, _, _, keeper⟩ := ListedLaterWalPrune.settledImage before.image
    have lengths : (layout.keeper.bytes ++ layout.tail).size = layout.keeper.bytes.size :=
      authorization.keeper.extent.symm.trans repair.aligned.symm
    rw [ByteArray.size_append] at lengths
    have tail : layout.tail = ByteArray.empty := ByteArray.size_eq_zero_iff.mp (by omega)
    have visible : image.keeper.active = some layout.target.trimmed := by
      change image.keeper.active = some layout.keeper.bytes
      rw [show image.keeper = before.image.keeper from keeper]
      simpa only [tail, ByteArray.append_empty] using layout.visible
    rw [ite_eq_left effective]
    exact pruned.aligned gone visible
  · rw [ite_eq_right effective]
    exact pruned

/-- A keeper error after the completed suffix pass extends the same
admitted bounded retry. Local unlock determines which error and owner
are returned, using the reached file state for either effect timing. -/
theorem continuesAfterError {input : FilePath} {source : LockedFileState FileImage} {admits : Target → Prop}
    (repair : ListedPrunedAlignedKeeper prune) (metadata : HeldMarkedMetadata held)
    {cause : IO.Error} {nativeReached : LockedFileState FileImage}
    (failed : authorization.fsync (authorization.keeper.inventory, authorization.keeper.slot, 0)
      (acquired operations) = .error cause nativeReached)
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
    let path := directory.file (.walSegment layout.keeper.first)
    let groupedError := IO.userError s!"sync failed for '{path}': {cause}"
    let image := settledSuffix (before := before)
    let reached := if repair.effective then image.syncKeeper else image
    let cleanup := (operations.cachedAttempt localUnlock).cleanupError groupedError reached
    operations.runWithAdmission admission = .error cleanup.1 cleanup.2 ∧
    BoundedReopenTrace directory admits source cleanup.2 ∧ cleanup.2.image = reached ∧
    match operations.unlock with
    | .success => cleanup.1 = groupedError ∧ cleanup.2.owners (directory.file .lock) = none
    | .failure unlockError _ =>
      cleanup.1 = unlockError ∧ cleanup.2.owners (directory.file .lock) = some operations.slot.description := by
  have later : ∀ first ∈ before.image.later.visible, layout.range.through < first := laterValid _ List.mem_cons_self
  exact metadata.continuesAfterRepairError admission localUnlock keeperValid laterValid following accepted ordered
    (repair.finishError later failed) (repair.effects later) prior admitted

end Alvoki.Storage.DiskSession.ListedPrunedAlignedKeeper
