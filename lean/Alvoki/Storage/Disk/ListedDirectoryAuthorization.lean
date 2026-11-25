import Alvoki.Storage.Disk.HeldDirectoryReadObservations

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

variable {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout before.image history}
  {operations : MarkedRetryChunkOperations (Cache (DescriptorInventory × DescriptorSlot × Nat)) directory layout}
  {published : CheckpointPublication.Image}

private def HeldDirectoryMarkedRetryReports.heldState (_ : HeldDirectoryMarkedRetryReports operations published) :
    LockedFileState FileImage :=
  ⟨before.image, before.owners.set (directory.file .lock) (some operations.slot.description)⟩

def projectDirectorySync {files : Type} :
    EStateM.Result IO.Error (files × LockedFileState FileImage) Unit → EStateM.Result IO.Error FileImage Unit
  | .ok () (_, after) => .ok () after.image
  | .error cause (_, after) => .error cause after.image

/-- Reports for the first directory barrier after a successful selected
keeper read. The sync callback used by the file-image installer must
project the real grouped sync from the cache reached by that read. The
projection supplies the refinement boundary for the opaque native refs.
The complete drop report still excludes an independent explicit unlock. -/
structure ListedDirectoryAuthorization (report : HeldDirectoryMarkedRetryReports operations published) where
  keeper : operations.reads.ObservesFile (directory.file (.walSegment layout.keeper.first))
    (layout.keeper.bytes ++ layout.tail)
  fits : layout.keeper.bytes.size < USize.size
  afterListing : List LockReferenceDrop
  directoryRetained : report.lifetime.directorySlot ∈ (report.listing.afterClose.afterDrops afterListing).slots
  lockRetained : operations.slot ∈ (report.listing.afterClose.afterDrops afterListing).slots
  bindings : FilePath → Option Nat
  bound : bindings directory.path = some (report.lifetime.namespaceView.modelObject report.lifetime.root)
  lockBound : bindings (directory.file .lock) = some (operations.descriptors.inode operations.slot.description)
  outcome : DelayedDirectorySyncOutcome
  openRead : FilePath → EStateM IO.Error (LockedFileState FileImage) (DescriptorInventory × DescriptorSlot × Nat)
  fsync : (DescriptorInventory × DescriptorSlot × Nat) → EStateM IO.Error (LockedFileState FileImage) Unit
  effect : fsync (operations.descriptors, report.lifetime.directorySlot, 0) report.heldState =
    (report.directoryBarrier afterListing directoryRetained bindings bound outcome).run report.heldState
  syncProjection : ∀ reached,
    readWalKeeperWithChunks operations.reads (directory.file (.walSegment layout.keeper.first))
      layout.keeper.bytes.size keeper.metadata.byteSize.toNat (operations.cache, report.heldState) =
      .ok layout.keeper.bytes (reached, report.heldState) →
    operations.sync operations.cache #[directory.path] before.image =
      projectDirectorySync (SyncPathGroup.run (sync directory.path openRead fsync) #[directory.path]
        (reached, report.heldState))

namespace ListedDirectoryAuthorization

variable {report : HeldDirectoryMarkedRetryReports operations published}

/-- The keeper metadata fixes the same extent for the pure installer
callback and the cache-bearing native-shaped reader. -/
theorem keeperPayload (observed : ListedDirectoryAuthorization report) :
    operations.readKeeper operations.cache (directory.file (.walSegment layout.keeper.first))
      layout.keeper.bytes.size observed.keeper.metadata.byteSize.toNat = .ok layout.keeper.bytes := by
  have measured : operations.reported.inventory.reports.lstat (directory.file (.walSegment layout.keeper.first)) =
      .ok observed.keeper.metadata := by
    rw [operations.metadata, observed.keeper.stat]
    rfl
  rw [operations.keeperReads]
  exact (operations.reported.keeper _ measured).2

/-- The acquired writer stays the lock owner under the same effect-time
drop history when its observed slot survives. -/
theorem lockAtBarrier (observed : ListedDirectoryAuthorization report) :
    let drops := report.lifetime.drops ++ observed.afterListing
    observed.bindings (directory.file .lock) = some (operations.descriptors.inode operations.slot.description) ∧
    ∃ refs : HeldLockReferences operations.slot.description,
      refs.live = operations.descriptors.references operations.slot.description ∧
      (refs.afterFileDrops drops directory report.heldState).owners.Owns directory operations.slot.description := by
  intro drops
  have issuing : operations.slot.reference ∈ (operations.descriptors.afterDrops drops).references
      operations.slot.description := by
    simp only [drops]
    rw [← DescriptorInventory.afterDrops_append, ← report.listing.afterClose_eq]
    exact (report.listing.afterClose.afterDrops observed.afterListing).mem_references.mpr
      ⟨_, observed.lockRetained, rfl, rfl⟩
  let refs := operations.descriptors.held operations.slot.description (DescriptorInventory.wasLive issuing)
  have stillLive : refs.remaining drops ≠ [] := by
    rw [operations.descriptors.held_remaining]
    exact List.ne_nil_of_mem issuing
  refine ⟨observed.lockBound, refs, rfl, ?_⟩
  rw [refs.afterFileDrops_surviving stillLive]
  simp [HeldDirectoryMarkedRetryReports.heldState, LockOwners.Owns, LockOwners.set]

/-- The single-path group preserves both kinds of sync failure, adding
the pathname to the returned error and keeping the reached file image. -/
theorem syncResult (observed : ListedDirectoryAuthorization report) :
    operations.sync operations.cache #[directory.path] before.image =
      match observed.outcome with
      | .completed => .ok () before.image.syncDirectory
      | .errorBeforeEffect cause => .error (IO.userError s!"sync failed for '{directory.path}': {cause}") before.image
      | .errorAfterEffect cause =>
        .error (IO.userError s!"sync failed for '{directory.path}': {cause}") before.image.syncDirectory := by
  obtain ⟨keeperRead, routed⟩ := report.keeperRead_syncListedDirectory observed.keeper observed.fits
    observed.afterListing observed.directoryRetained observed.bindings observed.bound observed.outcome report.heldState
    observed.openRead observed.fsync observed.effect
  rw [observed.syncProjection _ keeperRead, SyncPathGroup.run_single, routed]
  cases observed.outcome <;>
    simp only [HeldDirectoryMarkedRetryReports.directoryBarrier, DescriptorInventory.delayedDirectorySync,
      DelayedDirectorySync.run, withCache, projectDirectorySync, HeldDirectoryMarkedRetryReports.heldState] <;> rfl

theorem settles (observed : ListedDirectoryAuthorization report) (completed : observed.outcome = .completed) :
    operations.sync operations.cache #[directory.path] before.image = .ok () before.image.syncDirectory := by
  rw [observed.syncResult, completed]

/-- Feed the projected first grouped barrier into the exact admitted
installer. No independent successful-settlement report is needed. -/
theorem installs {input : FilePath} (observed : ListedDirectoryAuthorization report)
    (completed : observed.outcome = .completed)
    (healthy : operations.HealthyFinish)
    (admission : OpenAdmissionReports input directory operations.slot)
    (keeperValid : before.image.keeper.Valid layout.target.Accepts)
    (laterValid : before.image.later.Beyond layout.range.through)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      before.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history) :
    CachedRetryInstalled (before := before) operations.reported operations.descriptors operations.slot operations.bindings
      published operations.liveRefs ((report.toChunkReports (observed.settles completed) healthy).runWithAdmission admission) :=
  (report.installs (observed.settles completed) healthy admission keeperValid laterValid following accepted ordered).2.2.2.2

end ListedDirectoryAuthorization
end Alvoki.Storage.DiskSession
