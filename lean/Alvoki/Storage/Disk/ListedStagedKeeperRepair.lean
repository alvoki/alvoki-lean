import Alvoki.Storage.Disk.ListedDirectoryAuthorization
import Alvoki.Storage.Disk.LongWalBindingPublication

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

variable {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout before.image history}
  {operations : MarkedRetryChunkOperations (Cache (DescriptorInventory × DescriptorSlot × Nat)) directory layout}
  {published : CheckpointPublication.Image}
  {held : HeldDirectoryMarkedRetryReports operations published}
  {authorization : ListedDirectoryAuthorization held}

private abbrev Handle := DescriptorInventory × DescriptorSlot × Nat
private abbrev Files := LockedFileState FileImage

private def acquired (before : LockedFileState FileImage) (directory : DiskDirectory) (slot : DescriptorSlot) :
    Files :=
  { before with owners := before.owners.set (directory.file .lock) (some slot.description) }

private def authorized (files : Files) : Files := { files with image := files.image.syncDirectory }

private def scratch (files : Files) (bytes : ByteArray) (durable : Bool) : Files :=
  { files with image := files.image.withScratch (some (bytes, durable)) }

private abbrev grouped (authorization : ListedDirectoryAuthorization held) :=
  SyncPathGroup.run (sync directory.path authorization.openRead authorization.fsync)

/-- The long keeper and empty visible suffix still take two directory
barriers. The reported drops extend the listing census through the second
barrier and the same captured directory slot supplies both effects. -/
structure ListedLongKeeperPrune (authorization : ListedDirectoryAuthorization held) where
  completed : authorization.outcome = .completed
  longer : layout.keeper.bytes.size < authorization.keeper.metadata.byteSize.toNat
  noLater : before.image.later.visible = []
  afterAuthorization : List LockReferenceDrop
  directoryRetained : held.lifetime.directorySlot ∈
    (held.listing.afterClose.afterDrops (authorization.afterListing ++ afterAuthorization)).slots
  lockRetained : operations.slot ∈
    (held.listing.afterClose.afterDrops (authorization.afterListing ++ afterAuthorization)).slots
  bindings : FilePath → Option Nat
  directoryBound : bindings directory.path = some (operations.descriptors.inode held.lifetime.directorySlot.description)
  lockBound : bindings (directory.file .lock) = some (operations.descriptors.inode operations.slot.description)
  synced :
    let atPrune := authorized (acquired before directory operations.slot)
    authorization.fsync (operations.descriptors, held.lifetime.directorySlot, 0) atPrune = .ok () atPrune
  projected : ∀ reached,
    let initial := acquired before directory operations.slot
    let atPrune := authorized initial
    grouped authorization #[directory.path] (operations.cache, initial) = .ok () (reached, atPrune) →
    operations.sync operations.cache #[directory.path] atPrune.image =
      projectDirectorySync (grouped authorization #[directory.path] (reached, atPrune))

namespace ListedLongKeeperPrune

/-- Both original slots still refer to the reported canonical bindings
at the second directory barrier. -/
theorem pruneCustody (reported : ListedLongKeeperPrune authorization) :
    let atPrune := held.listing.afterClose.afterDrops (authorization.afterListing ++ reported.afterAuthorization)
    held.lifetime.directorySlot ∈ atPrune.slots ∧ operations.slot ∈ atPrune.slots ∧
    reported.bindings directory.path = some (atPrune.inode held.lifetime.directorySlot.description) ∧
    reported.bindings (directory.file .lock) = some (atPrune.inode operations.slot.description) := by
  intro atPrune
  refine ⟨reported.directoryRetained, reported.lockRetained, ?_, ?_⟩
  · simpa only [atPrune, DescriptorInventory.afterDrops, held.listing.afterClose_eq] using reported.directoryBound
  · simpa only [atPrune, DescriptorInventory.afterDrops, held.listing.afterClose_eq] using reported.lockBound

/-- Reading a long keeper returns the exact prefix without remembering
its open handle. Both reached directory barriers use the retained cache. -/
theorem barriers (reported : ListedLongKeeperPrune authorization) :
    let initial := acquired before directory operations.slot
    let atPrune := authorized initial
    readWalKeeperWithChunks operations.reads (directory.file (.walSegment layout.keeper.first))
      layout.keeper.bytes.size authorization.keeper.metadata.byteSize.toNat (operations.cache, initial) =
        .ok layout.keeper.bytes (operations.cache, initial) ∧
    grouped authorization #[directory.path] (operations.cache, initial) = .ok () (operations.cache, atPrune) ∧
    operations.sync operations.cache #[directory.path] atPrune.image = .ok () atPrune.image := by
  intro initial atPrune
  obtain ⟨read, routed⟩ := held.keeperRead_syncListedDirectory authorization.keeper authorization.fits
    authorization.afterListing authorization.directoryRetained authorization.bindings authorization.bound
    authorization.outcome initial authorization.openRead authorization.fsync authorization.effect
  have unequal : layout.keeper.bytes.size ≠ authorization.keeper.metadata.byteSize.toNat :=
    Nat.ne_of_lt reported.longer
  have routedExact : sync directory.path authorization.openRead authorization.fsync directory.path
      (operations.cache, initial) = .ok () (operations.cache, atPrune) := by
    simpa [Cache.captureKeeper, unequal, HeldDirectoryMarkedRetryReports.directoryBarrier,
      DescriptorInventory.delayedDirectorySync, DelayedDirectorySync.run, reported.completed, withCache,
      atPrune, authorized] using routed
  have first : grouped authorization #[directory.path] (operations.cache, initial) =
      .ok () (operations.cache, atPrune) := by
    rw [grouped, SyncPathGroup.run_single, routedExact]
  refine ⟨by simpa only [Cache.captureKeeper, ite_eq_right unequal] using read, first, ?_⟩
  rw [reported.projected operations.cache first, grouped, SyncPathGroup.run_single]
  simp [sync, Cache.resolve, held.capturedDirectory, reported.synced, withCache, projectDirectorySync]
  rfl

end ListedLongKeeperPrune

/-- The fresh staging schedule writes and flushes the selected prefix.
Its returned descriptor is inserted into the reached census. Native
projections identify both callbacks consumed by the bounded finisher. -/
structure ListedLongKeeperStage (prune : ListedLongKeeperPrune authorization) where
  tryCreate : FilePath → EStateM IO.Error Files (Except IO.Error Handle)
  detachStale : FilePath → EStateM IO.Error Files Unit
  create : FilePath → EStateM IO.Error Files Handle
  write : Handle → ByteArray → EStateM IO.Error Files Unit
  flush : Handle → EStateM IO.Error Files Unit
  inventory : DescriptorInventory
  slot : DescriptorSlot
  offset : Nat
  beforeStage : List LockReferenceDrop
  atWrite : ∀ old ∈ ((held.listing.afterClose.afterDrops
    (authorization.afterListing ++ prune.afterAuthorization)).afterDrops beforeStage).slots,
      old.address ≠ slot.address
  fresh : ((held.listing.afterClose.afterDrops
    (authorization.afterListing ++ prune.afterAuthorization)).afterDrops beforeStage).references slot.description = []
  captured : inventory =
    ((held.listing.afterClose.afterDrops
      (authorization.afterListing ++ prune.afterAuthorization)).afterDrops beforeStage).insert slot atWrite
  wrote :
    let atPrune := authorized (acquired before directory operations.slot)
    writeFreshStagedWith tryCreate detachStale create write flush (directory.file .stagedWal) layout.keeper.bytes atPrune =
      .ok (inventory, slot, offset) (scratch atPrune layout.keeper.bytes false)
  writeProjection :
    let atPrune := authorized (acquired before directory operations.slot)
    operations.write operations.cache (directory.file .stagedWal) layout.keeper.bytes atPrune.image =
      projectDirectorySync (stageFreshWithCache (directory.file .stagedWal) layout.keeper.bytes
        (writeFreshStagedWith tryCreate detachStale create write flush) (operations.cache, atPrune))
  beforeSync : List LockReferenceDrop
  retained : slot ∈ (inventory.afterDrops beforeSync).slots
  lockRetained : operations.slot ∈ (inventory.afterDrops beforeSync).slots
  bindings : FilePath → Option Nat
  stageBound : bindings (directory.file .stagedWal) = some (inventory.inode slot.description)
  keeperBound : bindings (directory.file (.walSegment layout.keeper.first)) = some authorization.keeper.object
  distinctKeeper : inventory.inode slot.description ≠ authorization.keeper.object
  lockBound : bindings (directory.file .lock) = some (inventory.inode operations.slot.description)
  effective : Bool
  outcome :
    let atPrune := authorized (acquired before directory operations.slot)
    let written := scratch atPrune layout.keeper.bytes false
    FsyncResult written (scratch atPrune layout.keeper.bytes true) effective
      (authorization.fsync (inventory, slot, offset) written)
  syncProjection : ∀ reached,
    let atPrune := authorized (acquired before directory operations.slot)
    let written := scratch atPrune layout.keeper.bytes false
    let path := directory.file .stagedWal
    stageFreshWithCache path layout.keeper.bytes (writeFreshStagedWith tryCreate detachStale create write flush)
      (operations.cache, atPrune) = .ok () (reached, written) →
    operations.sync operations.cache #[path] written.image =
      projectDirectorySync (grouped authorization #[path] (reached, written))

namespace ListedLongKeeperStage

variable {prune : ListedLongKeeperPrune authorization}

private theorem stagePath_ne_directory (directory : DiskDirectory) :
    directory.file .stagedWal ≠ directory.path := by
  intro same
  have lengths := congrArg (fun path : FilePath => path.toString.length) same
  change (directory.path.toString ++ "/" ++ "WAL.next").length = directory.path.toString.length at lengths
  simp only [String.length_append] at lengths
  have slash : "/".length = 1 := by decide
  rw [slash] at lengths
  omega

/-- The stage callback writes the selected bytes and remembers the exact
new descriptor. The grouped barrier consumes that entry even on error. -/
theorem stageCallbacks (reported : ListedLongKeeperStage prune) :
    let atPrune := authorized (acquired before directory operations.slot)
    let written := scratch atPrune layout.keeper.bytes false
    let durable := scratch atPrune layout.keeper.bytes true
    let path := directory.file .stagedWal
    operations.write operations.cache path layout.keeper.bytes atPrune.image = .ok () written.image ∧
    operations.sync operations.cache #[path] written.image =
      match authorization.fsync (reported.inventory, reported.slot, reported.offset) written with
      | .ok () _ => .ok () durable.image
      | .error cause _ => .error (IO.userError s!"sync failed for '{path}': {cause}")
          (if reported.effective then durable.image else written.image) := by
  intro atPrune written durable path
  let handle : Handle := (reported.inventory, reported.slot, reported.offset)
  have wrote :
      stageFreshWithCache path layout.keeper.bytes
        (writeFreshStagedWith reported.tryCreate reported.detachStale reported.create reported.write reported.flush)
        (operations.cache, atPrune) = .ok () (operations.cache.remember path handle, written) := by
    simp only [stageFreshWithCache, path, reported.wrote, handle, written, atPrune]
  refine ⟨by rw [reported.writeProjection, wrote]; rfl, ?_⟩
  rw [reported.syncProjection _ wrote, grouped, SyncPathGroup.run_single]
  rw [syncRemembered (stagePath_ne_directory directory) handle authorization.openRead authorization.fsync written]
  have outcome := reported.outcome
  change FsyncResult written durable reported.effective (authorization.fsync handle written) at outcome
  change _ = match authorization.fsync handle written with
    | .ok () _ => EStateM.Result.ok () durable.image
    | .error cause _ => EStateM.Result.error (IO.userError s!"sync failed for '{path}': {cause}")
        (if reported.effective then durable.image else written.image)
  generalize authorization.fsync handle written = returned at outcome ⊢
  generalize reported.effective = effective at outcome ⊢
  cases outcome <;> rfl

/-- The staged-file barrier uses a live description of the distinct
scratch inode. The same observed census also retains the lock issuer. -/
theorem stageCustody (reported : ListedLongKeeperStage prune) :
    let written := scratch (authorized (acquired before directory operations.slot)) layout.keeper.bytes false
    let handle : Handle := (reported.inventory, reported.slot, reported.offset)
    reported.bindings (directory.file .lock) = some (operations.descriptors.inode operations.slot.description) ∧
    (∃ refs : HeldLockReferences operations.slot.description,
      refs.live = reported.inventory.references operations.slot.description ∧
      (refs.afterFileDrops reported.beforeSync directory written).owners.Owns directory operations.slot.description) ∧
    ∃ observed : FsyncObservation (fun handle => handle.2.1.description)
        (fun handle => handle.1.inode handle.2.1.description) handle written
        (fun _ _ => scratch (authorized (acquired before directory operations.slot)) layout.keeper.bytes true)
        (authorization.fsync handle written),
      observed.issuer = reported.slot.reference ∧ observed.effective = reported.effective ∧
      reported.bindings (directory.file .stagedWal) = some observed.effectInode ∧
      reported.bindings (directory.file (.walSegment layout.keeper.first)) = some authorization.keeper.object ∧
      observed.effectInode ≠ authorization.keeper.object := by
  intro written handle
  have stagingLive : reported.slot.reference ∈
      (reported.inventory.afterDrops reported.beforeSync).references reported.slot.description :=
    (reported.inventory.afterDrops reported.beforeSync).mem_references.mpr ⟨_, reported.retained, rfl, rfl⟩
  have lockLive : operations.slot.reference ∈
      (reported.inventory.afterDrops reported.beforeSync).references operations.slot.description :=
    (reported.inventory.afterDrops reported.beforeSync).mem_references.mpr ⟨_, reported.lockRetained, rfl, rfl⟩
  let refs := reported.inventory.held operations.slot.description (DescriptorInventory.wasLive lockLive)
  have remains : refs.remaining reported.beforeSync ≠ [] := by
    rw [reported.inventory.held_remaining]
    exact List.ne_nil_of_mem lockLive
  let barrier := FsyncObservation.ofInventory reported.inventory reported.beforeSync
    (fun handle : Handle => handle.2.1.description) (fun handle => handle.1.inode handle.2.1.description)
    handle reported.slot.reference stagingLive rfl written
    (fun _ _ => scratch (authorized (acquired before directory operations.slot)) layout.keeper.bytes true)
    reported.outcome
  refine ⟨?_, ⟨refs, rfl, ?_⟩, barrier, rfl, rfl, reported.stageBound, reported.keeperBound, reported.distinctKeeper⟩
  · rw [reported.lockBound, reported.captured]
    rfl
  · rw [refs.afterFileDrops_surviving remains]
    simp [written, scratch, authorized, acquired, LockOwners.Owns, LockOwners.set]

/-- The bounded worker reaches the exact staged-file barrier after both
directory barriers and the fresh write. A reported staged-sync error is
returned directly. Rename and the final directory barrier run only after
successful staged sync. -/
theorem finishFromStage (reported : ListedLongKeeperStage prune) :
    let written := before.image.syncDirectory.withScratch (some (layout.keeper.bytes, false))
    let path := directory.file .stagedWal
    let keeper := directory.file (.walSegment layout.keeper.first)
    finishBoundedMarkedOpen directory layout.boundedPlan authorization.keeper.metadata.byteSize.toNat
      operations.removeFile (operations.write operations.cache) (operations.sync operations.cache)
      operations.renameFile before.image =
    match operations.sync operations.cache #[path] written with
    | .error cause reached => EStateM.Result.error cause reached
    | .ok () reached => (do
        operations.renameFile path keeper
        operations.sync operations.cache #[directory.path]
        pure () : EStateM IO.Error FileImage Unit) reached := by
  intro written path keeper
  have newer : layout.boundedPlan.newer = [] := prune.noLater
  have size : layout.boundedPlan.keeperBytes.size = layout.boundedPlan.keeperSize := layout.target.trimmedSize
  have long : layout.boundedPlan.keeperSize < authorization.keeper.metadata.byteSize.toNat :=
    size ▸ prune.longer
  have valid : layout.boundedPlan.valid = true :=
    (Plan.valid_iff layout.boundedPlan).mpr ⟨layout.target.firstCovered, Nat.le_of_eq size.symm, by simp [newer]⟩
  have bytes : layout.boundedPlan.keeperBytes.extract 0 layout.boundedPlan.keeperSize = layout.keeper.bytes := by
    rw [← size, ByteArray.extract_zero_size]
    rfl
  obtain ⟨_, _, pruned⟩ := prune.barriers
  change operations.sync operations.cache #[directory.path] before.image.syncDirectory =
    .ok () before.image.syncDirectory at pruned
  obtain ⟨wrote, _⟩ := reported.stageCallbacks
  change operations.write operations.cache (directory.file .stagedWal) layout.keeper.bytes before.image.syncDirectory =
    .ok () written at wrote
  rw [show finishBoundedMarkedOpen directory layout.boundedPlan authorization.keeper.metadata.byteSize.toNat
      operations.removeFile (operations.write operations.cache) (operations.sync operations.cache)
      operations.renameFile before.image = _ from
    congrFun (finishBoundedMarkedOpen_long directory layout.boundedPlan authorization.keeper.metadata.byteSize.toNat
      operations.removeFile (operations.write operations.cache) (operations.sync operations.cache)
      operations.renameFile valid size long) before.image]
  simp only [newer, List.map_nil, List.nil_append, List.forM_eq_forM, List.forM_cons, List.forM_nil,
    performPaths, Publication.performReplacement, Array.push_empty, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
    authorization.settles prune.completed, pruned, bytes, wrote]
  dsimp only [path, keeper]
  cases operations.sync operations.cache #[directory.file .stagedWal] written with
  | ok value => cases value; rfl
  | error => rfl

end ListedLongKeeperStage
end Alvoki.Storage.DiskSession
