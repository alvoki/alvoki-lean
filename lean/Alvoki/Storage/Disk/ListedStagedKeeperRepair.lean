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

open WAL.Boundary (WalInodeImage CheckpointRepresentsPrefix)

variable {prune : ListedLongKeeperPrune authorization}
  {stage : ListedLongKeeperStage prune}

inductive KeeperRenameOutcome where
  | completed
  | errorBeforeEffect (cause : IO.Error)
  | errorAfterEffect (cause : IO.Error)

def KeeperRenameOutcome.effective : KeeperRenameOutcome → Bool
  | .completed | .errorAfterEffect _ => true
  | .errorBeforeEffect _ => false

private def afterKeeperRename (files : Files) (bytes : ByteArray) : Files :=
  { files with image.keeper := ⟨some bytes, some bytes :: files.image.keeper.crashImages, none⟩ }

private def settleKeeperBinding (files : Files) : Files :=
  { files with image := files.image.syncDirectory.syncKeeper }

/-- The reached rename starts with the exact synced staging result. Its
source and destination resolve to the staged inode and the original keeper
in the retained writer's directory. The observation records whether the
rename changed the binding, including when it returned an error. -/
structure ListedLongKeeperRename (stage : ListedLongKeeperStage prune) where
  synced :
    let atPrune := authorized (acquired before directory operations.slot)
    authorization.fsync (stage.inventory, stage.slot, stage.offset) (scratch atPrune layout.keeper.bytes false) =
      .ok () (scratch atPrune layout.keeper.bytes true)
  original : WalInodeImage
  projectsOriginal : before.image.withKeeperInodes original = before.image
  originalKeeper : original.active = authorization.keeper.object
  freshBinding : stage.inventory.inode stage.slot.description ∉ original.crashBindings
  afterStageSync : List LockReferenceDrop
  lockRetained : operations.slot ∈ (stage.inventory.afterDrops (stage.beforeSync ++ afterStageSync)).slots
  bindings : FilePath → Option Nat
  directoryBound : bindings directory.path = some (operations.descriptors.inode held.lifetime.directorySlot.description)
  sourceBound : bindings (directory.file .stagedWal) = some (stage.inventory.inode stage.slot.description)
  keeperBound : bindings (directory.file (.walSegment layout.keeper.first)) = some original.active
  lockBound : bindings (directory.file .lock) = some (operations.descriptors.inode operations.slot.description)
  outcome : KeeperRenameOutcome
  reported :
    let atPrune := authorized (acquired before directory operations.slot)
    let durable := scratch atPrune layout.keeper.bytes true
    let renamed := afterKeeperRename durable layout.keeper.bytes
    operations.renameFile (directory.file .stagedWal) (directory.file (.walSegment layout.keeper.first)) durable.image =
      match outcome with
      | .completed => .ok () renamed.image
      | .errorBeforeEffect cause => .error cause durable.image
      | .errorAfterEffect cause => .error cause renamed.image
  renamedBindings : FilePath → Option Nat
  renamedSource : outcome.effective = true → renamedBindings (directory.file .stagedWal) = none
  renamedKeeper : outcome.effective = true →
    renamedBindings (directory.file (.walSegment layout.keeper.first)) = some (stage.inventory.inode stage.slot.description)

namespace ListedLongKeeperRename

/-- The reported rename uses the same directory and the two distinct
objects already observed at the staged-file sync. -/
theorem renameTargets (rename : ListedLongKeeperRename stage) :
    rename.bindings directory.path = authorization.bindings directory.path ∧
    rename.bindings (directory.file .stagedWal) = stage.bindings (directory.file .stagedWal) ∧
    rename.bindings (directory.file (.walSegment layout.keeper.first)) =
      stage.bindings (directory.file (.walSegment layout.keeper.first)) ∧
    rename.bindings (directory.file .stagedWal) ≠ rename.bindings (directory.file (.walSegment layout.keeper.first)) := by
  refine ⟨?_, rename.sourceBound.trans stage.stageBound.symm, ?_, ?_⟩
  · rw [rename.directoryBound, authorization.bound, held.lifetime.identifiesDirectory]
  · rw [rename.keeperBound, rename.originalKeeper, stage.keeperBound]
  · rw [rename.sourceBound, rename.keeperBound, rename.originalKeeper]
    exact fun same => stage.distinctKeeper (Option.some.inj same)

/-- An effective rename publishes the original staged inode and consumes
the staging name. The pathname model's old crash choices come from the same
observed original inode projection. -/
theorem publishesInode (rename : ListedLongKeeperRename stage) (effective : rename.outcome.effective = true) :
    let durable := scratch (authorized (acquired before directory operations.slot)) layout.keeper.bytes true
    let reached := afterKeeperRename durable layout.keeper.bytes
    let replacement := stage.inventory.inode stage.slot.description
    rename.renamedBindings (directory.file .stagedWal) = none ∧
    rename.renamedBindings (directory.file (.walSegment layout.keeper.first)) = some replacement ∧
    reached.image = (durable.image.withScratch none).withKeeperInodes
      (rename.original.renameSynced replacement layout.keeper.bytes) := by
  intro durable reached replacement
  refine ⟨rename.renamedSource effective, rename.renamedKeeper effective, ?_⟩
  have projection := rename.original.project_renameSynced durable.image.directory replacement
    layout.keeper.bytes rename.freshBinding
  have choices := congrArg (Option.map fun image : WAL.Boundary.ReopenImage => image.wal.crashImages) projection
  have beforeChoices : (rename.original.project before.image.directory).wal.crashImages =
      before.image.keeper.crashImages :=
    congrArg (fun files : FileImage => files.keeper.crashImages) rename.projectsOriginal
  change some (some layout.keeper.bytes :: (rename.original.project before.image.directory).wal.crashImages) =
    some (((rename.original.renameSynced replacement layout.keeper.bytes).project durable.image.directory).wal.crashImages)
    at choices
  rw [beforeChoices] at choices
  have survives := Option.some.inj choices
  simp only [reached, afterKeeperRename, FileImage.withKeeperInodes, FileImage.withScratch,
    WalInodeImage.project, WalInodeImage.renameSynced, ite_true]
  exact congrArg (fun bytes => { durable.image with keeper := ⟨some layout.keeper.bytes, bytes, none⟩ }) survives

/-- Both the original lock and the inode identity of that lock survive
to the rename observation. -/
theorem lockAtRename (rename : ListedLongKeeperRename stage) :
    let drops := stage.beforeSync ++ rename.afterStageSync
    rename.bindings (directory.file .lock) = some (stage.inventory.inode operations.slot.description) ∧
    ∃ refs : HeldLockReferences operations.slot.description,
      refs.live = stage.inventory.references operations.slot.description ∧
      (refs.afterFileDrops drops directory (acquired before directory operations.slot)).owners.Owns
        directory operations.slot.description := by
  intro drops
  have issuing : operations.slot.reference ∈ (stage.inventory.afterDrops drops).references operations.slot.description :=
    (stage.inventory.afterDrops drops).mem_references.mpr ⟨_, rename.lockRetained, rfl, rfl⟩
  let refs := stage.inventory.held operations.slot.description (DescriptorInventory.wasLive issuing)
  have remains : refs.remaining drops ≠ [] := by
    rw [stage.inventory.held_remaining]
    exact List.ne_nil_of_mem issuing
  refine ⟨?_, refs, rfl, ?_⟩
  · rw [rename.lockBound, stage.captured]
    rfl
  · rw [refs.afterFileDrops_surviving remains]
    simp [acquired, LockOwners.Owns, LockOwners.set]

/-- A successful staged-file sync starts the exact rename and final sync
tail of the bounded worker. -/
theorem reachesRename (rename : ListedLongKeeperRename stage) :
    let durable := scratch (authorized (acquired before directory operations.slot)) layout.keeper.bytes true
    finishBoundedMarkedOpen directory layout.boundedPlan authorization.keeper.metadata.byteSize.toNat
      operations.removeFile (operations.write operations.cache) (operations.sync operations.cache)
      operations.renameFile before.image =
    (do
      operations.renameFile (directory.file .stagedWal) (directory.file (.walSegment layout.keeper.first))
      operations.sync operations.cache #[directory.path]
      pure () : EStateM IO.Error FileImage Unit) durable.image := by
  intro durable
  have staged := stage.stageCallbacks.2
  rw [rename.synced] at staged
  simpa only [show before.image.syncDirectory.withScratch (some (layout.keeper.bytes, false)) =
    (scratch (authorized (acquired before directory operations.slot)) layout.keeper.bytes false).image from rfl,
    staged] using stage.finishFromStage

/-- An unsuccessful rename returns the exact reached image and skips any
final directory sync. -/
theorem finishAfterError (rename : ListedLongKeeperRename stage) (failed : rename.outcome ≠ .completed) :
    let durable := scratch (authorized (acquired before directory operations.slot)) layout.keeper.bytes true
    let renamed := afterKeeperRename durable layout.keeper.bytes
    finishBoundedMarkedOpen directory layout.boundedPlan authorization.keeper.metadata.byteSize.toNat
      operations.removeFile (operations.write operations.cache) (operations.sync operations.cache)
      operations.renameFile before.image =
    match rename.outcome with
    | .completed => .ok () renamed.image
    | .errorBeforeEffect cause => .error cause durable.image
    | .errorAfterEffect cause => .error cause renamed.image := by
  intro durable renamed
  rw [rename.reachesRename]
  simp only [Bind.bind, EStateM.bind]
  have reported := rename.reported
  change operations.renameFile (directory.file .stagedWal) (directory.file (.walSegment layout.keeper.first))
    durable.image = _ at reported
  rw [reported]
  cases returned : rename.outcome with
  | completed => exact False.elim (failed returned)
  | errorBeforeEffect cause => rfl
  | errorAfterEffect cause => rfl

end ListedLongKeeperRename

/-- The final directory sync keeps using the directory handle captured by
the held open. Both it and the lock survive the same descriptor history
through staging and rename. The observed grouped callback settles the
replacement binding only when the syscall takes effect. -/
structure ListedLongKeeperSettlement (rename : ListedLongKeeperRename stage) where
  completed : rename.outcome = .completed
  afterRename : List LockReferenceDrop
  directoryRetained : held.lifetime.directorySlot ∈
    (stage.inventory.afterDrops (stage.beforeSync ++ rename.afterStageSync ++ afterRename)).slots
  lockRetained : operations.slot ∈
    (stage.inventory.afterDrops (stage.beforeSync ++ rename.afterStageSync ++ afterRename)).slots
  bindings : FilePath → Option Nat
  directoryBound : bindings directory.path = some (operations.descriptors.inode held.lifetime.directorySlot.description)
  lockBound : bindings (directory.file .lock) = some (operations.descriptors.inode operations.slot.description)
  keeperBound : bindings (directory.file (.walSegment layout.keeper.first)) =
    rename.renamedBindings (directory.file (.walSegment layout.keeper.first))
  stageAbsent : bindings (directory.file .stagedWal) = rename.renamedBindings (directory.file .stagedWal)
  outcome : DelayedDirectorySyncOutcome
  effect :
    let durable := scratch (authorized (acquired before directory operations.slot)) layout.keeper.bytes true
    let renamed := afterKeeperRename durable layout.keeper.bytes
    authorization.fsync (operations.descriptors, held.lifetime.directorySlot, 0) renamed =
      match outcome with
      | .completed => .ok () (settleKeeperBinding renamed)
      | .errorBeforeEffect cause => .error cause renamed
      | .errorAfterEffect cause => .error cause (settleKeeperBinding renamed)
  projected :
    let durable := scratch (authorized (acquired before directory operations.slot)) layout.keeper.bytes true
    let renamed := afterKeeperRename durable layout.keeper.bytes
    operations.renameFile (directory.file .stagedWal) (directory.file (.walSegment layout.keeper.first)) durable.image =
      .ok () renamed.image →
    operations.sync operations.cache #[directory.path] renamed.image =
      projectDirectorySync (grouped authorization #[directory.path]
        (operations.cache.consume (directory.file .stagedWal), renamed))

namespace ListedLongKeeperSettlement

variable {rename : ListedLongKeeperRename stage}

/-- Both original issuing slots survive the final barrier, and its
effect-time keeper binding is the exact inode published by rename. -/
theorem settlementCustody (reported : ListedLongKeeperSettlement rename) :
    let atSync := stage.inventory.afterDrops (stage.beforeSync ++ rename.afterStageSync ++ reported.afterRename)
    held.lifetime.directorySlot ∈ atSync.slots ∧ operations.slot ∈ atSync.slots ∧
    reported.bindings directory.path = some (atSync.inode held.lifetime.directorySlot.description) ∧
    reported.bindings (directory.file .lock) = some (atSync.inode operations.slot.description) ∧
    reported.bindings (directory.file .stagedWal) = none ∧
    reported.bindings (directory.file (.walSegment layout.keeper.first)) = some (stage.inventory.inode stage.slot.description) := by
  intro atSync
  have effective : rename.outcome.effective = true := by rw [reported.completed]; rfl
  refine ⟨reported.directoryRetained, reported.lockRetained, ?_, ?_,
    reported.stageAbsent.trans (rename.renamedSource effective),
    reported.keeperBound.trans (rename.renamedKeeper effective)⟩
  · simp only [atSync, DescriptorInventory.afterDrops, stage.captured, DescriptorInventory.insert,
      held.listing.afterClose_eq]
    exact reported.directoryBound
  · simp only [atSync, DescriptorInventory.afterDrops, stage.captured, DescriptorInventory.insert,
      held.listing.afterClose_eq]
    exact reported.lockBound

/-- When the final sync takes effect, its reached image has exactly the
crash bytes of the replacement inode now bound to the keeper path. -/
theorem settledInode (reported : ListedLongKeeperSettlement rename) :
    let durable := scratch (authorized (acquired before directory operations.slot)) layout.keeper.bytes true
    let settled := settleKeeperBinding (afterKeeperRename durable layout.keeper.bytes)
    let replacement := stage.inventory.inode stage.slot.description
    reported.bindings (directory.file (.walSegment layout.keeper.first)) = some replacement ∧
    settled.image.withKeeperInodes (rename.original.renameSynced replacement layout.keeper.bytes).settleBinding =
      settled.image := by
  intro durable settled replacement
  refine ⟨reported.settlementCustody.2.2.2.2.2, ?_⟩
  simp [settled, settleKeeperBinding, afterKeeperRename, FileImage.syncDirectory, FileImage.syncKeeper,
    FileImage.withKeeperInodes, WalInodeImage.project, WalInodeImage.settleBinding, WalInodeImage.renameSynced]

/-- The cache still routes the final sync to the captured directory after
the staging cache entry was consumed. Only an effective final barrier
settles the already-synced replacement. -/
theorem syncResult (reported : ListedLongKeeperSettlement rename) :
    let durable := scratch (authorized (acquired before directory operations.slot)) layout.keeper.bytes true
    let renamed := afterKeeperRename durable layout.keeper.bytes
    operations.sync operations.cache #[directory.path] renamed.image =
      match reported.outcome with
      | .completed => .ok () (settleKeeperBinding renamed).image
      | .errorBeforeEffect cause => .error (IO.userError s!"sync failed for '{directory.path}': {cause}") renamed.image
      | .errorAfterEffect cause =>
        .error (IO.userError s!"sync failed for '{directory.path}': {cause}") (settleKeeperBinding renamed).image := by
  intro durable renamed
  have routed : operations.renameFile (directory.file .stagedWal) (directory.file (.walSegment layout.keeper.first))
      durable.image = .ok () renamed.image := by
    simpa only [reported.completed] using rename.reported
  rw [reported.projected routed, grouped, SyncPathGroup.run_single]
  let cache := operations.cache.consume (directory.file .stagedWal)
  have finalRoute : sync directory.path authorization.openRead authorization.fsync directory.path (cache, renamed) =
      withCache cache (authorization.fsync (operations.descriptors, held.lifetime.directorySlot, 0) renamed) := by
    simp [sync, Cache.resolve, cache, Cache.consume, held.capturedDirectory]
  rw [finalRoute]
  have settledEffect := reported.effect
  change authorization.fsync (operations.descriptors, held.lifetime.directorySlot, 0) renamed = _ at settledEffect
  rw [settledEffect]
  cases reported.outcome <;> rfl

/-- After the reported successful rename, the actual bounded finisher
returns the exact final grouped directory outcome. -/
theorem finishResult (reported : ListedLongKeeperSettlement rename) :
    let durable := scratch (authorized (acquired before directory operations.slot)) layout.keeper.bytes true
    let renamed := afterKeeperRename durable layout.keeper.bytes
    finishBoundedMarkedOpen directory layout.boundedPlan authorization.keeper.metadata.byteSize.toNat
      operations.removeFile (operations.write operations.cache) (operations.sync operations.cache)
      operations.renameFile before.image = operations.sync operations.cache #[directory.path] renamed.image := by
  intro durable renamed
  rw [rename.reachesRename]
  have routed : operations.renameFile (directory.file .stagedWal) (directory.file (.walSegment layout.keeper.first))
      durable.image = .ok () renamed.image := by simpa only [reported.completed] using rename.reported
  simp only [Bind.bind, EStateM.bind]
  rw [routed]
  change (operations.sync operations.cache #[directory.path] >>= fun _ => pure ()) renamed.image = _
  simp only [Bind.bind, EStateM.bind]
  cases operations.sync operations.cache #[directory.path] renamed.image with
  | ok value reached => cases value; rfl
  | error cause reached => rfl

private theorem prependHealthy {target : Target} {initial next : FileImage} {head : Step} {rest : List Step}
    {perform : Step → EStateM IO.Error FileImage Unit}
    (effect : initial.effect target head = some next) (run : perform head initial = .ok () next)
    (tail : ∀ action prior next', ReachesAction target next rest action prior →
      prior.effect target action = some next' → perform action prior = .ok () next') :
    ∀ action prior next', ReachesAction target initial (head :: rest) action prior →
      prior.effect target action = some next' → perform action prior = .ok () next' := by
  intro action prior next' reached applied
  obtain ⟨earlier, suffix, schedule, executed⟩ := reached
  cases earlier with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at schedule
    obtain ⟨rfl, _⟩ := schedule
    have same : initial = prior := Option.some.inj executed
    subst prior
    rw [effect] at applied
    exact Option.some.inj applied ▸ run
  | cons first earlier =>
    simp only [List.cons_append, List.cons.injEq] at schedule
    obtain ⟨rfl, ordered⟩ := schedule
    simp only [List.foldlM_cons, effect, Bind.bind, Option.bind] at executed
    exact tail action prior next' ⟨earlier, suffix, ordered, executed⟩ applied

/-- Per-operation results supply the whole finishing contract on the
long-keeper route with an empty visible suffix. -/
theorem healthyFinish (reported : ListedLongKeeperSettlement rename)
    (succeeded : reported.outcome = .completed) : operations.HealthyFinish := by
  let pruned := before.image.syncDirectory
  let written := scratch (authorized (acquired before directory operations.slot)) layout.keeper.bytes false
  let durable := scratch (authorized (acquired before directory operations.slot)) layout.keeper.bytes true
  let renamed := afterKeeperRename durable layout.keeper.bytes
  have long : layout.plan.keeperSize < layout.plan.keeperBytes.size := calc
    layout.plan.keeperSize = layout.keeper.bytes.size := layout.target.trimmedSize.symm
    _ < authorization.keeper.metadata.byteSize.toNat := prune.longer
    _ = layout.plan.keeperBytes.size := authorization.keeper.extent
  have declined : layout.plan.alignedWithoutPrune = false := by
    simp [Plan.alignedWithoutPrune, Nat.ne_of_gt long]
  have noLater : layout.plan.newer = [] := prune.noLater
  have schedule : layout.plan.finishActions =
      [.syncPruned, .replace .writeStaged, .replace .syncStaged, .replace .renameStaged, .replace .syncDirectory] := by
    simp [Plan.finishActions, declined, Plan.actions, steps, noLater, long, Publication.steps]
  have selectedSize : layout.keeper.bytes.size = layout.plan.keeperSize := layout.target.trimmedSize
  have selectedBytes : layout.plan.keeperBytes.extract 0 layout.plan.keeperSize = layout.keeper.bytes := by
    rw [← selectedSize]
    exact ByteArray.extract_append_eq_left rfl
  have prunedResult := prune.barriers.2.2
  have staged := stage.stageCallbacks.2
  rw [rename.synced] at staged
  have renameResult := rename.reported
  dsimp only at renameResult
  rw [reported.completed] at renameResult
  have final := reported.syncResult
  dsimp only at final
  rw [succeeded] at final
  unfold MarkedRetryChunkOperations.HealthyFinish
  rw [schedule]
  refine prependHealthy (next := pruned) rfl prunedResult ?_
  refine prependHealthy (next := written.image) rfl ?_ ?_
  · simp only [performPaths, Publication.performReplacement, selectedBytes]
    exact stage.stageCallbacks.1
  refine prependHealthy (next := durable.image) rfl ?_ ?_
  · simp only [performPaths, Publication.performReplacement, Array.push_empty]
    exact staged
  refine prependHealthy (next := renamed.image) rfl renameResult ?_
  refine prependHealthy (next := (settleKeeperBinding renamed).image) rfl final ?_
  intro action prior next reached _
  obtain ⟨earlier, later, ordered, _⟩ := reached
  have size := congrArg List.length ordered
  simp at size

/-- Successful reports of the reached replacement callbacks install the
exact selected checkpoint and marked WAL under the acquired descriptor. -/
theorem installs {input : FilePath} (reported : ListedLongKeeperSettlement rename)
    (succeeded : reported.outcome = .completed) (metadata : HeldMarkedMetadata held)
    (admission : OpenAdmissionReports input directory operations.slot)
    (keeperValid : before.image.keeper.Valid layout.target.Accepts)
    (laterValid : before.image.later.Beyond layout.range.through)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      before.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history) :
    CachedRetryInstalled (before := before) operations.reported operations.descriptors operations.slot operations.bindings
      published operations.liveRefs (operations.runWithAdmission admission) :=
  authorization.installs metadata prune.completed (reported.healthyFinish succeeded) admission keeperValid laterValid
    following accepted ordered

end ListedLongKeeperSettlement
end Alvoki.Storage.DiskSession
