import Alvoki.Storage.Disk.ListedDirectoryAuthorization
import Alvoki.Storage.Disk.HeldLaterWalPrune

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

variable {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout before.image history}
  {operations : MarkedRetryChunkOperations (Cache (DescriptorInventory × DescriptorSlot × Nat)) directory layout}
  {published : CheckpointPublication.Image} {readStart : DescriptorInventory}
  {held : HeldDirectoryMarkedRetryReports operations published readStart}
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
  · simpa only [atPrune, DescriptorInventory.afterDrops, held.listing.afterClose_eq, held.objectMap] using reported.directoryBound
  · simpa only [atPrune, DescriptorInventory.afterDrops, held.listing.afterClose_eq, held.objectMap] using reported.lockBound

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

/-- Which reported prune prefix reached the staging callbacks. Existing
empty-suffix reports retain the same starting image. Nonempty reports
carry the exact reached image after all approved unlinks. -/
inductive LongKeeperPruning (authorization : ListedDirectoryAuthorization held) where
  | empty (reported : ListedLongKeeperPrune authorization)
  | listed (reported : ListedLaterWalPrune authorization)
      (longer : layout.keeper.bytes.size < authorization.keeper.metadata.byteSize.toNat)
      (later : ∀ first ∈ before.image.later.visible, layout.range.through < first)

namespace LongKeeperPruning

def afterAuthorization : LongKeeperPruning authorization → List LockReferenceDrop
  | .empty reported => reported.afterAuthorization
  | .listed reported _ _ => reported.afterAuthorization

def afterUnlinks : LongKeeperPruning authorization → FileImage
  | .empty _ => before.image.syncDirectory
  | .listed _ _ _ => before.image.unlinkVisibleSuffix

def stageInput (pruning : LongKeeperPruning authorization) : Files :=
  { acquired before directory operations.slot with image := pruning.afterUnlinks.syncDirectory }

theorem completed (pruning : LongKeeperPruning authorization) : authorization.outcome = .completed :=
  match pruning with
  | .empty reported => reported.completed
  | .listed reported _ _ => reported.authorized

theorem longer (pruning : LongKeeperPruning authorization) :
    layout.keeper.bytes.size < authorization.keeper.metadata.byteSize.toNat :=
  match pruning with
  | .empty reported => reported.longer
  | .listed _ longer _ => longer

theorem later (pruning : LongKeeperPruning authorization) :
    ∀ first ∈ before.image.later.visible, layout.range.through < first := by
  cases pruning with
  | empty reported => simp [reported.noLater]
  | listed _ _ later => exact later

theorem suffixSync (pruning : LongKeeperPruning authorization) :
    operations.sync operations.cache #[directory.path] pruning.afterUnlinks = .ok () pruning.stageInput.image :=
  match pruning with
  | .empty reported => reported.barriers.2.2
  | .listed reported _ _ => reported.suffixBarrier.2.2.2.2

theorem keepsKeeper (pruning : LongKeeperPruning authorization) : pruning.stageInput.image.keeper = before.image.keeper :=
  match pruning with
  | .empty _ => rfl
  | .listed _ _ _ => (ListedLaterWalPrune.settledImage before.image).2.2.2

/-- The reached staging input follows the complete approved suffix pass
and its barrier. The suffix is durably absent before replacement. -/
theorem stageInputEffects (pruning : LongKeeperPruning authorization) :
    EffectTrace layout.target before.image pruning.stageInput.image ∧ pruning.stageInput.image.later.DurablyEmpty := by
  cases pruning with
  | empty reported =>
    refine ⟨.syncPruned .authorized, ?_⟩
    simp [stageInput, afterUnlinks, acquired, FileImage.syncDirectory, LaterNames.syncDirectory,
      LaterNames.DurablyEmpty, LaterNames.settled, reported.noLater]
  | listed _ _ later =>
    exact ⟨.syncPruned ((EffectTrace.authorized (target := layout.target) (initial := before.image)).unlinks
      before.image.later.visible later), (ListedLaterWalPrune.settledImage before.image).1⟩

/-- Both approved pruning routes reach the same staged-replacement
schedule at their exact settled file image. -/
theorem finishAfterPrune (pruning : LongKeeperPruning authorization) :
    let run := performPaths directory layout.boundedPlan operations.removeFile throw
      (operations.write operations.cache) (operations.sync operations.cache) operations.renameFile
    finishBoundedMarkedOpen directory layout.boundedPlan authorization.keeper.metadata.byteSize.toNat
      operations.removeFile (operations.write operations.cache) (operations.sync operations.cache)
      operations.renameFile before.image =
    (do
      run (.replace .writeStaged)
      run (.replace .syncStaged)
      run (.replace .renameStaged)
      run (.replace .syncDirectory)
      pure () : EStateM IO.Error FileImage Unit) pruning.stageInput.image := by
  intro run
  cases pruning with
  | listed reported longer later => exact reported.finishAfterPrune longer later
  | empty reported =>
    have newer : layout.boundedPlan.newer = [] := reported.noLater
    have size : layout.boundedPlan.keeperBytes.size = layout.boundedPlan.keeperSize := layout.target.trimmedSize
    have long : layout.boundedPlan.keeperSize < authorization.keeper.metadata.byteSize.toNat :=
      size ▸ reported.longer
    have valid : layout.boundedPlan.valid = true :=
      (Plan.valid_iff layout.boundedPlan).mpr ⟨layout.target.firstCovered, Nat.le_of_eq size.symm, by simp [newer]⟩
    have suffix := reported.barriers.2.2
    change operations.sync operations.cache #[directory.path] before.image.syncDirectory =
      .ok () before.image.syncDirectory at suffix
    rw [show finishBoundedMarkedOpen directory layout.boundedPlan authorization.keeper.metadata.byteSize.toNat
        operations.removeFile (operations.write operations.cache) (operations.sync operations.cache)
        operations.renameFile before.image = _ from
      congrFun (finishBoundedMarkedOpen_long directory layout.boundedPlan authorization.keeper.metadata.byteSize.toNat
        operations.removeFile (operations.write operations.cache) (operations.sync operations.cache)
        operations.renameFile valid size long) before.image]
    simp only [newer, List.map_nil, List.nil_append, List.forM_eq_forM, List.forM_cons, List.forM_nil, performPaths,
      Publication.performReplacement, Array.push_empty, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
      authorization.settles reported.completed, suffix]
    rfl

end LongKeeperPruning

/-- The fresh staging schedule writes and flushes the selected prefix.
Its returned descriptor is inserted into the reached census. Native
projections identify both callbacks consumed by the bounded finisher. -/
structure ListedLongKeeperStageAt (pruning : LongKeeperPruning authorization) where
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
    (authorization.afterListing ++ pruning.afterAuthorization)).afterDrops beforeStage).slots,
      old.address ≠ slot.address
  fresh : ((held.listing.afterClose.afterDrops
    (authorization.afterListing ++ pruning.afterAuthorization)).afterDrops beforeStage).references slot.description = []
  captured : inventory =
    ((held.listing.afterClose.afterDrops
      (authorization.afterListing ++ pruning.afterAuthorization)).afterDrops beforeStage).insert slot atWrite
  wrote :
    let atPrune := pruning.stageInput
    writeFreshStagedWith tryCreate detachStale create write flush (directory.file .stagedWal) layout.keeper.bytes atPrune =
      .ok (inventory, slot, offset) (scratch atPrune layout.keeper.bytes false)
  writeProjection :
    let atPrune := pruning.stageInput
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
    let atPrune := pruning.stageInput
    let written := scratch atPrune layout.keeper.bytes false
    FsyncResult written (scratch atPrune layout.keeper.bytes true) effective
      (authorization.fsync (inventory, slot, offset) written)
  syncProjection : ∀ reached,
    let atPrune := pruning.stageInput
    let written := scratch atPrune layout.keeper.bytes false
    let path := directory.file .stagedWal
    stageFreshWithCache path layout.keeper.bytes (writeFreshStagedWith tryCreate detachStale create write flush)
      (operations.cache, atPrune) = .ok () (reached, written) →
    operations.sync operations.cache #[path] written.image =
      projectDirectorySync (grouped authorization #[path] (reached, written))

/-- Empty-suffix staging is the same report specialized to its existing
authorized starting image. -/
abbrev ListedLongKeeperStage (prune : ListedLongKeeperPrune authorization) :=
  ListedLongKeeperStageAt (.empty prune)

namespace ListedLongKeeperStageAt

variable {pruning : LongKeeperPruning authorization}

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
theorem stageCallbacks (reported : ListedLongKeeperStageAt pruning) :
    let atPrune := pruning.stageInput
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
theorem stageCustody (reported : ListedLongKeeperStageAt pruning) :
    let written := scratch (pruning.stageInput) layout.keeper.bytes false
    let handle : Handle := (reported.inventory, reported.slot, reported.offset)
    reported.bindings (directory.file .lock) = some (operations.descriptors.inode operations.slot.description) ∧
    (∃ refs : HeldLockReferences operations.slot.description,
      refs.live = reported.inventory.references operations.slot.description ∧
      (refs.afterFileDrops reported.beforeSync directory written).owners.Owns directory operations.slot.description) ∧
    ∃ observed : FsyncObservation (fun handle => handle.2.1.description)
        (fun handle => handle.1.inode handle.2.1.description) handle written
        (fun _ _ => scratch (pruning.stageInput) layout.keeper.bytes true)
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
    (fun _ _ => scratch (pruning.stageInput) layout.keeper.bytes true)
    reported.outcome
  refine ⟨?_, ⟨refs, rfl, ?_⟩, barrier, rfl, rfl, reported.stageBound, reported.keeperBound, reported.distinctKeeper⟩
  · rw [reported.lockBound, reported.captured]
    simp only [DescriptorInventory.insert, DescriptorInventory.afterDrops, held.listing.afterClose_eq, held.objectMap]
  · rw [refs.afterFileDrops_surviving remains]
    simp [written, scratch, LongKeeperPruning.stageInput, acquired, LockOwners.Owns, LockOwners.set]

/-- The bounded worker reaches the exact staged-file barrier after both
directory barriers and the fresh write. A reported staged-sync error is
returned directly. Rename and the final directory barrier run only after
successful staged sync. -/
theorem finishFromStage (reported : ListedLongKeeperStageAt pruning) :
    let written := pruning.stageInput.image.withScratch (some (layout.keeper.bytes, false))
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
  have size : layout.boundedPlan.keeperBytes.size = layout.boundedPlan.keeperSize := layout.target.trimmedSize
  have bytes : layout.boundedPlan.keeperBytes.extract 0 layout.boundedPlan.keeperSize = layout.keeper.bytes := by
    rw [← size, ByteArray.extract_zero_size]
    rfl
  have wrote : operations.write operations.cache (directory.file .stagedWal) layout.keeper.bytes pruning.stageInput.image =
      .ok () written := reported.stageCallbacks.1
  rw [pruning.finishAfterPrune]
  simp only [performPaths, Publication.performReplacement, Array.push_empty, Bind.bind, EStateM.bind, Pure.pure,
    EStateM.pure, bytes, wrote]
  dsimp only [path, keeper]
  cases operations.sync operations.cache #[directory.file .stagedWal] written with
  | ok value => cases value; rfl
  | error => rfl

end ListedLongKeeperStageAt

namespace ListedLongKeeperStage

variable {prune : ListedLongKeeperPrune authorization}

abbrev stageCallbacks (reported : ListedLongKeeperStage prune) :=
  ListedLongKeeperStageAt.stageCallbacks reported

abbrev stageCustody (reported : ListedLongKeeperStage prune) :=
  ListedLongKeeperStageAt.stageCustody reported

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
        pure () : EStateM IO.Error FileImage Unit) reached :=
  ListedLongKeeperStageAt.finishFromStage reported

end ListedLongKeeperStage

open WAL.Boundary (WalInodeImage CheckpointRepresentsPrefix)

variable {pruning : LongKeeperPruning authorization}
  {stage : ListedLongKeeperStageAt pruning}

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
structure ListedLongKeeperRename (stage : ListedLongKeeperStageAt pruning) where
  synced :
    let atPrune := pruning.stageInput
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
    let atPrune := pruning.stageInput
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
  · rw [rename.directoryBound, authorization.bound, held.lifetime.identifiesDirectory, held.objectMap]
  · rw [rename.keeperBound, rename.originalKeeper, stage.keeperBound]
  · rw [rename.sourceBound, rename.keeperBound, rename.originalKeeper]
    exact fun same => stage.distinctKeeper (Option.some.inj same)

/-- An effective rename publishes the original staged inode and consumes
the staging name. The pathname model's old crash choices come from the same
observed original inode projection. -/
theorem publishesInode (rename : ListedLongKeeperRename stage) (effective : rename.outcome.effective = true) :
    let durable := scratch (pruning.stageInput) layout.keeper.bytes true
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
  have keeping : durable.image.keeper.crashImages = before.image.keeper.crashImages := by
    have equal := congrArg Publication.Image.crashImages pruning.keepsKeeper
    exact equal
  rw [beforeChoices, ← keeping] at choices
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
    simp only [DescriptorInventory.insert, DescriptorInventory.afterDrops, held.listing.afterClose_eq, held.objectMap]
  · rw [refs.afterFileDrops_surviving remains]
    simp [acquired, LockOwners.Owns, LockOwners.set]

/-- A successful staged-file sync starts the exact rename and final sync
tail of the bounded worker. -/
theorem reachesRename (rename : ListedLongKeeperRename stage) :
    let durable := scratch (pruning.stageInput) layout.keeper.bytes true
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
  simpa only [show pruning.stageInput.image.withScratch (some (layout.keeper.bytes, false)) =
    (scratch (pruning.stageInput) layout.keeper.bytes false).image from rfl,
    staged] using stage.finishFromStage

/-- An unsuccessful rename returns the exact reached image and skips any
final directory sync. -/
theorem finishAfterError (rename : ListedLongKeeperRename stage) (failed : rename.outcome ≠ .completed) :
    let durable := scratch (pruning.stageInput) layout.keeper.bytes true
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

/-- The issued final directory barrier uses the retained directory
description after successful rename. The observation stops at the
actual callback input, where the directory and lock slots are still live. -/
structure ListedLongKeeperDirectoryIssue (rename : ListedLongKeeperRename stage) where
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
  projected :
    let durable := scratch (pruning.stageInput) layout.keeper.bytes true
    let renamed := afterKeeperRename durable layout.keeper.bytes
    operations.renameFile (directory.file .stagedWal) (directory.file (.walSegment layout.keeper.first)) durable.image =
      .ok () renamed.image →
    operations.sync operations.cache #[directory.path] renamed.image =
      projectDirectorySync (grouped authorization #[directory.path]
        (operations.cache.consume (directory.file .stagedWal), renamed))

namespace ListedLongKeeperDirectoryIssue

variable {rename : ListedLongKeeperRename stage}

/-- The live replacement and the original acquired owner at the issue. -/
def files (_issued : ListedLongKeeperDirectoryIssue rename) : LockedFileState FileImage :=
  afterKeeperRename (scratch pruning.stageInput layout.keeper.bytes true) layout.keeper.bytes

/-- The staged-file barrier consumed this name's pending cache entry. -/
def cache (_issued : ListedLongKeeperDirectoryIssue rename) : Cache Handle :=
  operations.cache.consume (directory.file .stagedWal)

/-- The inventory reached by the original opener when it issues fsync. -/
def inventory (issued : ListedLongKeeperDirectoryIssue rename) : DescriptorInventory :=
  stage.inventory.afterDrops (stage.beforeSync ++ rename.afterStageSync ++ issued.afterRename)

/-- Interpret the directory effect independently of any callback return. -/
def stopped (issued : ListedLongKeeperDirectoryIssue rename) (effective : Bool) : LockedFileState FileImage :=
  if effective then settleKeeperBinding issued.files else issued.files

/-- Both original issuing slots survive the final barrier, and its
effect-time keeper binding is the exact inode published by rename. -/
theorem custody (issued : ListedLongKeeperDirectoryIssue rename) :
    let atSync := issued.inventory
    held.lifetime.directorySlot ∈ atSync.slots ∧ operations.slot ∈ atSync.slots ∧
    issued.bindings directory.path = some (atSync.inode held.lifetime.directorySlot.description) ∧
    issued.bindings (directory.file .lock) = some (atSync.inode operations.slot.description) ∧
    issued.bindings (directory.file .stagedWal) = none ∧
    issued.bindings (directory.file (.walSegment layout.keeper.first)) = some (stage.inventory.inode stage.slot.description) := by
  intro atSync
  have effective : rename.outcome.effective = true := by rw [issued.completed]; rfl
  refine ⟨issued.directoryRetained, issued.lockRetained, ?_, ?_,
    issued.stageAbsent.trans (rename.renamedSource effective),
    issued.keeperBound.trans (rename.renamedKeeper effective)⟩
  · simp only [atSync, inventory, DescriptorInventory.afterDrops, stage.captured, DescriptorInventory.insert,
      held.listing.afterClose_eq, held.objectMap]
    exact issued.directoryBound
  · simp only [atSync, inventory, DescriptorInventory.afterDrops, stage.captured, DescriptorInventory.insert,
      held.listing.afterClose_eq, held.objectMap]
    exact issued.lockBound

private theorem renamed (issued : ListedLongKeeperDirectoryIssue rename) :
    let durable := scratch pruning.stageInput layout.keeper.bytes true
    operations.renameFile (directory.file .stagedWal) (directory.file (.walSegment layout.keeper.first)) durable.image =
      .ok () issued.files.image := by
  simpa only [issued.completed, files] using rename.reported

/-- The native cache resolver supplies the exact directory handle before
invoking fsync. The directory route leaves the reached cache in place. -/
theorem resolvesDirectory (issued : ListedLongKeeperDirectoryIssue rename) :
    issued.cache.resolve directory.path directory.path authorization.openRead issued.files =
      .ok (operations.descriptors, held.lifetime.directorySlot, 0) (issued.cache, issued.files) := by
  simp [Cache.resolve, cache, Cache.consume, held.capturedDirectory]

/-- The program after the returned rename calls the exact grouped
directory barrier. This equality imposes no outcome on that barrier. -/
theorem finishesFromIssue (issued : ListedLongKeeperDirectoryIssue rename) :
    finishBoundedMarkedOpen directory layout.boundedPlan authorization.keeper.metadata.byteSize.toNat
      operations.removeFile (operations.write operations.cache) (operations.sync operations.cache)
      operations.renameFile before.image = operations.sync operations.cache #[directory.path] issued.files.image := by
  rw [rename.reachesRename]
  simp only [Bind.bind, EStateM.bind]
  rw [issued.renamed]
  change (operations.sync operations.cache #[directory.path] >>= fun _ => pure ()) issued.files.image = _
  simp only [Bind.bind, EStateM.bind]
  cases operations.sync operations.cache #[directory.path] issued.files.image with
  | ok value reached => cases value; rfl
  | error cause reached => rfl

theorem groupedCallback (issued : ListedLongKeeperDirectoryIssue rename) :
    operations.sync operations.cache #[directory.path] issued.files.image =
      projectDirectorySync (grouped authorization #[directory.path] (issued.cache, issued.files)) :=
  issued.projected issued.renamed

end ListedLongKeeperDirectoryIssue

/-- A returned final directory sync adds the outcome and effect to the
same issued call that also supports an interrupted execution. -/
structure ListedLongKeeperSettlement (rename : ListedLongKeeperRename stage)
    extends ListedLongKeeperDirectoryIssue rename where
  outcome : DelayedDirectorySyncOutcome
  effect : authorization.fsync (operations.descriptors, held.lifetime.directorySlot, 0) toListedLongKeeperDirectoryIssue.files =
    match outcome with
    | .completed => .ok () (toListedLongKeeperDirectoryIssue.stopped true)
    | .errorBeforeEffect cause => .error cause toListedLongKeeperDirectoryIssue.files
    | .errorAfterEffect cause => .error cause (toListedLongKeeperDirectoryIssue.stopped true)

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
    reported.bindings (directory.file (.walSegment layout.keeper.first)) = some (stage.inventory.inode stage.slot.description) :=
  reported.toListedLongKeeperDirectoryIssue.custody

/-- When the final sync takes effect, its reached image has exactly the
crash bytes of the replacement inode now bound to the keeper path. -/
theorem settledInode (reported : ListedLongKeeperSettlement rename) :
    let durable := scratch (pruning.stageInput) layout.keeper.bytes true
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
    let durable := scratch (pruning.stageInput) layout.keeper.bytes true
    let renamed := afterKeeperRename durable layout.keeper.bytes
    operations.sync operations.cache #[directory.path] renamed.image =
      match reported.outcome with
      | .completed => .ok () (settleKeeperBinding renamed).image
      | .errorBeforeEffect cause => .error (IO.userError s!"sync failed for '{directory.path}': {cause}") renamed.image
      | .errorAfterEffect cause =>
        .error (IO.userError s!"sync failed for '{directory.path}': {cause}") (settleKeeperBinding renamed).image := by
  intro durable renamed
  let issue := reported.toListedLongKeeperDirectoryIssue
  change operations.sync operations.cache #[directory.path] issue.files.image = _
  rw [issue.groupedCallback, grouped, SyncPathGroup.run_single]
  simp only [sync, issue.resolvesDirectory]
  rw [reported.effect]
  cases reported.outcome <;> rfl

/-- After the reported successful rename, the actual bounded finisher
returns the exact final grouped directory outcome. -/
theorem finishResult (reported : ListedLongKeeperSettlement rename) :
    let durable := scratch (pruning.stageInput) layout.keeper.bytes true
    let renamed := afterKeeperRename durable layout.keeper.bytes
    finishBoundedMarkedOpen directory layout.boundedPlan authorization.keeper.metadata.byteSize.toNat
      operations.removeFile (operations.write operations.cache) (operations.sync operations.cache)
      operations.renameFile before.image = operations.sync operations.cache #[directory.path] renamed.image :=
  reported.toListedLongKeeperDirectoryIssue.finishesFromIssue

private theorem prependPruning (pruning : LongKeeperPruning authorization) {rest : List Step}
    (tail : ∀ action prior next, ReachesAction layout.target pruning.stageInput.image rest action prior →
      prior.effect layout.target action = some next →
      performPaths directory layout.plan operations.removeFile throw (operations.write operations.cache)
        (operations.sync operations.cache) operations.renameFile action prior = .ok () next) :
    ∀ action prior next,
      ReachesAction layout.target before.image.syncDirectory
        (before.image.later.visible.map Step.unlink ++ Step.syncPruned :: rest) action prior →
      prior.effect layout.target action = some next →
      performPaths directory layout.plan operations.removeFile throw (operations.write operations.cache)
        (operations.sync operations.cache) operations.renameFile action prior = .ok () next := by
  have barrier := ReachesAction.prependHealthy (target := layout.target) (initial := pruning.afterUnlinks)
    (next := pruning.stageInput.image) (head := .syncPruned) (rest := rest) rfl pruning.suffixSync tail
  cases pruning with
  | empty reported => simpa [reported.noLater, LongKeeperPruning.afterUnlinks] using barrier
  | listed reported _ _ => exact reported.unlinks.prependHealthy layout.plan barrier

/-- Per-operation results supply the whole finishing contract on the
long-keeper route, including all reported suffix unlinks. -/
theorem healthyFinish (reported : ListedLongKeeperSettlement rename)
    (succeeded : reported.outcome = .completed) : operations.HealthyFinish := by
  let written := scratch (pruning.stageInput) layout.keeper.bytes false
  let durable := scratch (pruning.stageInput) layout.keeper.bytes true
  let renamed := afterKeeperRename durable layout.keeper.bytes
  have long : layout.plan.keeperSize < layout.plan.keeperBytes.size := calc
    layout.plan.keeperSize = layout.keeper.bytes.size := layout.target.trimmedSize.symm
    _ < authorization.keeper.metadata.byteSize.toNat := pruning.longer
    _ = layout.plan.keeperBytes.size := authorization.keeper.extent
  have declined : layout.plan.alignedWithoutPrune = false := by
    simp [Plan.alignedWithoutPrune, Nat.ne_of_gt long]
  have schedule : layout.plan.finishActions =
      before.image.later.visible.map Step.unlink ++
        [.syncPruned, .replace .writeStaged, .replace .syncStaged, .replace .renameStaged, .replace .syncDirectory] := by
    simp [Plan.finishActions, declined, Plan.actions, steps, long, Publication.steps]
    rfl
  have selectedSize : layout.keeper.bytes.size = layout.plan.keeperSize := layout.target.trimmedSize
  have selectedBytes : layout.plan.keeperBytes.extract 0 layout.plan.keeperSize = layout.keeper.bytes := by
    rw [← selectedSize]
    exact ByteArray.extract_append_eq_left rfl
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
  refine prependPruning pruning ?_
  refine ReachesAction.prependHealthy (next := written.image) rfl ?_ ?_
  · simp only [performPaths, Publication.performReplacement, selectedBytes]
    exact stage.stageCallbacks.1
  refine ReachesAction.prependHealthy (next := durable.image) rfl ?_ ?_
  · simp only [performPaths, Publication.performReplacement, Array.push_empty]
    exact staged
  refine ReachesAction.prependHealthy (next := renamed.image) rfl renameResult ?_
  refine ReachesAction.prependHealthy (next := (settleKeeperBinding renamed).image) rfl final ?_
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
  authorization.installs metadata pruning.completed (reported.healthyFinish succeeded) admission keeperValid laterValid
    following accepted ordered

end ListedLongKeeperSettlement
end Alvoki.Storage.DiskSession
