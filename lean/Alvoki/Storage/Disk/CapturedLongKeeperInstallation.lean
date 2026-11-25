import Alvoki.Storage.Disk.CapturedAlignedInstallation
import Alvoki.Storage.Disk.KeeperDirectoryInterruption

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix WalInodeImage)

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {published : CheckpointPublication.Image}
  {calls : CapturedAlignedCallbacks admission} {report : CapturedMarkedReadReports admission layout published}
  {vacant : TryLockObserves retry.owners directory (.ok true)} {checkpoint : Option (PackedTable × UInt64)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}

private abbrev ReplacementState := CensusDirectoryCache × LockedFileState FileImage

private def keeperClose (slot : DescriptorSlot) : LockReferenceDrop :=
  .closed slot.reference.process slot.reference.fd

private theorem insert_thenClose (before : DescriptorInventory) (slot : DescriptorSlot)
    (free : ∀ current ∈ before.slots, current.address ≠ slot.address) (drops : List LockReferenceDrop) :
    (before.insert slot free).afterDrops (drops ++ [keeperClose slot]) = before.afterDrops (drops ++ [keeperClose slot]) := by
  cases before with
  | mk slots distinct inode =>
    simp [DescriptorInventory.insert, DescriptorInventory.afterDrops, keeperClose, LockReferenceDrop.removes,
      List.all_append]

/-- The long keeper is read without a pending capture. Its observed close
precedes the authorization barrier. The empty later-name route still
performs its suffix directory barrier before the staged replacement. -/
structure CapturedLongKeeperFinish (calls : CapturedAlignedCallbacks admission)
    (report : CapturedMarkedReadReports admission layout published)
    (vacant : TryLockObserves retry.owners directory (.ok true))
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint) where
  reader : CapturedKeeperOpenReports report
  authorization : ListedDirectoryAuthorization (calls.heldReport report vacant selected)
  readClosed : authorization.afterListing = reader.beforeOpen ++
    (reader.duringRead ++ [keeperClose report.wal.keeper.calls.slot])
  prune : ListedLongKeeperPrune authorization
  stage : ListedLongKeeperStage prune
  rename : ListedLongKeeperRename stage
  settlement : ListedLongKeeperSettlement rename
  completed : settlement.outcome = .completed
  afterSettlement : List LockReferenceDrop
  lockRetained : admission.owner ∈ (settlement.inventory.afterDrops afterSettlement).slots
  directoryRetained : admission.cached ∈ (settlement.inventory.afterDrops afterSettlement).slots

namespace CapturedLongKeeperFinish

theorem sameKeeper (finish : CapturedLongKeeperFinish calls report vacant selected) :
    finish.authorization.keeper = report.wal.keeper.observesFile :=
  (calls.wal report vacant).keeperObserved finish.authorization

theorem longer (finish : CapturedLongKeeperFinish calls report vacant selected) :
    layout.keeper.bytes.size < report.wal.keeper.calls.metadata.byteSize.toNat := by
  have physical := finish.prune.longer
  rw [finish.sameKeeper] at physical
  exact physical

/-- The old handle never enters the cache and its reported finalizer
removes the newly allocated slot from the census used by the directory
barrier. The other reported drop effects are preserved. -/
theorem readAndClose (finish : CapturedLongKeeperFinish calls report vacant selected) :
    finish.reader.readKeeper (admission.cache, finish.reader.atOpen, admission.held) =
      .ok layout.keeper.bytes (admission.cache, finish.reader.afterRead, admission.held) ∧
    finish.reader.afterRead.afterDrops [keeperClose report.wal.keeper.calls.slot] =
      report.listing.afterClose.afterDrops finish.authorization.afterListing := by
  refine ⟨finish.reader.readsLong finish.longer, ?_⟩
  rw [CapturedKeeperOpenReports.afterRead, finish.reader.opened, finish.readClosed,
    ← DescriptorInventory.afterDrops_append, DescriptorInventory.afterDrops_append]
  exact insert_thenClose _ _ finish.reader.free _

noncomputable def census (finish : CapturedLongKeeperFinish calls report vacant selected) : DescriptorInventory :=
  finish.settlement.inventory.afterDrops finish.afterSettlement

noncomputable def settled (finish : CapturedLongKeeperFinish calls report vacant selected) : LockedFileState FileImage :=
  finish.settlement.stopped true

theorem sameCensusObjects (finish : CapturedLongKeeperFinish calls report vacant selected) :
    finish.census.inode = admission.reached.inode := by
  unfold census ListedLongKeeperDirectoryIssue.inventory
  rw [finish.stage.captured]
  change (calls.heldReport report vacant selected).listing.afterClose.inode = admission.reached.inode
  rw [(calls.heldReport report vacant selected).listing.afterClose_eq]
  rfl

/-- The last barrier settles the replacement's name. Any already open
description of the old inode still refers to its former bytes. -/
theorem replacementInodes (finish : CapturedLongKeeperFinish calls report vacant selected) :
    let replacement := finish.stage.inventory.inode finish.stage.slot.description
    let old := finish.rename.original
    let inodes := finish.settlement.toListedLongKeeperDirectoryIssue.stoppedInodes true
    inodes.active = replacement ∧ inodes.crashBindings = [replacement] ∧
      inodes.visible replacement = layout.keeper.bytes ∧ inodes.crashBytes replacement = [layout.keeper.bytes] ∧
      inodes.visible old.active = old.visible old.active ∧ inodes.crashBytes old.active = old.crashBytes old.active := by
  intro replacement old inodes
  have different : old.active ≠ replacement := by
    change finish.rename.original.active ≠ finish.stage.inventory.inode finish.stage.slot.description
    rw [finish.rename.originalKeeper]
    exact finish.stage.distinctKeeper.symm
  have projected : inodes = (old.renameSynced replacement layout.keeper.bytes).settleBinding := rfl
  rw [projected]
  simp [WalInodeImage.settleBinding, WalInodeImage.renameSynced, different]

private def fileAction {result : Type} (action : EStateM IO.Error FileImage result) :
    EStateM IO.Error ReplacementState result := fun (cache, before) =>
  match action before.image with
  | .ok value after => .ok value (cache, { before with image := after })
  | .error cause after => .error cause (cache, { before with image := after })

private noncomputable def stageAt (finish : CapturedLongKeeperFinish calls report vacant selected)
    (path : FilePath) (bytes : ByteArray) : EStateM IO.Error ReplacementState Unit :=
  stageFreshWithCache path bytes
    (writeFreshStagedWith finish.stage.tryCreate finish.stage.detachStale finish.stage.create
      finish.stage.write finish.stage.flush)

private def syncAt (finish : CapturedLongKeeperFinish calls report vacant selected) (resolved : DiskDirectory) :=
  SyncPathGroup.run (sync resolved.path finish.authorization.openRead finish.authorization.fsync)

private noncomputable def repairAt (finish : CapturedLongKeeperFinish calls report vacant selected)
    (resolved : DiskDirectory) (plan : Plan) (size : Nat) :
    EStateM IO.Error ReplacementState Unit :=
  finishBoundedMarkedOpen resolved plan size (fun path => fileAction (calls.removeFile path))
    finish.stageAt (finish.syncAt resolved) (fun source target => fileAction (calls.renameFile source target))

private theorem syncDirectory (finish : CapturedLongKeeperFinish calls report vacant selected)
    {cache : CensusDirectoryCache} {before after : LockedFileState FileImage}
    (directoryCached : cache.directory = some (admission.reached, admission.cached, 0))
    (returned : finish.authorization.fsync (admission.reached, admission.cached, 0) before = .ok () after) :
    finish.syncAt directory #[directory.path] (cache, before) = .ok () (cache, after) := by
  simp [syncAt, SyncPathGroup.run_single, sync, Cache.resolve, directoryCached, returned, withCache]

/-- The bounded worker follows its shared long-repair schedule. The
reported staged write inserts exactly the handle consumed by the staged
fsync. Rename follows that sync, and the last directory sync uses the
original directory handle and the cache with the staged entry removed. -/
theorem repairAt_returns (finish : CapturedLongKeeperFinish calls report vacant selected) :
    finish.repairAt directory layout.boundedPlan layout.plan.keeperBytes.size (admission.cache, admission.held) =
      .ok () (admission.cache, finish.settled) := by
  let authorized : LockedFileState FileImage := { admission.held with image := retry.image.syncDirectory }
  let atStage := (LongKeeperPruning.empty finish.prune).stageInput
  let stagePath := directory.file .stagedWal
  let written : LockedFileState FileImage :=
    { atStage with image := atStage.image.withScratch (some (layout.keeper.bytes, false)) }
  let durable : LockedFileState FileImage :=
    { atStage with image := atStage.image.withScratch (some (layout.keeper.bytes, true)) }
  let handle := (finish.stage.inventory, finish.stage.slot, finish.stage.offset)
  let remembered := admission.cache.remember stagePath handle
  have firstEffect := finish.authorization.effect
  rw [finish.prune.completed] at firstEffect
  have first : finish.syncAt directory #[directory.path] (admission.cache, admission.held) =
      .ok () (admission.cache, authorized) := finish.syncDirectory rfl firstEffect
  have second : finish.syncAt directory #[directory.path] (admission.cache, authorized) =
      .ok () (admission.cache, atStage) := finish.syncDirectory rfl finish.prune.synced
  have stage : finish.stageAt stagePath layout.keeper.bytes (admission.cache, atStage) =
      .ok () (remembered, written) := by
    have wrote : writeFreshStagedWith finish.stage.tryCreate finish.stage.detachStale finish.stage.create
        finish.stage.write finish.stage.flush stagePath layout.keeper.bytes atStage = .ok handle written :=
      finish.stage.wrote
    simp only [stageAt, stageFreshWithCache, remembered, wrote]
  have consume : admission.cache.consume stagePath = admission.cache := rfl
  have persisted : finish.syncAt directory #[stagePath] (remembered, written) =
      .ok () (admission.cache, durable) := by
    have synced : finish.authorization.fsync handle written = .ok () durable := finish.rename.synced
    dsimp only [syncAt, remembered]
    rw [SyncPathGroup.run_single,
      syncRemembered (file_ne_directory directory .stagedWal) handle finish.authorization.openRead
        finish.authorization.fsync written, consume, synced]
  have moved : fileAction (calls.renameFile stagePath (directory.file (.walSegment layout.keeper.first)))
      (admission.cache, durable) = .ok () (admission.cache, finish.settlement.files) := by
    have returned := finish.rename.reported
    dsimp only at returned
    rw [finish.settlement.completed] at returned
    change calls.renameFile stagePath (directory.file (.walSegment layout.keeper.first)) durable.image =
      .ok () finish.settlement.files.image at returned
    simp only [fileAction, returned]
    rfl
  have settled : finish.syncAt directory #[directory.path] (admission.cache, finish.settlement.files) =
      .ok () (admission.cache, finish.settled) := by
    have effect := finish.settlement.effect
    rw [finish.completed] at effect
    exact finish.syncDirectory rfl effect
  have size : layout.boundedPlan.keeperBytes.size = layout.boundedPlan.keeperSize := layout.target.trimmedSize
  have later : layout.boundedPlan.newer = [] := finish.prune.noLater
  have valid : layout.boundedPlan.valid = true :=
    (Plan.valid_iff _).mpr ⟨layout.target.firstCovered, Nat.le_of_eq size.symm, by simp [later]⟩
  have bytes : layout.boundedPlan.keeperBytes.extract 0 layout.boundedPlan.keeperSize = layout.keeper.bytes := by
    rw [← size, ByteArray.extract_zero_size]
    rfl
  have measured : report.wal.keeper.calls.metadata.byteSize.toNat = layout.plan.keeperBytes.size :=
    report.wal.keeper.observesFile.extent
  have long : layout.boundedPlan.keeperSize < layout.plan.keeperBytes.size := by
    rw [← size, ← measured]
    exact finish.longer
  have keeper : layout.boundedPlan.keeper = layout.keeper.first := rfl
  change finish.repairAt directory layout.boundedPlan layout.plan.keeperBytes.size (admission.cache, admission.held) = _
  unfold repairAt
  rw [finishBoundedMarkedOpen_long _ _ _ _ _ _ _ valid size long]
  simp only [later, List.map_nil, List.nil_append, List.forM_eq_forM, List.forM_cons, List.forM_nil,
    performPaths, Publication.performReplacement, bytes, keeper, Array.push_empty, Bind.bind, EStateM.bind,
    Pure.pure, EStateM.pure, first, second, stage, persisted, moved, settled, stagePath]

private noncomputable def finishAt (finish : CapturedLongKeeperFinish calls report vacant selected)
    (resolved : DiskDirectory) (_owner : DescriptorSlot) (cache : CensusDirectoryCache) (prepared : Plan × Reopened × Nat) :
    EStateM IO.Error CensusOpenState Reopened := fun (entered, before) =>
  let (plan, opened, size) := prepared
  match finish.repairAt resolved plan size (cache, before) with
  | .ok () (_, reached) => .ok opened (finish.census, reached)
  | .error cause (_, reached) => .error cause (entered, reached)

/-- The native-shaped open with the reached long replacement callbacks.
Ready state and the two fresh reference identities are allocated only
after the final replacement barrier returns. -/
noncomputable def run (finish : CapturedLongKeeperFinish calls report vacant selected) :
    EStateM.Result IO.Error CensusOpenState SegmentedSession :=
  calls.runWithFinish report finish.finishAt

/-- The actual selected read, staged replacement and successful final
directory barrier lead to the installed session. The new canonical keeper
is the staged inode and the original selected checkpoint supplies replay. -/
theorem installs {description keeperFirst : Nat} {initial : DescriptorInventory}
    {origin source : LockedFileState FileImage}
    (trace : LockCensusTrace directory description initial source inventory retry)
    (earlier : ReportedReopenPrefix directory keeperFirst origin source)
    (last : inventory.references description = [])
    (distinct : admission.owner.description ≠ description)
    (distinctCached : admission.cached.description ≠ description)
    (lockObject : inventory.inode admission.owner.description = initial.inode description)
    (finish : CapturedLongKeeperFinish calls report (trace.freshFlockAllowed.mpr last) selected)
    {metadata : IO.FS.Metadata}
    (marker : admission.lookup (directory.file .walBoundary) (admission.reached, admission.held) =
      .ok (.ok metadata) (admission.reached, admission.held))
    (keeperValid : retry.image.keeper.Valid layout.target.Accepts)
    (laterValid : retry.image.later.Beyond layout.range.through)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history) :
    ReportedReopenPrefix directory keeperFirst origin retry ∧
    report.bindings (directory.file .lock) = some (initial.inode description) ∧
    finish.reader.readKeeper (admission.cache, finish.reader.atOpen, admission.held) =
      .ok layout.keeper.bytes (admission.cache, finish.reader.afterRead, admission.held) ∧
    finish.reader.afterRead.afterDrops [keeperClose report.wal.keeper.calls.slot] =
      report.listing.afterClose.afterDrops finish.authorization.afterListing ∧
    admission.owner ∈ finish.census.slots ∧ admission.cached ∈ finish.census.slots ∧
    finish.census.inode = admission.reached.inode ∧
    finish.settlement.bindings (directory.file (.walSegment layout.keeper.first)) =
      some (finish.stage.inventory.inode finish.stage.slot.description) ∧
    finish.settled.image.withKeeperInodes (finish.settlement.toListedLongKeeperDirectoryIssue.stoppedInodes true) =
      finish.settled.image ∧
    report.reads.ObservesSelected directory retry.image.directory.active.manifest published.durable ∧
    ∃ session, finish.run = .ok session (finish.census, finish.settled) ∧
      CachedRetryInstalled (before := retry) report.walReads admission.reached admission.owner report.bindings
        published calls.liveRefs (.ok session finish.settled) := by
  have effects := finish.settlement.toListedLongKeeperDirectoryIssue.stoppedEffects true
  have prepared : Prepared retry.image layout.target layout.plan :=
    ⟨rfl, keeperValid, laterValid, rfl, rfl, rfl, layout.visible⟩
  have safe := effects.valid prepared.pair prepared.keeperPrefix prepared.newer
  have pruned := (LongKeeperPruning.empty finish.prune).stageInputEffects.2
  have ready : finish.settled.image.Ready layout.target := by
    refine ⟨safe.selected, safe.settled, rfl, rfl, ?_⟩
    exact pruned
  have reached (opened : Reopened) : finish.finishAt directory admission.owner admission.cache
      (layout.boundedPlan, opened, layout.plan.keeperBytes.size) (admission.reached, admission.held) =
      .ok opened (finish.census, { admission.held with image := finish.settled.image }) := by
    rw [finishAt, finish.repairAt_returns]
    rfl
  obtain ⟨prefixReached, vacant, _, _, _, oldObject, _, _⟩ :=
    trace.capturesAfterAdmission earlier last admission distinct distinctCached lockObject (calls.recoverWithFinish report finish.finishAt)
  have sameLock := report.sameObjects.2.1.trans (congrArg some oldObject)
  obtain ⟨session, returned, installed⟩ :=
    CapturedAlignedCallbacks.installsWithFinish (calls := calls) (report := report) vacant marker laterValid
      following accepted ordered selected finish.finishAt reached ready effects
  exact ⟨prefixReached, sameLock, finish.readAndClose.1, finish.readAndClose.2, finish.lockRetained,
    finish.directoryRetained, finish.sameCensusObjects, finish.settlement.settledInode.1,
    finish.settlement.toListedLongKeeperDirectoryIssue.projectsStoppedInodes true,
    report.chunkReads, session, returned, installed⟩

end CapturedLongKeeperFinish

end Alvoki.Storage.DiskSession
