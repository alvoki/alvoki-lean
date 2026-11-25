import Alvoki.Storage.Disk.CapturedAlignedInstallation
import Alvoki.Storage.Disk.CapturedCheckpointReadCensus
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

private abbrev ReplacementSyncState := CensusOpenState × List (List LockReferenceDrop)
private abbrev ReplacementState := CensusDirectoryCache × ReplacementSyncState

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
    (reader.duringRead ++ [report.wal.keeper.calls.slot.closeEvent])
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
    finish.reader.afterRead.afterDrops [report.wal.keeper.calls.slot.closeEvent] =
      report.listing.afterClose.afterDrops finish.authorization.afterListing := by
  refine ⟨finish.reader.readsLong finish.longer, ?_⟩
  rw [CapturedKeeperOpenReports.afterRead, finish.reader.opened, finish.readClosed,
    ← DescriptorInventory.afterDrops_append, DescriptorInventory.afterDrops_append]
  exact DescriptorInventory.insert_thenClose _ _ finish.reader.free _

/-- The staged allocation starts from the inventory reached by the
temporary keeper close and the measured drops before staging. -/
theorem stagedAllocation (finish : CapturedLongKeeperFinish calls report vacant selected) :
    let entered := finish.reader.afterRead.afterDrops [report.wal.keeper.calls.slot.closeEvent]
    let beforeStage := (entered.afterDrops finish.prune.afterAuthorization).afterDrops finish.stage.beforeStage
    ∃ free : ∀ slot ∈ beforeStage.slots, slot.address ≠ finish.stage.slot.address,
      finish.stage.inventory = beforeStage.insert finish.stage.slot free := by
  dsimp only
  simp only [finish.readAndClose.2, DescriptorInventory.afterDrops_append, List.append_assoc]
  have available := finish.stage.atWrite
  have opened := finish.stage.captured
  simp only [DescriptorInventory.afterDrops_append, List.append_assoc] at available opened
  exact ⟨available, opened⟩

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

/-- Subsequent events belong to the successful syscall that was reached.
The empty suffix still calls its directory sync, which has no extra drops. -/
private noncomputable def syncDrops (finish : CapturedLongKeeperFinish calls report vacant selected) :
    List (List LockReferenceDrop) :=
  [finish.prune.afterAuthorization, [], finish.rename.afterStageSync, finish.afterSettlement]

private def fileAction {result : Type} (action : EStateM IO.Error FileImage result)
    (drops : List LockReferenceDrop := []) :
    EStateM IO.Error ReplacementState result := fun (cache, (census, before), remaining) =>
  match action before.image with
  | .ok value after => .ok value (cache, (census.afterDrops drops, { before with image := after }), remaining)
  | .error cause after => .error cause (cache, (census, { before with image := after }), remaining)

private noncomputable def stageAt (finish : CapturedLongKeeperFinish calls report vacant selected)
    (path : FilePath) (bytes : ByteArray) : EStateM IO.Error ReplacementState Unit :=
  stageFreshWithCache path bytes fun name payload ((census, before), remaining) =>
    match writeFreshStagedWith finish.stage.tryCreate finish.stage.detachStale finish.stage.create
        finish.stage.write finish.stage.flush name payload before with
    | .ok handle after => .ok handle ((handle.1.afterDrops finish.stage.beforeSync, after), remaining)
    | .error cause after => .error cause ((census, after), remaining)

private def openForSync (finish : CapturedLongKeeperFinish calls report vacant selected) (path : FilePath) :
    EStateM IO.Error ReplacementSyncState (DescriptorInventory × DescriptorSlot × Nat) :=
  fun ((census, before), remaining) =>
  match finish.authorization.openRead path before with
  | .ok handle after => .ok handle ((census, after), remaining)
  | .error cause after => .error cause ((census, after), remaining)

private def fsyncWithCensus (finish : CapturedLongKeeperFinish calls report vacant selected)
    (handle : DescriptorInventory × DescriptorSlot × Nat) : EStateM IO.Error ReplacementSyncState Unit :=
  fun ((census, before), remaining) =>
  match finish.authorization.fsync handle before with
  | .ok () after => .ok () ((census.afterDrops (remaining.headD []), after), remaining.tail)
  | .error cause after => .error cause ((census, after), remaining)

private noncomputable def syncAt (finish : CapturedLongKeeperFinish calls report vacant selected)
    (resolved : DiskDirectory) :=
  SyncPathGroup.run (sync resolved.path finish.openForSync finish.fsyncWithCensus)

private noncomputable def repairAt (finish : CapturedLongKeeperFinish calls report vacant selected)
    (resolved : DiskDirectory) (plan : Plan) (size : Nat) :
    EStateM IO.Error ReplacementState Unit :=
  finishBoundedMarkedOpen resolved plan size (fun path => fileAction (calls.removeFile path))
    finish.stageAt (finish.syncAt resolved)
    (fun source target => fileAction (calls.renameFile source target) finish.settlement.afterRename)

private theorem syncDirectory (finish : CapturedLongKeeperFinish calls report vacant selected)
    {cache : CensusDirectoryCache} {before after : LockedFileState FileImage}
    {entered : DescriptorInventory} {drops : List LockReferenceDrop} {remaining : List (List LockReferenceDrop)}
    (directoryCached : cache.directory = some (admission.reached, admission.cached, 0))
    (returned : finish.authorization.fsync (admission.reached, admission.cached, 0) before = .ok () after) :
    finish.syncAt directory #[directory.path] (cache, (entered, before), drops :: remaining) =
      .ok () (cache, (entered.afterDrops drops, after), remaining) := by
  simp [syncAt, SyncPathGroup.run_single, sync, Cache.resolve, directoryCached, fsyncWithCensus, returned, withCache]

/-- The bounded worker follows its shared long-repair schedule. The
reported staged write inserts exactly the handle consumed by the staged
fsync. Rename follows that sync, and the last directory sync uses the
original directory handle and the cache with the staged entry removed. -/
theorem repairAt_returns (finish : CapturedLongKeeperFinish calls report vacant selected) :
    finish.repairAt directory layout.boundedPlan layout.plan.keeperBytes.size
      (admission.cache, (finish.reader.afterRead.afterDrops [report.wal.keeper.calls.slot.closeEvent], admission.held),
        finish.syncDrops) = .ok () (admission.cache, (finish.census, finish.settled), []) := by
  let entered := finish.reader.afterRead.afterDrops [report.wal.keeper.calls.slot.closeEvent]
  let beforeStage := entered.afterDrops finish.prune.afterAuthorization
  let authorized : LockedFileState FileImage := { admission.held with image := retry.image.syncDirectory }
  let atStage := (LongKeeperPruning.empty finish.prune).stageInput
  let stagePath := directory.file .stagedWal
  let written : LockedFileState FileImage :=
    { atStage with image := atStage.image.withScratch (some (layout.keeper.bytes, false)) }
  let durable : LockedFileState FileImage :=
    { atStage with image := atStage.image.withScratch (some (layout.keeper.bytes, true)) }
  let handle := (finish.stage.inventory, finish.stage.slot, finish.stage.offset)
  let remembered := admission.cache.remember stagePath handle
  obtain ⟨free, allocated⟩ := finish.stagedAllocation
  let beforeSync := ((beforeStage.afterDrops finish.stage.beforeStage).insert finish.stage.slot free).afterDrops
    finish.stage.beforeSync
  have openedCensus : beforeSync = finish.stage.inventory.afterDrops finish.stage.beforeSync :=
    congrArg (fun inventory => inventory.afterDrops finish.stage.beforeSync) allocated.symm
  let afterSync := beforeSync.afterDrops finish.rename.afterStageSync
  let movedCensus := afterSync.afterDrops finish.settlement.afterRename
  have firstEffect := finish.authorization.effect
  rw [finish.prune.completed] at firstEffect
  have first : finish.syncAt directory #[directory.path] (admission.cache, (entered, admission.held), finish.syncDrops) =
      .ok () (admission.cache, (beforeStage, authorized), [[], finish.rename.afterStageSync, finish.afterSettlement]) :=
    finish.syncDirectory rfl firstEffect
  have second : finish.syncAt directory #[directory.path]
      (admission.cache, (beforeStage, authorized), [[], finish.rename.afterStageSync, finish.afterSettlement]) =
      .ok () (admission.cache, (beforeStage, atStage), [finish.rename.afterStageSync, finish.afterSettlement]) := by
    have returned := finish.syncDirectory (entered := beforeStage) (drops := []) (cache := admission.cache)
      (remaining := [finish.rename.afterStageSync, finish.afterSettlement]) rfl finish.prune.synced
    have unchanged : beforeStage.afterDrops [] = beforeStage := by
      cases beforeStage
      simp only [DescriptorInventory.afterDrops, List.all_nil,
        List.filter_eq_self.mpr (fun _ _ => rfl)]
    rw [unchanged] at returned
    exact returned
  have stage : finish.stageAt stagePath layout.keeper.bytes
      (admission.cache, (beforeStage, atStage), [finish.rename.afterStageSync, finish.afterSettlement]) =
      .ok () (remembered, (beforeSync, written), [finish.rename.afterStageSync, finish.afterSettlement]) := by
    have wrote : writeFreshStagedWith finish.stage.tryCreate finish.stage.detachStale finish.stage.create
        finish.stage.write finish.stage.flush stagePath layout.keeper.bytes atStage = .ok handle written :=
      finish.stage.wrote
    simp only [stageAt, stageFreshWithCache, remembered, wrote, openedCensus]
    rfl
  have consume : admission.cache.consume stagePath = admission.cache := rfl
  have persisted : finish.syncAt directory #[stagePath]
      (remembered, (beforeSync, written), [finish.rename.afterStageSync, finish.afterSettlement]) =
      .ok () (admission.cache, (afterSync, durable), [finish.afterSettlement]) := by
    have synced : finish.authorization.fsync handle written = .ok () durable := finish.rename.synced
    dsimp only [syncAt, remembered]
    rw [SyncPathGroup.run_single,
      syncRemembered (file_ne_directory directory .stagedWal) handle finish.openForSync
        finish.fsyncWithCensus ((beforeSync, written), [finish.rename.afterStageSync, finish.afterSettlement]),
      consume]
    simp only [fsyncWithCensus, synced, List.headD_cons, List.tail_cons]
    rfl
  have moved : fileAction (calls.renameFile stagePath (directory.file (.walSegment layout.keeper.first)))
      finish.settlement.afterRename (admission.cache, (afterSync, durable), [finish.afterSettlement]) =
      .ok () (admission.cache, (movedCensus, finish.settlement.files), [finish.afterSettlement]) := by
    have returned := finish.rename.reported
    dsimp only at returned
    rw [finish.settlement.completed] at returned
    change calls.renameFile stagePath (directory.file (.walSegment layout.keeper.first)) durable.image =
      .ok () finish.settlement.files.image at returned
    simp only [fileAction, returned]
    rfl
  have settled : finish.syncAt directory #[directory.path]
      (admission.cache, (movedCensus, finish.settlement.files), [finish.afterSettlement]) =
      .ok () (admission.cache, (finish.census, finish.settled), []) := by
    have effect := finish.settlement.effect
    rw [finish.completed] at effect
    have output := finish.syncDirectory (entered := movedCensus) (drops := finish.afterSettlement)
      (remaining := []) (cache := admission.cache) rfl effect
    simpa only [movedCensus, openedCensus, afterSync, DescriptorInventory.afterDrops_append, census,
      ListedLongKeeperDirectoryIssue.inventory, settled, List.append_assoc] using output
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
  change finish.repairAt directory layout.boundedPlan layout.plan.keeperBytes.size
    (admission.cache, (entered, admission.held), finish.syncDrops) = _
  unfold repairAt
  rw [finishBoundedMarkedOpen_long _ _ _ _ _ _ _ valid size long]
  simp only [later, List.map_nil, List.nil_append, List.forM_eq_forM, List.forM_cons, List.forM_nil,
    performPaths, Publication.performReplacement, bytes, keeper, Array.push_empty, Bind.bind, EStateM.bind,
    Pure.pure, EStateM.pure, first, second, stage, persisted, moved, settled, stagePath]

private noncomputable def repairFromCensus (finish : CapturedLongKeeperFinish calls report vacant selected)
    (resolved : DiskDirectory) (plan : Plan) (size : Nat) :
    EStateM IO.Error (CensusDirectoryCache × CensusOpenState) Unit := fun (cache, reached, before) =>
  match finish.repairAt resolved plan size (cache, (reached, before), finish.syncDrops) with
  | .ok () (cache, reached, _) => .ok () (cache, reached)
  | .error cause (cache, reached, _) => .error cause (cache, reached)

private noncomputable def repairAfterRead (finish : CapturedLongKeeperFinish calls report vacant selected)
    (resolved : DiskDirectory) (plan : Plan) (size : Nat) :
    EStateM IO.Error (CensusDirectoryCache × CensusOpenState) Unit := fun (cache, reached, before) =>
  finish.repairFromCensus resolved plan size (cache, reached.afterDrops [report.wal.keeper.calls.slot.closeEvent], before)

private noncomputable def readRepair (finish : CapturedLongKeeperFinish calls report vacant selected) :
    EStateM IO.Error (CensusDirectoryCache × CensusOpenState) Unit := do
  let _ ← finish.reader.readKeeper
  finish.repairAfterRead directory layout.boundedPlan layout.plan.keeperBytes.size

/-- Read and close the long keeper, then enter the shared replacement with
the resulting census. The last grouped sync returns the census of the
staged allocation and subsequent observed events. -/
theorem readRepair_returns (finish : CapturedLongKeeperFinish calls report vacant selected) :
    finish.readRepair (admission.cache, finish.reader.atOpen, admission.held) =
      .ok () (admission.cache, finish.census, finish.settled) := by
  simp only [readRepair, Bind.bind, EStateM.bind, finish.readAndClose.1, repairAfterRead, repairFromCensus,
    finish.repairAt_returns]

/-- A temporary keeper read releases its slot before returning the
selected prefix to replay. An aligned read stays in the pending cache. -/
private def readKeeperAndRelease (finish : CapturedLongKeeperFinish calls report vacant selected)
    (path : FilePath) (count physical : Nat) : EStateM IO.Error (CensusDirectoryCache × CensusOpenState) ByteArray :=
  fun initial => match finish.reader.readKeeperAt path count physical initial with
    | .error cause reached => .error cause reached
    | .ok bytes (cache, census, files) =>
      let census := if count < physical then census.afterDrops [report.wal.keeper.calls.slot.closeEvent] else census
      .ok bytes (cache, census, files)

private theorem readKeeperAndRelease_returns (finish : CapturedLongKeeperFinish calls report vacant selected) :
    finish.readKeeperAndRelease (directory.file (.walSegment layout.keeper.first)) layout.keeper.bytes.size
        report.wal.keeper.calls.metadata.byteSize.toNat (admission.cache, finish.reader.atOpen, admission.held) =
      .ok layout.keeper.bytes (admission.cache,
        finish.reader.afterRead.afterDrops [report.wal.keeper.calls.slot.closeEvent], admission.held) := by
  have read := finish.readAndClose.1
  unfold CapturedKeeperOpenReports.readKeeper at read
  simp only [readKeeperAndRelease, read, finish.longer, ↓reduceIte]

private noncomputable def finishFromCensus (finish : CapturedLongKeeperFinish calls report vacant selected)
    (prepare : EStateM IO.Error (CensusDirectoryCache × CensusOpenState) (Plan × Reopened × Nat))
    (resolved : DiskDirectory) (cache : CensusDirectoryCache) : EStateM IO.Error CensusOpenState Reopened :=
  fun initial => match prepare (cache, initial) with
    | .error cause (_, reached) => .error cause reached
    | .ok (plan, opened, size) reached =>
      match finish.repairFromCensus resolved plan size reached with
      | .ok () (_, final) => .ok opened final
      | .error cause (_, final) => .error cause final

private theorem finishFromCensus_returns (finish : CapturedLongKeeperFinish calls report vacant selected)
    {prepare : EStateM IO.Error (CensusDirectoryCache × CensusOpenState) (Plan × Reopened × Nat)} {opened : Reopened}
    (reached : prepare (admission.cache, admission.reached, admission.held) =
      .ok (layout.boundedPlan, opened, layout.plan.keeperBytes.size) (admission.cache,
        finish.reader.afterRead.afterDrops [report.wal.keeper.calls.slot.closeEvent], admission.held)) :
    finish.finishFromCensus prepare directory admission.cache (admission.reached, admission.held) =
      .ok opened (finish.census, finish.settled) := by
  simp only [finishFromCensus, reached, repairFromCensus, finish.repairAt_returns]

private noncomputable def finishAt (finish : CapturedLongKeeperFinish calls report vacant selected)
    (resolved : DiskDirectory) (_owner : DescriptorSlot) (cache : CensusDirectoryCache) (prepared : Plan × Reopened × Nat) :
    EStateM IO.Error CensusOpenState Reopened := fun (_, before) =>
  let (plan, opened, size) := prepared
  match finish.repairAfterRead resolved plan size (cache, finish.reader.afterRead, before) with
  | .ok () (_, reached) => .ok opened reached
  | .error cause (_, reached) => .error cause reached

private theorem finishAt_returns (finish : CapturedLongKeeperFinish calls report vacant selected) (opened : Reopened) :
    finish.finishAt directory admission.owner admission.cache (layout.boundedPlan, opened, layout.plan.keeperBytes.size)
      (admission.reached, admission.held) = .ok opened (finish.census, finish.settled) := by
  have repaired := finish.readRepair_returns
  simp only [readRepair, Bind.bind, EStateM.bind, finish.readAndClose.1] at repaired
  rw [finishAt, repaired]

/-- The native-shaped open with the reached long replacement callbacks.
Ready state and the two fresh reference identities are allocated only
after the final replacement barrier returns. -/
noncomputable def run (finish : CapturedLongKeeperFinish calls report vacant selected) :
    EStateM.Result IO.Error CensusOpenState SegmentedSession :=
  calls.runWithFinish report finish.finishAt

/-- Follow one admitted census through the selected reads, temporary
keeper release, replacement, and ready session installation. -/
noncomputable def runFromCensus (finish : CapturedLongKeeperFinish calls report vacant selected)
    (metadataRelease runRelease sealRelease : FilePath → List LockReferenceDrop) :
    EStateM.Result IO.Error CensusOpenState SegmentedSession :=
  calls.runWithMarked (finish.finishFromCensus
    (report.prepareFromCensus metadataRelease runRelease sealRelease finish.readKeeperAndRelease))

/-- The long replacement starts after a reported vacant admission. Its
directory barriers preserve the selected manifest and marker while the
final barrier settles the newly staged keeper. -/
theorem installsAfterVacancy (finish : CapturedLongKeeperFinish calls report vacant selected)
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
    ∃ session, finish.run = .ok session (finish.census, finish.settled) ∧
      finish.settled.image.directory.active = retry.image.directory.active ∧
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
  obtain ⟨session, returned, installed⟩ :=
    CapturedAlignedCallbacks.installsWithFinish (calls := calls) (report := report) vacant marker laterValid
      following accepted ordered selected finish.finishAt finish.finishAt_returns ready effects
  exact ⟨session, returned, safe.selected, installed⟩

/-- A chronology from the admitted files through the exact selected
checkpoint and WAL supplies the same returned table and continues into
replacement using the temporary keeper's reached close census. -/
theorem installsFromCensus (finish : CapturedLongKeeperFinish calls report vacant selected)
    {metadataRelease : FilePath → List LockReferenceDrop} {manifestDrops : List LockReferenceDrop}
    (manifest : CapturedManifestCensus report metadataRelease manifestDrops)
    (runs : CapturedRunReadCensus report (admission.reached.afterDrops manifestDrops))
    (markerRead : CapturedMarkerCensus report ((admission.reached.afterDrops manifestDrops).afterDrops
      (runReadDrops runs.events (selectedRunCount retry.image.directory.active.manifest))) metadataRelease)
    (chronology : report.listing.beforeOpen = manifestDrops ++
      runReadDrops runs.events (selectedRunCount retry.image.directory.active.manifest) ++
      (markerRead.custody.beforeOpen ++ metadataRelease (directory.file .walBoundary)))
    {released : FilePath → List LockReferenceDrop} {required : List (Nat × IO.FS.Metadata)}
    (seals : CapturedSealReadChain report released required report.listing.afterClose finish.reader.beforeOpen)
    (offsets : required.map Prod.fst = (layout.sealed ++ [layout.keeper]).map WalSegment.first)
    (retained : ∀ event ∈ finish.reader.beforeOpen,
      event.removes admission.owner.reference = false ∧ event.removes admission.cached.reference = false)
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
    ∃ session, finish.runFromCensus metadataRelease runs.released released = .ok session (finish.census, finish.settled) ∧
      finish.settled.image.directory.active = retry.image.directory.active ∧
      admission.owner ∈ finish.census.slots ∧ admission.cached ∈ finish.census.slots ∧
      CachedRetryInstalled (before := retry) report.walReads admission.reached admission.owner report.bindings
        published calls.liveRefs (.ok session finish.settled) := by
  obtain ⟨opened, reached, projected⟩ := report.preparesFromCensus manifest runs selected markerRead chronology
    finish.reader seals offsets retained following laterValid accepted ordered finish.readKeeperAndRelease
    finish.readKeeperAndRelease_returns
  have same : finish.runFromCensus metadataRelease runs.released released = finish.run := by
    unfold runFromCensus run
    apply calls.runWithMarked_eq report _ finish.finishAt marker
    simp only [finish.finishFromCensus_returns reached, Bind.bind, EStateM.bind, projected, finish.finishAt_returns]
  rw [same]
  obtain ⟨session, returned, pair, installed⟩ := finish.installsAfterVacancy marker keeperValid laterValid following accepted ordered
  exact ⟨session, returned, pair, finish.lockRetained, finish.directoryRetained, installed⟩

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
    finish.reader.afterRead.afterDrops [report.wal.keeper.calls.slot.closeEvent] =
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
  obtain ⟨prefixReached, _, _, _, _, oldObject, _, _⟩ :=
    trace.capturesAfterAdmission earlier last admission distinct distinctCached lockObject (calls.recoverWithFinish report finish.finishAt)
  have sameLock := report.sameObjects.2.1.trans (congrArg some oldObject)
  obtain ⟨session, returned, _, installed⟩ := finish.installsAfterVacancy marker keeperValid laterValid following accepted ordered
  exact ⟨prefixReached, sameLock, finish.readAndClose.1, finish.readAndClose.2, finish.lockRetained,
    finish.directoryRetained, finish.sameCensusObjects, finish.settlement.settledInode.1,
    finish.settlement.toListedLongKeeperDirectoryIssue.projectsStoppedInodes true,
    report.chunkReads, session, returned, installed⟩

end CapturedLongKeeperFinish

end Alvoki.Storage.DiskSession
