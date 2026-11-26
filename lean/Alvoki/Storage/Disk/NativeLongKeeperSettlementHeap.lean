import Alvoki.Storage.Disk.NativeLongKeeperSuffixStageHeap

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

/-- Project the literal longer-keeper success to the descriptor opened
for staging, its actual pending-entry fsync, the rename, and the cached
root's last barrier. Authorization and pruning retain their own heaps. -/
theorem LongKeeperStageCallbacks.finishedReplacement {heap image : Type}
    (stage : LongKeeperStageCallbacks heap) (calls : AlignedKeeperCacheCallbacks heap)
    (view : OpenCloseHeapView heap image)
    (directory : DiskDirectory) (plan : Plan) (physicalSize : Nat)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {entry reached : heap}
    (longer : plan.keeperSize < physicalSize)
    (records : ∀ {file before after},
      calls.modifyPending pending (pushPending (directory.file .stagedWal) file) before = .ok () after →
      view.pending after pending = pushPending (directory.file .stagedWal) file (view.pending before pending))
    (readsPending : ∀ {before entries loaded}, calls.getPending pending before = .ok entries loaded →
      entries = view.pending before pending)
    (readsDirectory : ∀ {before result issued}, calls.getDirectory cached before = .ok result issued →
      result = view.directory before cached)
    (returned : finishBoundedMarkedOpen directory plan physicalSize remove
      (stage.stage pending calls.modifyPending) (calls.syncPaths directory.path cached active pending) rename entry =
      .ok () reached) :
    let write := stage.stage pending calls.modifyPending
    let sync := calls.syncPaths directory.path cached active pending
    let path := directory.file .stagedWal
    let bytes := plan.keeperBytes.extract 0 plan.keeperSize
    ∃ (authorized unlinked pruned opened written flushed staged loaded consumed synced renamed rootIssued : heap)
      (file root : IO.FS.Handle) (entries : List (FilePath × IO.FS.Handle)),
      sync #[directory.path] entry = .ok () authorized ∧
      ((plan.newer.map Step.unlink).forM (performPaths directory plan remove throw write sync rename)) authorized =
        .ok () unlinked ∧
      sync #[directory.path] unlinked = .ok () pruned ∧
      stage.acquire path pruned = .ok file opened ∧
      stage.write file bytes opened = .ok () written ∧ stage.flush file written = .ok () flushed ∧
      calls.modifyPending pending (pushPending path file) flushed = .ok () staged ∧
      calls.getPending pending staged = .ok entries loaded ∧
      entries.find? (fun item => item.1 == path) = some (path, file) ∧
      calls.setPending pending (entries.filter (fun item => item.1 != path)) loaded = .ok () consumed ∧
      calls.sync file consumed = .ok () synced ∧
      rename path (directory.file (.walSegment plan.keeper)) synced = .ok () renamed ∧
      calls.getDirectory cached renamed = .ok (some root) rootIssued ∧
      view.directory renamed cached = some root ∧ calls.sync root rootIssued = .ok () reached := by
  intro write sync path bytes
  obtain ⟨authorized, unlinked, pruned, staged, synced, renamed, firstRoot, unlinks, prunedRoot,
    wroteStage, syncedStage, moved, finalRoot⟩ :=
    finishBoundedMarkedOpen_replacementReached directory plan physicalSize remove write sync rename longer returned
  obtain ⟨file, opened, written, flushed, acquired, wrote, didFlush, recorded⟩ := stage.reachedStage wroteStage
  obtain ⟨entries, loaded, consumed, got, selected, cleared, syncedFile⟩ :=
    calls.rememberedPendingReturned view (file_ne_directory directory .stagedWal)
      (records recorded) readsPending syncedStage
  let syncer : RawSyncCalls heap :=
    ⟨⟨calls.getDirectory, calls.getPending, calls.setPending, calls.getActive, calls.openRead⟩, calls.sync⟩
  obtain ⟨root, rootIssued, readRoot, syncedRoot⟩ := syncer.rootGroupReturned finalRoot
  exact ⟨authorized, unlinked, pruned, opened, written, flushed, staged, loaded, consumed, synced, renamed,
    rootIssued, file, root, entries, firstRoot, unlinks, prunedRoot, acquired, wrote, didFlush, recorded,
    got, selected, cleared, syncedFile, moved, readRoot, (readsDirectory readRoot).symm, syncedRoot⟩

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {vacant : TryLockObserves retry.owners directory (.ok true)} {checkpoint : Option (PackedTable × UInt64)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {calls : CapturedAlignedCallbacks admission} {reads : CapturedMarkedReadReports admission layout published}
  {heap : Type} {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {finish : CapturedLongKeeperFinish calls reads vacant selected}
  {seed : OpenSyncCacheAllocations admission.opened view init entry}
  {reader : MarkedTemporaryReadCalls heap} {before : heap}
  {read : NativeLongKeeperReadHeap finish seed reader before} {sync : AlignedKeeperCacheCallbacks heap}
  {authorization : NativeLongKeeperAuthorizationHeap read sync}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)}
  {suffix : NativeLongKeeperSuffixHeap authorization remove} {stage : LongKeeperStageCallbacks heap}

private def stagePath (directory : DiskDirectory) := directory.file .stagedWal

private def keeperPath (directory : DiskDirectory) (first : Nat) := directory.file (.walSegment first)

/-- The original pending cell supplies the staged descriptor. Its
entries for this pathname are removed before that descriptor is synced. -/
structure NativeLongKeeperStagedSyncHeap (staged : NativeLongKeeperFreshStageHeap suffix stage)
    (names : heap → FilePath → Option Nat) where
  consumed : heap
  reached : heap
  loaded : sync.getPending seed.pendingRef staged.recorded =
    .ok [(stagePath directory, staged.descriptor)] staged.recorded
  cleared : sync.setPending seed.pendingRef [] staged.recorded = .ok () consumed
  sameSlot : view.handle consumed staged.descriptor = view.handle staged.recorded staged.descriptor
  consumeCensus : view.descriptors consumed = view.descriptors staged.recorded
  consumeFileFrame : view.files consumed = view.files staged.recorded
  sourceAtSync : names consumed (stagePath directory) = finish.stage.bindings (stagePath directory)
  synced : sync.sync staged.descriptor consumed = .ok () reached
  census : view.descriptors reached = (view.descriptors consumed).afterDrops finish.rename.afterStageSync
  durable : view.files reached =
    { finish.prune.stageInput with image := finish.prune.stageInput.image.withScratch (some (layout.keeper.bytes, true)) }
  pending : view.pending reached seed.pendingRef = []
  directory : view.directory reached seed.directoryRef = view.directory staged.recorded seed.directoryRef
  active : view.active reached seed.activeRef = view.active staged.recorded seed.activeRef
  directoryHandle : view.handle reached seed.handle = view.handle staged.recorded seed.handle

namespace NativeLongKeeperStagedSyncHeap

variable {staged : NativeLongKeeperFreshStageHeap suffix stage} {names : heap → FilePath → Option Nat}

/-- At the staged-file barrier the selected raw handle is the same
captured live slot, bound to the staging name at issue time. -/
theorem syncs (seen : NativeLongKeeperStagedSyncHeap staged names) :
    sync.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef #[stagePath directory] staged.recorded =
      .ok () seen.reached ∧
    view.handle seen.consumed staged.descriptor = (finish.stage.inventory, finish.stage.slot, finish.stage.offset) ∧
    finish.stage.slot ∈ (view.descriptors seen.consumed).slots ∧
    names seen.consumed (stagePath directory) = some ((view.descriptors seen.consumed).inode finish.stage.slot.description) ∧
    view.descriptors seen.reached = finish.stage.inventory.afterDrops (finish.stage.beforeSync ++ finish.rename.afterStageSync) := by
  have census := seen.consumeCensus.trans staged.atSync
  refine ⟨sync.syncsPendingKeeper (file_ne_directory directory .stagedWal) seen.loaded seen.cleared seen.synced,
    seen.sameSlot.trans (staged.handleKept.trans staged.captured), census.symm ▸ finish.stage.retained, ?_, ?_⟩
  · rw [seen.sourceAtSync]
    change finish.stage.bindings (directory.file .stagedWal) = _
    rw [finish.stage.stageBound, census]
    rfl
  · rw [seen.census, census, DescriptorInventory.afterDrops_append]

end NativeLongKeeperStagedSyncHeap

variable {staged : NativeLongKeeperFreshStageHeap suffix stage} {names : heap → FilePath → Option Nat}
  {synced : NativeLongKeeperStagedSyncHeap staged names}
  {rename : FilePath → FilePath → EStateM IO.Error heap Unit}

/-- The source and destination at the reported path-based rename are
the synced staging inode and the originally selected keeper inode. -/
structure NativeLongKeeperRenameHeap (synced : NativeLongKeeperStagedSyncHeap staged names)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) where
  reached : heap
  source : names synced.reached (stagePath directory) = finish.rename.bindings (stagePath directory)
  target : names synced.reached (keeperPath directory layout.keeper.first) =
    finish.rename.bindings (keeperPath directory layout.keeper.first)
  renamed : rename (stagePath directory) (keeperPath directory layout.keeper.first) synced.reached = .ok () reached
  sourceAfter : names reached (stagePath directory) = finish.rename.renamedBindings (stagePath directory)
  targetAfter : names reached (keeperPath directory layout.keeper.first) =
    finish.rename.renamedBindings (keeperPath directory layout.keeper.first)
  files : view.files reached = finish.settlement.files
  census : view.descriptors reached = (view.descriptors synced.reached).afterDrops finish.settlement.afterRename
  cells : KeeperCacheCellsFrame view seed.directoryRef seed.activeRef seed.pendingRef synced.reached reached
  directoryHandle : view.handle reached seed.handle = view.handle synced.reached seed.handle

theorem NativeLongKeeperRenameHeap.movesStagedInode (seen : NativeLongKeeperRenameHeap synced rename) :
    names synced.reached (stagePath directory) = some (finish.stage.inventory.inode finish.stage.slot.description) ∧
    names synced.reached (keeperPath directory layout.keeper.first) = some finish.rename.original.active ∧
    names synced.reached (stagePath directory) ≠ names synced.reached (keeperPath directory layout.keeper.first) ∧
    names seen.reached (stagePath directory) = none ∧
    names seen.reached (keeperPath directory layout.keeper.first) = some (finish.stage.inventory.inode finish.stage.slot.description) ∧
    view.descriptors seen.reached = finish.settlement.inventory := by
  have distinct := finish.rename.renameTargets.2.2.2
  have effective : finish.rename.outcome.effective = true := by
    rw [finish.settlement.completed]
    rfl
  refine ⟨seen.source.trans finish.rename.sourceBound, seen.target.trans finish.rename.keeperBound,
    ?_, seen.sourceAfter.trans (finish.rename.renamedSource effective),
    seen.targetAfter.trans (finish.rename.renamedKeeper effective), ?_⟩
  · rw [seen.source, seen.target]
    exact distinct
  · rw [seen.census, synced.syncs.2.2.2.2, DescriptorInventory.afterDrops_append]
    rfl

variable {renamed : NativeLongKeeperRenameHeap synced rename}

/-- The last barrier closes publication on the same cached directory.
The file projection records its local binding durability effect and the
census records the reported drops during or after that callback. -/
structure NativeLongKeeperSettlementHeap (renamed : NativeLongKeeperRenameHeap synced rename) where
  reached : heap
  loaded : sync.getDirectory seed.directoryRef renamed.reached = .ok (some seed.handle) renamed.reached
  synced : sync.sync seed.handle renamed.reached = .ok () reached
  files : view.files reached = { view.files renamed.reached with image := (view.files renamed.reached).image.syncDirectory.syncKeeper }
  census : view.descriptors reached = (view.descriptors renamed.reached).afterDrops finish.afterSettlement
  cells : KeeperCacheCellsFrame view seed.directoryRef seed.activeRef seed.pendingRef renamed.reached reached
  directoryHandle : view.handle reached seed.handle = view.handle renamed.reached seed.handle
  stageAbsent : names reached (stagePath directory) = names renamed.reached (stagePath directory)
  keeperKept : names reached (keeperPath directory layout.keeper.first) = names renamed.reached (keeperPath directory layout.keeper.first)

namespace NativeLongKeeperSettlementHeap

structure Reached (seen : NativeLongKeeperSettlementHeap renamed) : Prop where
  ran : finishBoundedMarkedOpen directory layout.boundedPlan reads.wal.keeper.calls.metadata.byteSize.toNat
    remove (stage.stage seed.pendingRef sync.modifyPending)
    (sync.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef) rename read.closed = .ok () seen.reached
  directoryAtIssue : view.handle renamed.reached seed.handle = (admission.reached, admission.cached, 0)
  directoryLive : admission.cached ∈ (view.descriptors renamed.reached).slots
  ownerLive : admission.owner ∈ (view.descriptors renamed.reached).slots
  stageAbsent : names seen.reached (stagePath directory) = none
  keeperBound : names seen.reached (keeperPath directory layout.keeper.first) =
    some (finish.stage.inventory.inode finish.stage.slot.description)
  keeperDurable : (finish.settlement.toListedLongKeeperDirectoryIssue.stoppedInodes true).crashBytes
    (finish.stage.inventory.inode finish.stage.slot.description) = [layout.keeper.bytes]
  final : (view.cacheAt seen.reached seed.directoryRef seed.activeRef seed.pendingRef,
    view.descriptors seen.reached, view.files seen.reached) = (admission.cache, finish.census, finish.settled)

/-- The same bounded repair returns after the staged fsync, rename and
directory fsync. Its reached cache, descriptor census and file image
agree with the longer-keeper finish that supplies the replayed table. -/
theorem returns (seen : NativeLongKeeperSettlementHeap renamed) : seen.Reached := by
  let write := stage.stage seed.pendingRef sync.modifyPending
  let grouped := sync.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef
  obtain ⟨_, _, _, cells, directoryHandle⟩ := suffix.returns write rename
  have directoryAtIssue := renamed.directoryHandle.trans
    (synced.directoryHandle.trans (staged.directoryKept.trans directoryHandle))
  obtain ⟨_, _, _, stageGone, keeper, census⟩ := renamed.movesStagedInode
  have custody := finish.settlement.settlementCustody
  refine {
    ran := ?_
    directoryAtIssue := directoryAtIssue
    directoryLive := census.symm ▸ custody.1
    ownerLive := census.symm ▸ custody.2.1
    stageAbsent := seen.stageAbsent.trans stageGone
    keeperBound := seen.keeperKept.trans keeper
    keeperDurable := finish.replacementInodes.2.2.2.1
    final := ?_ }
  · change finishBoundedMarkedOpen directory layout.boundedPlan reads.wal.keeper.calls.metadata.byteSize.toNat
      remove write grouped rename read.closed = _
    rw [staged.reachesStageSync rename]
    have persisted : grouped #[stagePath directory] staged.recorded = .ok () synced.reached := synced.syncs.1
    have settled : grouped #[directory.path] renamed.reached = .ok () seen.reached :=
      sync.syncsDirectory seen.loaded seen.synced
    change (do
      grouped #[stagePath directory]
      rename (stagePath directory) (keeperPath directory layout.keeper.first)
      grouped #[directory.path]
      pure () : EStateM IO.Error heap Unit) staged.recorded = _
    simp only [Bind.bind, EStateM.bind, persisted, renamed.renamed, settled, Pure.pure, EStateM.pure]
  · have inventory := seen.census.trans (congrArg (fun census => census.afterDrops finish.afterSettlement) census)
    have files : view.files seen.reached = finish.settled := by
      rw [seen.files, renamed.files]
      rfl
    have released := read.readsAndReleases
    simp only [OpenCloseHeapView.cacheAt, seen.cells.directory, renamed.cells.directory, synced.directory,
      staged.directory, cells.directory, released.frame.directoryCell, read.entryFrame.directoryCell,
      seed.directoryKept, seed.directorySet, seen.cells.active, renamed.cells.active, synced.active,
      staged.active, cells.active, released.frame.activeCell, read.entryFrame.activeCell, seed.activeKept, seed.activeSet,
      seen.cells.pending, renamed.cells.pending, synced.pending, Option.map_some, Option.map_none, List.map_nil,
      seen.directoryHandle, directoryAtIssue, CensusOpenAdmissionReports.cache, inventory, files]
    rfl

end NativeLongKeeperSettlementHeap

end Alvoki.Storage.DiskSession
