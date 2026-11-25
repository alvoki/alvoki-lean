import Alvoki.Storage.Disk.NativeLongKeeperReadHeap
import Alvoki.Storage.Disk.StagingFile

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

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

private abbrev Remove := FilePath → EStateM IO.Error heap (Except IO.Error Unit)

/-- Reuse the checked ordered unlink callbacks, with an empty pass
when the selected longer-keeper report has no later names. -/
def NativeLongKeeperUnlinks (finish : CapturedLongKeeperFinish calls reads vacant selected)
    (seed : OpenSyncCacheAllocations admission.opened view init entry)
    (remove : @Remove heap) (before after : heap) : Prop :=
  match finish.prune with
  | .empty _ => after = before
  | .listed prune _ _ =>
    PrunedWalUnlinkHeaps view seed.directoryRef seed.activeRef seed.pendingRef remove prune.unlinks before after

/-- The unlink pass starts at the returned authorization heap. The
second directory fsync uses the original directory descriptor and
leaves the exact file state used for subsequent staging. -/
structure NativeLongKeeperSuffixHeap (authorization : NativeLongKeeperAuthorizationHeap read sync)
    (remove : @Remove heap) where
  unlinked : heap
  reached : heap
  unlinks : NativeLongKeeperUnlinks finish seed remove authorization.reached unlinked
  directoryHandle : view.handle unlinked seed.handle = view.handle authorization.reached seed.handle
  loaded : sync.getDirectory seed.directoryRef unlinked = .ok (some seed.handle) unlinked
  synced : sync.sync seed.handle unlinked = .ok () reached
  files : view.files reached = finish.prune.stageInput
  census : view.descriptors reached = view.descriptors unlinked
  cells : KeeperCacheCellsFrame view seed.directoryRef seed.activeRef seed.pendingRef unlinked reached
  handle : view.handle reached seed.handle = view.handle unlinked seed.handle

namespace NativeLongKeeperSuffixHeap

variable {remove : @Remove heap}

private theorem unlinksInOrder (seen : NativeLongKeeperSuffixHeap authorization remove)
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit) (rename : FilePath → FilePath → EStateM IO.Error heap Unit) :
    ((layout.boundedPlan.newer.map Step.unlink).forM (performPaths directory layout.boundedPlan remove throw write
      (sync.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef) rename)) authorization.reached =
      .ok () seen.unlinked ∧
    view.files seen.unlinked = { admission.held with image := finish.prune.afterUnlinks } ∧
    view.descriptors seen.unlinked = view.descriptors authorization.reached ∧
    KeeperCacheCellsFrame view seed.directoryRef seed.activeRef seed.pendingRef authorization.reached seen.unlinked := by
  have unlinks := seen.unlinks
  unfold NativeLongKeeperUnlinks at unlinks
  cases route : finish.prune with
  | empty report =>
    rw [route] at unlinks
    change seen.unlinked = authorization.reached at unlinks
    have suffix : layout.boundedPlan.newer = [] := report.noLater
    rw [unlinks, suffix]
    exact ⟨rfl, authorization.files, rfl, KeeperCacheCellsFrame.same⟩
  | listed report _ _ =>
    rw [route] at unlinks
    change PrunedWalUnlinkHeaps view seed.directoryRef seed.activeRef seed.pendingRef
      remove report.unlinks authorization.reached seen.unlinked at unlinks
    exact unlinks.returns admission.held authorization.files layout.boundedPlan write
      (sync.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef) rename

theorem returns (seen : NativeLongKeeperSuffixHeap authorization remove)
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit) (rename : FilePath → FilePath → EStateM IO.Error heap Unit) :
    let grouped := sync.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef
    (((layout.boundedPlan.newer.map Step.unlink) ++ [Step.syncPruned]).forM
      (performPaths directory layout.boundedPlan remove throw write grouped rename)) authorization.reached =
      .ok () seen.reached ∧ view.files seen.reached = finish.prune.stageInput ∧
    view.descriptors seen.reached = view.descriptors authorization.reached ∧
    KeeperCacheCellsFrame view seed.directoryRef seed.activeRef seed.pendingRef read.closed seen.reached ∧
    view.handle seen.reached seed.handle = (admission.reached, admission.cached, 0) := by
  intro grouped
  obtain ⟨removed, _, census, framed⟩ := seen.unlinksInOrder write rename
  have unlinked : ((layout.boundedPlan.newer.map Step.unlink).forM
      (performPaths directory layout.boundedPlan remove throw write grouped rename)) authorization.reached =
    .ok () seen.unlinked := removed
  have groupedSync : grouped #[directory.path] seen.unlinked = .ok () seen.reached :=
    sync.syncsDirectory seen.loaded seen.synced
  refine ⟨?_, seen.files, seen.census.trans census, (authorization.cells.trans framed).trans seen.cells,
    seen.handle.trans (seen.directoryHandle.trans (authorization.handle.trans read.readsAndReleases.directoryHandle))⟩
  rw [List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM]
  simp only [Bind.bind, EStateM.bind, unlinked, List.forM_eq_forM, List.forM_cons, List.forM_nil,
    performPaths, groupedSync, Pure.pure, EStateM.pure]

end NativeLongKeeperSuffixHeap

structure LongKeeperStageCallbacks (heap : Type) where
  tryCreate : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Handle)
  detachStale : FilePath → EStateM IO.Error heap Unit
  create : FilePath → EStateM IO.Error heap IO.FS.Handle
  write : IO.FS.Handle → ByteArray → EStateM IO.Error heap Unit
  flush : IO.FS.Handle → EStateM IO.Error heap Unit

noncomputable def LongKeeperStageCallbacks.stage (calls : LongKeeperStageCallbacks heap)
    (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (modifyPending : IO.Ref (List (FilePath × IO.FS.Handle)) →
      (List (FilePath × IO.FS.Handle) → List (FilePath × IO.FS.Handle)) → EStateM IO.Error heap Unit)
    (path : FilePath) (bytes : ByteArray) : EStateM IO.Error heap Unit := do
  let descriptor ← writeFreshStagedWith calls.tryCreate calls.detachStale calls.create calls.write calls.flush path bytes
  modifyPending pending (pushPending path descriptor)

variable {remove : @Remove heap} {suffix : NativeLongKeeperSuffixHeap authorization remove}

/-- A successful first exclusive create returns the descriptor subsequently
written, flushed and inserted into the original pending cell. -/
structure NativeLongKeeperFreshStageHeap (suffix : NativeLongKeeperSuffixHeap authorization remove)
    (stage : LongKeeperStageCallbacks heap) where
  descriptor : IO.FS.Handle
  created : heap
  written : heap
  flushed : heap
  recorded : heap
  fresh : stage.tryCreate (directory.file .stagedWal) suffix.reached = .ok (.ok descriptor) created
  openedSlot : (view.handle created descriptor).2.1 = finish.stage.slot
  openedCensus : view.descriptors created = finish.stage.inventory
  wrote : stage.write descriptor layout.keeper.bytes created = .ok () written
  flush : stage.flush descriptor written = .ok () flushed
  captured : view.handle flushed descriptor = (finish.stage.inventory, finish.stage.slot, finish.stage.offset)
  record : sync.modifyPending seed.pendingRef (pushPending (directory.file .stagedWal) descriptor) flushed =
    .ok () recorded
  pending : view.pending recorded seed.pendingRef =
    pushPending (directory.file .stagedWal) descriptor (view.pending suffix.reached seed.pendingRef)
  directory : view.directory recorded seed.directoryRef = view.directory suffix.reached seed.directoryRef
  active : view.active recorded seed.activeRef = view.active suffix.reached seed.activeRef
  directoryKept : view.handle recorded seed.handle = view.handle suffix.reached seed.handle
  handleKept : view.handle recorded descriptor = view.handle flushed descriptor
  fileEffect : view.files flushed =
    { finish.prune.stageInput with image := finish.prune.stageInput.image.withScratch (some (layout.keeper.bytes, false)) }
  fileFrame : view.files recorded = view.files flushed
  atSync : view.descriptors recorded = finish.stage.inventory.afterDrops finish.stage.beforeSync

namespace NativeLongKeeperFreshStageHeap

variable {stage : LongKeeperStageCallbacks heap}

theorem returns (seen : NativeLongKeeperFreshStageHeap suffix stage)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) :
    stage.stage seed.pendingRef sync.modifyPending (directory.file .stagedWal) layout.keeper.bytes suffix.reached =
      .ok () seen.recorded ∧
    view.cacheAt seen.recorded seed.directoryRef seed.activeRef seed.pendingRef =
      admission.cache.remember (directory.file .stagedWal) (finish.stage.inventory, finish.stage.slot, finish.stage.offset) ∧
    view.descriptors seen.recorded = finish.stage.inventory.afterDrops finish.stage.beforeSync ∧
    view.files seen.recorded =
      { finish.prune.stageInput with image := finish.prune.stageInput.image.withScratch (some (layout.keeper.bytes, false)) } := by
  obtain ⟨_, _, _, cells, directoryHandle⟩ := suffix.returns (stage.stage seed.pendingRef sync.modifyPending) rename
  have released := read.readsAndReleases
  refine ⟨?_, ?_, seen.atSync, seen.fileFrame.trans seen.fileEffect⟩
  · simp only [LongKeeperStageCallbacks.stage, writeFreshStagedWith, withFreshStaging, Bind.bind, EStateM.bind,
      seen.fresh, Pure.pure, EStateM.pure, seen.wrote, seen.flush, seen.record]
  · simp only [OpenCloseHeapView.cacheAt, seen.directory, cells.directory, released.frame.directoryCell,
      read.entryFrame.directoryCell, seed.directoryKept, seed.directorySet,
      seen.active, cells.active, released.frame.activeCell, read.entryFrame.activeCell, seed.activeKept, seed.activeSet,
      seen.pending, cells.pending, released.frame.pendingCell, read.entryFrame.pendingCell, seed.pendingSet,
      pushPending, seen.directoryKept, directoryHandle, Option.map_some, Option.map_none, List.map_cons, List.map_nil,
      seen.handleKept, seen.captured, CensusOpenAdmissionReports.cache, Cache.remember]

/-- The original authorization heap, ordered suffix and fresh stage
leave the bounded worker immediately before the staged-file fsync. -/
theorem reachesStageSync (seen : NativeLongKeeperFreshStageHeap suffix stage)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) :
    let write := stage.stage seed.pendingRef sync.modifyPending
    let grouped := sync.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef
    let perform := performPaths directory layout.boundedPlan remove throw write grouped rename
    finishBoundedMarkedOpen directory layout.boundedPlan reads.wal.keeper.calls.metadata.byteSize.toNat
      remove write grouped rename read.closed =
      (do
        perform (.replace .syncStaged)
        perform (.replace .renameStaged)
        perform (.replace .syncDirectory)
        pure () : EStateM IO.Error heap Unit) seen.recorded := by
  intro write grouped perform
  have first : grouped #[directory.path] read.closed = .ok () authorization.reached :=
    authorization.returns.1
  have pruned : (((layout.boundedPlan.newer.map Step.unlink) ++ [Step.syncPruned]).forM perform)
      authorization.reached = .ok () suffix.reached :=
    (suffix.returns write rename).1
  have staged := (seen.returns rename).1
  have bytes : layout.boundedPlan.keeperBytes.size = layout.boundedPlan.keeperSize := layout.target.trimmedSize
  have longer : layout.boundedPlan.keeperSize < reads.wal.keeper.calls.metadata.byteSize.toNat :=
    bytes ▸ finish.longer
  have valid : layout.boundedPlan.valid = true :=
    (Plan.valid_iff _).mpr ⟨layout.target.firstCovered, Nat.le_of_eq bytes.symm, finish.prune.later⟩
  have exactBytes : layout.boundedPlan.keeperBytes.extract 0 layout.boundedPlan.keeperSize = layout.keeper.bytes := by
    rw [← bytes, ByteArray.extract_zero_size]
    rfl
  rw [finishBoundedMarkedOpen_long _ _ _ _ _ _ _ valid bytes longer]
  change (do
    grouped #[directory.path]
    (((layout.boundedPlan.newer.map Step.unlink) ++ [Step.syncPruned]).forM perform)
    perform (.replace .writeStaged)
    perform (.replace .syncStaged)
    perform (.replace .renameStaged)
    perform (.replace .syncDirectory)
    pure () : EStateM IO.Error heap Unit) read.closed = _
  simp only [Bind.bind, EStateM.bind, first, pruned]
  have wrote : perform (.replace .writeStaged) suffix.reached = .ok () seen.recorded := by
    simp only [perform, performPaths, Publication.performReplacement, exactBytes, write]
    exact staged
  simp only [wrote]

end NativeLongKeeperFreshStageHeap

end Alvoki.Storage.DiskSession
