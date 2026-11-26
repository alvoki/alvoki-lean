import Alvoki.Storage.Disk.NativeAlignedKeeperCache
import Alvoki.Storage.Disk.CapturedPrunedAlignedInstallation

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
  {checkpoint : Option (PackedTable × UInt64)}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {vacant : TryLockObserves retry.owners directory (.ok true)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {calls : CapturedAlignedCallbacks admission} {reads : CapturedMarkedReadReports admission layout published}
  {heap : Type}

/- The three cells are unchanged across a directory fsync or unlink. The
file and descriptor effects are observed at those boundaries separately. -/
structure KeeperCacheCellsFrame (view : OpenCloseHeapView heap FileImage)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (before after : heap) : Prop where
  directory : view.directory after cached = view.directory before cached
  active : view.active after active = view.active before active
  pending : view.pending after pending = view.pending before pending

namespace KeeperCacheCellsFrame

variable {view : OpenCloseHeapView heap FileImage} {cached active pending} {before middle after : heap}

theorem same : KeeperCacheCellsFrame view cached active pending before before := ⟨rfl, rfl, rfl⟩

theorem trans (first : KeeperCacheCellsFrame view cached active pending before middle)
    (last : KeeperCacheCellsFrame view cached active pending middle after) :
    KeeperCacheCellsFrame view cached active pending before after :=
  ⟨last.directory.trans first.directory, last.active.trans first.active, last.pending.trans first.pending⟩

end KeeperCacheCellsFrame

variable {operations : MarkedRetryChunkOperations CensusDirectoryCache directory layout}
  {held : HeldDirectoryMarkedRetryReports operations published}

/-- Each actual raw callback is paired with the same accepted unlink
from the held namespace report. The next call starts from that heap. -/
inductive PrunedWalUnlinkHeaps (view : OpenCloseHeapView heap FileImage)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)) :
    {initial : FileImage} → {bindings : FilePath → Option Nat} → {names : List Nat} →
      {final : FilePath → Option Nat} → HeldLaterWalUnlinks held initial bindings names final →
      heap → heap → Prop where
  | done : PrunedWalUnlinkHeaps view cached active pending remove (.done (initial := initial) (bindings := bindings))
      before before
  | step (head : HeldLaterWalUnlink held first initial bindings reached)
      (tail : HeldLaterWalUnlinks held (initial.unlinkLater first) reached names final)
      (raw : remove (directory.file (.walSegment first)) before = .ok head.raw next)
      (effect : view.files next = { view.files before with image := initial.unlinkLater first })
      (slots : view.descriptors next = view.descriptors before)
      (cells : KeeperCacheCellsFrame view cached active pending before next)
      (rest : PrunedWalUnlinkHeaps view cached active pending remove tail next after) :
      PrunedWalUnlinkHeaps view cached active pending remove (.step head tail) before after

namespace PrunedWalUnlinkHeaps

variable {view : OpenCloseHeapView heap FileImage} {cached active pending}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)}
  {initial : FileImage} {bindings final : FilePath → Option Nat} {names : List Nat}
  {unlinks : HeldLaterWalUnlinks held initial bindings names final} {before after : heap}

theorem returns (seen : PrunedWalUnlinkHeaps view cached active pending remove unlinks before after)
    (files : LockedFileState FileImage) (entered : view.files before = { files with image := initial })
    (plan : Plan) (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit) (rename : FilePath → FilePath → EStateM IO.Error heap Unit) :
    ((names.map Step.unlink).forM (performPaths directory plan remove throw write sync rename)) before =
      .ok () after ∧ view.files after = { files with image := names.foldl FileImage.unlinkLater initial } ∧
      view.descriptors after = view.descriptors before ∧ KeeperCacheCellsFrame view cached active pending before after := by
  induction seen with
  | done => exact ⟨rfl, entered, rfl, KeeperCacheCellsFrame.same⟩
  | step head _ raw effect slots cells _ earlier =>
    have atNext := by simpa only [entered] using effect
    obtain ⟨returned, reached, inventory, kept⟩ := earlier atNext
    refine ⟨?_, reached, inventory.trans slots, cells.trans kept⟩
    simpa only [List.map_cons, List.forM_eq_forM, List.forM_cons, Bind.bind, EStateM.bind,
      Pure.pure, EStateM.pure, performPaths, RunCollection.performPaths, raw, head.accepted] using returned

end PrunedWalUnlinkHeaps

private def keeperPath (directory : DiskDirectory) (first : Nat) : FilePath :=
  directory.file (.walSegment first)

/-- The aligned keeper remains in the original pending cell throughout
authorization, the checked ordered unlinks and suffix sync. The final
keeper sync uses that same descriptor after consuming its pending entry. -/
structure PrunedAlignedKeeperCacheReport
    (finish : CapturedPrunedAlignedFinish calls reads vacant selected)
    (view : OpenCloseHeapView heap FileImage) (init : OpenSyncCacheCallbacks heap) (cacheEntry : heap)
    (seed : OpenSyncCacheAllocations admission.opened view init cacheEntry)
    (callbacks : AlignedKeeperCacheCallbacks heap)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)) (entry : heap) where
  keeper : IO.FS.Handle
  opened : heap
  read : heap
  remembered : heap
  authorized : heap
  pruned : heap
  suffixSettled : heap
  consumed : heap
  reached : heap
  entryCells : KeeperCacheCellsFrame view seed.directoryRef seed.activeRef seed.pendingRef seed.afterPending entry
  entryFiles : view.files entry = admission.held
  entryCensus : view.descriptors entry = finish.reader.atOpen
  rawOpen : callbacks.openRead (keeperPath directory layout.keeper.first) entry = .ok keeper opened
  rawKeeper : view.handle opened keeper = (reads.wal.keeper.calls.inventory, reads.wal.keeper.calls.slot, 0)
  openedCensus : view.descriptors opened = reads.wal.keeper.calls.inventory
  rawRead : readExactPrefixWith (IO.userError "short or oversized WAL keeper read") (callbacks.readChunk keeper)
    layout.keeper.bytes.size ByteArray.empty opened = .ok layout.keeper.bytes read
  readFiles : view.files read = admission.held
  readCensus : view.descriptors read = finish.reader.afterRead
  rawRemember : callbacks.modifyPending seed.pendingRef (pushPending (keeperPath directory layout.keeper.first) keeper)
    read = .ok () remembered
  rememberFrame : view.files remembered = view.files read ∧ view.descriptors remembered = view.descriptors read
  rememberedPending : view.pending remembered seed.pendingRef = [(keeperPath directory layout.keeper.first, keeper)]
  authorizationLoad : callbacks.getDirectory seed.directoryRef remembered = .ok (some seed.handle) remembered
  authorizationHandle : view.handle remembered seed.handle = (admission.reached, admission.cached, 0)
  authorizationSync : callbacks.sync seed.handle remembered = .ok () authorized
  authorizedFiles : view.files authorized = { admission.held with image := retry.image.syncDirectory }
  authorizedCensus : view.descriptors authorized = finish.reader.afterRead.afterDrops finish.prune.afterAuthorization
  authorizedCells : KeeperCacheCellsFrame view seed.directoryRef seed.activeRef seed.pendingRef remembered authorized
  unlinks : PrunedWalUnlinkHeaps view seed.directoryRef seed.activeRef seed.pendingRef remove
    finish.prune.unlinks authorized pruned
  suffixLoad : callbacks.getDirectory seed.directoryRef pruned = .ok (some seed.handle) pruned
  suffixHandle : view.handle pruned seed.handle = view.handle remembered seed.handle
  suffixSync : callbacks.sync seed.handle pruned = .ok () suffixSettled
  suffixFiles : view.files suffixSettled = { admission.held with image := retry.image.unlinkVisibleSuffix.syncDirectory }
  suffixCensus : view.descriptors suffixSettled =
    (finish.reader.afterRead.afterDrops finish.prune.afterAuthorization).afterDrops finish.repair.afterSuffix
  suffixCells : KeeperCacheCellsFrame view seed.directoryRef seed.activeRef seed.pendingRef pruned suffixSettled
  pendingLoad : callbacks.getPending seed.pendingRef suffixSettled =
    .ok [(keeperPath directory layout.keeper.first, keeper)] suffixSettled
  consume : callbacks.setPending seed.pendingRef [] suffixSettled = .ok () consumed
  consumeFrame : view.files consumed = view.files suffixSettled ∧ view.descriptors consumed = view.descriptors suffixSettled
  sameKeeper : view.handle consumed keeper = view.handle opened keeper
  keeperSync : callbacks.sync keeper consumed = .ok () reached
  reachedFiles : view.files reached = finish.settled
  reachedCensus : view.descriptors reached = finish.census
  directoryKept : view.directory reached seed.directoryRef = view.directory entry seed.directoryRef
  activeKept : view.active reached seed.activeRef = view.active entry seed.activeRef
  pendingConsumed : view.pending reached seed.pendingRef = []
  directoryHandleKept : view.handle reached seed.handle = view.handle remembered seed.handle

namespace PrunedAlignedKeeperCacheReport

variable {finish : CapturedPrunedAlignedFinish calls reads vacant selected}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap} {cacheEntry entry : heap}
  {seed : OpenSyncCacheAllocations admission.opened view init cacheEntry} {callbacks : AlignedKeeperCacheCallbacks heap}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)}

def schedule (_seen : PrunedAlignedKeeperCacheReport finish view init cacheEntry seed callbacks remove entry)
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) : EStateM IO.Error heap Unit :=
  let path := keeperPath directory layout.keeper.first
  let size := reads.wal.keeper.calls.metadata.byteSize.toNat
  let sync := callbacks.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef
  do
    let _ ← callbacks.readKeeper seed.pendingRef path layout.keeper.bytes.size size
    finishBoundedMarkedOpen directory layout.boundedPlan size remove write sync rename

private theorem alignedExtent (finish : CapturedPrunedAlignedFinish calls reads vacant selected) :
    layout.keeper.bytes.size = reads.wal.keeper.calls.metadata.byteSize.toNat := by
  have extent := finish.repair.aligned
  rw [finish.sameKeeper] at extent
  exact extent

/-- The raw keeper read leaves the selected bytes and remembered handle
at the same boundary as the aligned route with an empty suffix. -/
theorem readsKeeper (seen : PrunedAlignedKeeperCacheReport finish view init cacheEntry seed callbacks remove entry) :
    callbacks.readKeeper seed.pendingRef (directory.file (.walSegment layout.keeper.first))
      layout.keeper.bytes.size reads.wal.keeper.calls.metadata.byteSize.toNat entry =
      .ok layout.keeper.bytes seen.remembered := by
  rw [← alignedExtent finish]
  exact callbacks.readsAligned reads.wal.keeperFits seen.rawOpen seen.rawRead seen.rawRemember

/-- Settle the checked suffix starting at the already remembered keeper,
then use that pending entry for the last barrier. -/
theorem repairsAfterRead (seen : PrunedAlignedKeeperCacheReport finish view init cacheEntry seed callbacks remove entry)
    (later : ∀ first ∈ retry.image.later.visible, layout.range.through < first)
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) :
    finishBoundedMarkedOpen directory layout.boundedPlan reads.wal.keeper.calls.metadata.byteSize.toNat
      remove write (callbacks.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef) rename
      seen.remembered = .ok () seen.reached := by
  let path := directory.file (.walSegment layout.keeper.first)
  let sync := callbacks.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef
  have initialSync : sync #[directory.path] seen.remembered = .ok () seen.authorized :=
    callbacks.syncsDirectory seen.authorizationLoad seen.authorizationSync
  have suffixSync : sync #[directory.path] seen.pruned = .ok () seen.suffixSettled :=
    callbacks.syncsDirectory seen.suffixLoad seen.suffixSync
  have separate : path ≠ directory.path := file_ne_directory directory (.walSegment layout.keeper.first)
  have keeperSync : sync #[path] seen.suffixSettled = .ok () seen.reached :=
    callbacks.syncsPendingKeeper separate seen.pendingLoad seen.consume seen.keeperSync
  have unlinked : ((layout.boundedPlan.newer.map Step.unlink).forM
      (performPaths directory layout.boundedPlan remove throw write sync rename)) seen.authorized =
    .ok () seen.pruned :=
    (seen.unlinks.returns admission.held seen.authorizedFiles layout.boundedPlan write sync rename).1
  have bytes : layout.boundedPlan.keeperBytes.size = layout.boundedPlan.keeperSize := layout.target.trimmedSize
  have sizeEq := (alignedExtent finish).symm.trans bytes
  have valid := layout.boundedPlan_valid later
  have suffix : layout.boundedPlan.newer.isEmpty = false := List.isEmpty_eq_false_iff.mpr finish.repair.nonempty
  change finishBoundedMarkedOpen directory layout.boundedPlan reads.wal.keeper.calls.metadata.byteSize.toNat
      remove write sync rename seen.remembered = _
  simp only [finishBoundedMarkedOpen, valid, bytes, sizeEq, beq_self_eq_true,
    decide_eq_true (Nat.le_refl _), Bool.and_self, ↓reduceIte, suffix, Bool.false_and, Bool.false_eq_true,
    Nat.lt_irrefl, decide_false, runRepairPlan, steps, List.append_assoc, Bind.bind, EStateM.bind, initialSync]
  rw [List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM]
  change ((layout.boundedPlan.newer.map Step.unlink).forM
      (performPaths directory layout.boundedPlan remove throw write sync rename) >>= fun _ =>
    ([Step.syncPruned] ++ [Step.syncKeeper]).forM
      (performPaths directory layout.boundedPlan remove throw write sync rename)) seen.authorized = _
  simp only [Bind.bind, EStateM.bind, unlinked, List.cons_append, List.nil_append, List.forM_eq_forM,
    List.forM_cons, List.forM_nil, performPaths, suffixSync,
    show directory.file (.walSegment layout.boundedPlan.keeper) = path from rfl, keeperSync, Pure.pure, EStateM.pure]

structure Reached (seen : PrunedAlignedKeeperCacheReport finish view init cacheEntry seed callbacks remove entry)
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) : Prop where
  ran : seen.schedule write rename entry = .ok () seen.reached
  prunedFiles : view.files seen.pruned = { admission.held with image := retry.image.unlinkVisibleSuffix }
  prunedCensus : view.descriptors seen.pruned =
    finish.reader.afterRead.afterDrops finish.prune.afterAuthorization
  prunedPending : view.pending seen.pruned seed.pendingRef = [(keeperPath directory layout.keeper.first, seen.keeper)]
  removed : ∀ first ∈ retry.image.later.visible, finish.prune.reached (directory.file (.walSegment first)) = none
  directoryAtSuffix : view.handle seen.pruned seed.handle = (admission.reached, admission.cached, 0)
  settledPending : view.pending seen.suffixSettled seed.pendingRef = [(keeperPath directory layout.keeper.first, seen.keeper)]
  keeperAtSync : view.handle seen.consumed seen.keeper = (reads.wal.keeper.calls.inventory, reads.wal.keeper.calls.slot, 0)
  filesAtSync : view.files seen.consumed = { admission.held with image := retry.image.unlinkVisibleSuffix.syncDirectory }
  keeperLive : reads.wal.keeper.calls.slot ∈ (view.descriptors seen.consumed).slots
  ownerLive : admission.owner ∈ (view.descriptors seen.consumed).slots
  keeperBound : finish.prune.reached (keeperPath directory layout.keeper.first) =
    some ((view.descriptors seen.consumed).inode reads.wal.keeper.calls.slot.description)
  keeperReleased : (view.descriptors seen.reached).references reads.wal.keeper.calls.slot.description = []
  final : (view.cacheAt seen.reached seed.directoryRef seed.activeRef seed.pendingRef,
    view.descriptors seen.reached, view.files seen.reached) = (admission.cache, finish.census, finish.settled)

/-- Follow the same cache through the entire bounded prune schedule.
The checked later names are absent after the unlink pass, the keeper is
still pending at that point, and the final census has released it. -/
theorem returns (seen : PrunedAlignedKeeperCacheReport finish view init cacheEntry seed callbacks remove entry)
    (later : ∀ first ∈ retry.image.later.visible, layout.range.through < first)
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) : seen.Reached write rename := by
  let sync := callbacks.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef
  obtain ⟨_, unlinkedFiles, unlinkedCensus, unlinkedCells⟩ :=
    seen.unlinks.returns admission.held seen.authorizedFiles layout.boundedPlan write sync rename
  have pending := (seen.authorizedCells.trans unlinkedCells).pending.trans seen.rememberedPending
  have custody := finish.keeperAtSync later
  have consumedSlots := seen.consumeFrame.2.trans seen.suffixCensus
  rw [DescriptorInventory.afterDrops_append] at consumedSlots
  rw [← consumedSlots] at custody
  refine {
    ran := ?_
    prunedFiles := unlinkedFiles
    prunedCensus := unlinkedCensus.trans seen.authorizedCensus
    prunedPending := pending
    removed := (finish.prune.selectedBindings later).1
    directoryAtSuffix := seen.suffixHandle.trans seen.authorizationHandle
    settledPending := seen.suffixCells.pending.trans pending
    keeperAtSync := seen.sameKeeper.trans seen.rawKeeper
    filesAtSync := seen.consumeFrame.1.trans seen.suffixFiles
    keeperLive := custody.1
    ownerLive := custody.2.1
    keeperBound := custody.2.2
    keeperReleased := seen.reachedCensus.symm ▸ finish.keeperReleased
    final := ?_ }
  · simpa only [schedule, keeperPath, Bind.bind, EStateM.bind, seen.readsKeeper] using
      seen.repairsAfterRead later write rename
  · simp only [OpenCloseHeapView.cacheAt, seen.directoryKept, seen.entryCells.directory, seed.directoryKept,
      seed.directorySet, seen.activeKept, seen.entryCells.active, seed.activeKept, seed.activeSet,
      seen.pendingConsumed, Option.map_some, Option.map_none, List.map_nil, seen.directoryHandleKept,
      seen.authorizationHandle, seen.reachedFiles, seen.reachedCensus, CensusOpenAdmissionReports.cache]

end PrunedAlignedKeeperCacheReport

end Alvoki.Storage.DiskSession
