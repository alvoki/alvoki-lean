import Alvoki.Storage.Disk.NativeOpenCacheReferences
import Alvoki.Storage.Disk.CapturedAlignedInstallation
import Alvoki.Storage.Disk.NativeRawSync

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

/-- A successful aligned finish with no later names uses exactly the
directory barrier followed by the barrier on its existing keeper. -/
theorem _root_.Alvoki.Storage.WalSegmentRepair.finishBoundedMarkedOpen_alignedSyncsReached {heap : Type}
    (directory : DiskDirectory) (plan : Plan) (physicalSize : Nat)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {entry reached : heap}
    (valid : plan.valid = true) (size : plan.keeperBytes.size = plan.keeperSize)
    (aligned : physicalSize = plan.keeperSize) (noneLater : plan.newer = [])
    (returned : finishBoundedMarkedOpen directory plan physicalSize remove write sync rename entry = .ok () reached) :
    ∃ afterDirectory, sync #[directory.path] entry = .ok () afterDirectory ∧
      sync #[directory.file (.walSegment plan.keeper)] afterDirectory = .ok () reached := by
  subst physicalSize
  simp [finishBoundedMarkedOpen, valid, size, noneLater, Bind.bind, EStateM.bind] at returned
  cases directoryBarrier : sync #[directory.path] entry with
  | error cause failed => simp [directoryBarrier] at returned
  | ok result afterDirectory =>
    cases result
    exact ⟨afterDirectory, rfl, by simpa only [directoryBarrier] using returned⟩

structure AlignedKeeperCacheCallbacks (heap : Type) where
  openRead : FilePath → EStateM IO.Error heap IO.FS.Handle
  readChunk : IO.FS.Handle → USize → EStateM IO.Error heap ByteArray
  modifyPending : IO.Ref (List (FilePath × IO.FS.Handle)) →
    (List (FilePath × IO.FS.Handle) → List (FilePath × IO.FS.Handle)) → EStateM IO.Error heap Unit
  getDirectory : IO.Ref (Option IO.FS.Handle) → EStateM IO.Error heap (Option IO.FS.Handle)
  getPending : IO.Ref (List (FilePath × IO.FS.Handle)) → EStateM IO.Error heap (List (FilePath × IO.FS.Handle))
  setPending : IO.Ref (List (FilePath × IO.FS.Handle)) → List (FilePath × IO.FS.Handle) → EStateM IO.Error heap Unit
  getActive : IO.Ref (Option (FilePath × IO.FS.Handle)) → EStateM IO.Error heap (Option (FilePath × IO.FS.Handle))
  sync : IO.FS.Handle → EStateM IO.Error heap Unit

namespace AlignedKeeperCacheCallbacks

variable {heap : Type} (calls : AlignedKeeperCacheCallbacks heap)

/-- Interpret the native keeper reader with a pending cell allocated by
the same opener. -/
def readKeeper (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (path : FilePath)
    (count size : Nat) : EStateM IO.Error heap ByteArray :=
  readKeeperWith calls.openRead
    (fun handle size => readExactPrefixWith (IO.userError "short or oversized WAL keeper read")
      (calls.readChunk handle) size ByteArray.empty)
    (fun name handle => calls.modifyPending pending (pushPending name handle)) path count size

def syncPaths (directory : FilePath) (cached : IO.Ref (Option IO.FS.Handle))
    (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (paths : Array FilePath) : EStateM IO.Error heap Unit :=
  SyncPathGroup.run (fun path => syncWithHandles directory path (calls.getDirectory cached)
    (calls.getPending pending) (calls.setPending pending) (calls.getActive active) calls.openRead calls.sync) paths

theorem readsAligned {pending path count before opened read remembered keeper bytes}
    (fits : count < USize.size)
    (openedKeeper : calls.openRead path before = .ok keeper opened)
    (readKeeper : readExactPrefixWith (IO.userError "short or oversized WAL keeper read") (calls.readChunk keeper)
      count ByteArray.empty opened = .ok bytes read)
    (rememberedKeeper : calls.modifyPending pending (pushPending path keeper) read = .ok () remembered) :
    calls.readKeeper pending path count count before = .ok bytes remembered := by
  simp [AlignedKeeperCacheCallbacks.readKeeper, readKeeperWith, Bind.bind, EStateM.bind, fits, openedKeeper,
    readKeeper, rememberedKeeper, Pure.pure, EStateM.pure]

theorem syncsDirectory {dir cached active pending before after handle}
    (loaded : calls.getDirectory cached before = .ok (some handle) before)
    (synced : calls.sync handle before = .ok () after) :
    calls.syncPaths dir cached active pending #[dir] before = .ok () after := by
  rw [syncPaths, SyncPathGroup.run_single]
  simp [syncWithHandles, Bind.bind, EStateM.bind, loaded, synced, Pure.pure, EStateM.pure]

/-- A pending keeper bypasses the active cell and any fallback open.
The removal from the pending cell precedes fsync. -/
theorem syncsPendingKeeper {dir path cached active pending before consumed after handle}
    (separate : path ≠ dir)
    (loaded : calls.getPending pending before = .ok [(path, handle)] before)
    (cleared : calls.setPending pending [] before = .ok () consumed)
    (synced : calls.sync handle consumed = .ok () after) :
    calls.syncPaths dir cached active pending #[path] before = .ok () after := by
  rw [syncPaths, SyncPathGroup.run_single]
  simp [syncWithHandles, Bind.bind, EStateM.bind, separate, loaded, cleared, synced, Pure.pure, EStateM.pure]

/-- The actual aligned finisher uses the original cached root and the
keeper surfaced by the preceding read. The root barrier frames the
pending names, and the keeper fsync follows removal of all matches. -/
theorem alignedRepairSyncs {image : Type} (view : OpenCloseHeapView heap image)
    (directory : DiskDirectory) (plan : Plan) (physicalSize : Nat)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {readHeap entry reached : heap} {root keeper : IO.FS.Handle}
    (valid : plan.valid = true) (size : plan.keeperBytes.size = plan.keeperSize)
    (aligned : physicalSize = plan.keeperSize) (noneLater : plan.newer = [])
    (cachedRoot : view.directory entry cached = some root)
    (remembered : calls.modifyPending pending (pushPending (directory.file (.walSegment plan.keeper)) keeper)
      readHeap = .ok () entry)
    (recordsKeeper : calls.modifyPending pending (pushPending (directory.file (.walSegment plan.keeper)) keeper)
      readHeap = .ok () entry →
      view.pending entry pending = pushPending (directory.file (.walSegment plan.keeper)) keeper (view.pending readHeap pending))
    (readsDirectory : ∀ {result issued}, calls.getDirectory cached entry = .ok result issued →
      result = view.directory entry cached ∧ view.pending issued pending = view.pending entry pending)
    (syncKeepsPending : ∀ {issued after}, calls.sync root issued = .ok () after →
      view.pending after pending = view.pending issued pending)
    (readsPending : ∀ {before entries loaded}, calls.getPending pending before = .ok entries loaded →
      entries = view.pending before pending)
    (returned : finishBoundedMarkedOpen directory plan physicalSize remove write
      (calls.syncPaths directory.path cached active pending) rename entry = .ok () reached) :
    let path := directory.file (.walSegment plan.keeper)
    ∃ (rootIssued afterDirectory : heap) (entries : List (FilePath × IO.FS.Handle)) (loaded consumed : heap),
      calls.getDirectory cached entry = .ok (some root) rootIssued ∧
      calls.sync root rootIssued = .ok () afterDirectory ∧
      calls.getPending pending afterDirectory = .ok entries loaded ∧
      entries.find? (fun item => item.1 == path) = some (path, keeper) ∧
      calls.setPending pending (entries.filter (fun item => item.1 != path)) loaded = .ok () consumed ∧
      calls.sync keeper consumed = .ok () reached := by
  intro path
  obtain ⟨afterDirectory, rootBarrier, keeperBarrier⟩ :=
    finishBoundedMarkedOpen_alignedSyncsReached directory plan physicalSize remove write
      (calls.syncPaths directory.path cached active pending) rename valid size aligned noneLater returned
  let syncer : RawSyncCalls heap :=
    ⟨⟨calls.getDirectory, calls.getPending, calls.setPending, calls.getActive, calls.openRead⟩, calls.sync⟩
  change syncer.group directory.path cached active pending #[directory.path] entry = .ok () afterDirectory at rootBarrier
  change syncer.group directory.path cached active pending #[path] afterDirectory = .ok () reached at keeperBarrier
  obtain ⟨directoryHandle, issued, loadedRoot, syncedRoot⟩ := syncer.rootGroupReturned rootBarrier
  obtain ⟨sameRoot, pendingFromRead⟩ := readsDirectory loadedRoot
  have sameHandle := Option.some.inj (sameRoot.trans cachedRoot)
  subst directoryHandle
  have pendingFromRemember :=
    (syncKeepsPending syncedRoot).trans (pendingFromRead.trans (recordsKeeper remembered))
  have selects {entries loaded} (read : syncer.readPending pending afterDirectory = .ok entries loaded) :
      entries.find? (fun item => item.1 == path) = some (path, keeper) := by
    rw [readsPending read, pendingFromRemember]
    simp [path, pushPending]
  obtain ⟨entries, loaded, consumed, got, chosen, removed, synced⟩ :=
    syncer.pendingGroupReturned (file_ne_directory directory (.walSegment plan.keeper)) selects keeperBarrier
  exact ⟨issued, afterDirectory, entries, loaded, consumed, loadedRoot, syncedRoot, got, chosen, removed, synced⟩

end AlignedKeeperCacheCallbacks

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
  {checkpoint : Option (PackedTable × UInt64)}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {vacant : TryLockObserves retry.owners directory (.ok true)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {calls : CapturedAlignedCallbacks admission} {reads : CapturedMarkedReadReports admission layout published}
  {heap : Type}

private def keeperPath (directory : DiskDirectory) (first : Nat) : FilePath :=
  directory.file (.walSegment first)

/-- The raw keeper callbacks use the cells from the preceding cache
allocation. Earlier checkpoint and WAL reads reach the given entry
census. The directory and keeper fsyncs carry their own file and slot
effects, including the keeper's observed drops after the second fsync. -/
structure AlignedKeeperCacheReport
    (finish : CapturedAlignedFinish calls reads vacant selected)
    (view : OpenCloseHeapView heap FileImage) (init : OpenSyncCacheCallbacks heap) (cacheEntry : heap)
    (seed : OpenSyncCacheAllocations admission.opened view init cacheEntry)
    (callbacks : AlignedKeeperCacheCallbacks heap) (entry : heap) where
  keeper : IO.FS.Handle
  opened : heap
  read : heap
  remembered : heap
  authorized : heap
  consumed : heap
  reached : heap
  entryDirectory : view.directory entry seed.directoryRef = view.directory seed.afterPending seed.directoryRef
  entryActive : view.active entry seed.activeRef = view.active seed.afterPending seed.activeRef
  entryPending : view.pending entry seed.pendingRef = view.pending seed.afterPending seed.pendingRef
  entryFiles : view.files entry = admission.held
  entryCensus : view.descriptors entry = finish.readCustody.atOpen
  rawOpen : callbacks.openRead (keeperPath directory layout.keeper.first) entry = .ok keeper opened
  rawKeeper : view.handle opened keeper = (reads.wal.keeper.calls.inventory, reads.wal.keeper.calls.slot, 0)
  openedCensus : view.descriptors opened = reads.wal.keeper.calls.inventory
  rawRead : readExactPrefixWith (IO.userError "short or oversized WAL keeper read") (callbacks.readChunk keeper)
    layout.keeper.bytes.size ByteArray.empty opened = .ok layout.keeper.bytes read
  readFiles : view.files read = admission.held
  readCensus : view.descriptors read = finish.readCustody.afterRead
  rawRemember : callbacks.modifyPending seed.pendingRef (pushPending (keeperPath directory layout.keeper.first) keeper)
    read = .ok () remembered
  rememberFrame : view.files remembered = view.files read ∧ view.descriptors remembered = view.descriptors read
  directoryLoad : callbacks.getDirectory seed.directoryRef remembered = .ok (some seed.handle) remembered
  sameDirectory : view.handle remembered seed.handle = (admission.reached, admission.cached, 0)
  directorySync : callbacks.sync seed.handle remembered = .ok () authorized
  authorizedFiles : view.files authorized = { admission.held with image := retry.image.syncDirectory }
  authorizedCensus : view.descriptors authorized = finish.readCustody.afterRead.afterDrops finish.repair.afterAuthorization
  pendingLoad : callbacks.getPending seed.pendingRef authorized =
    .ok [(keeperPath directory layout.keeper.first, keeper)] authorized
  consume : callbacks.setPending seed.pendingRef [] authorized = .ok () consumed
  consumeFrame : view.files consumed = view.files authorized ∧ view.descriptors consumed = view.descriptors authorized
  sameKeeper : view.handle consumed keeper = view.handle opened keeper
  keeperSync : callbacks.sync keeper consumed = .ok () reached
  reachedFiles : view.files reached = { admission.held with image := retry.image.syncDirectory.syncKeeper }
  reachedCensus : view.descriptors reached = finish.census
  directoryKept : view.directory reached seed.directoryRef = view.directory entry seed.directoryRef
  activeKept : view.active reached seed.activeRef = view.active entry seed.activeRef
  pendingConsumed : view.pending reached seed.pendingRef = []
  directoryHandleKept : view.handle reached seed.handle = view.handle remembered seed.handle

variable {finish : CapturedAlignedFinish calls reads vacant selected}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap} {cacheEntry entry : heap}
  {seed : OpenSyncCacheAllocations admission.opened view init cacheEntry} {callbacks : AlignedKeeperCacheCallbacks heap}

def AlignedKeeperCacheReport.schedule
    (_seen : AlignedKeeperCacheReport finish view init cacheEntry seed callbacks entry)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) : EStateM IO.Error heap Unit :=
    let path := keeperPath directory layout.keeper.first
    let size := reads.wal.keeper.calls.metadata.byteSize.toNat
    let sync := callbacks.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef
    do
      let _ ← callbacks.readKeeper seed.pendingRef path layout.keeper.bytes.size size
      finishBoundedMarkedOpen directory layout.boundedPlan size remove write sync rename

private theorem alignedExtent (finish : CapturedAlignedFinish calls reads vacant selected) :
    layout.keeper.bytes.size = reads.wal.keeper.calls.metadata.byteSize.toNat := by
  have exactSize := finish.repair.aligned
  rw [finish.sameKeeper] at exactSize
  exact exactSize

/-- The actual keeper reader returns the selected bytes at the heap
where it has just remembered the original read handle. -/
theorem AlignedKeeperCacheReport.readsKeeper
    (seen : AlignedKeeperCacheReport finish view init cacheEntry seed callbacks entry) :
    callbacks.readKeeper seed.pendingRef (directory.file (.walSegment layout.keeper.first))
      layout.keeper.bytes.size reads.wal.keeper.calls.metadata.byteSize.toNat entry =
      .ok layout.keeper.bytes seen.remembered := by
  rw [← alignedExtent finish]
  exact callbacks.readsAligned reads.wal.keeperFits seen.rawOpen seen.rawRead seen.rawRemember

/-- Both barriers start at the heap returned by the keeper reader.
The bounded finisher uses the pending handle already held there. -/
theorem AlignedKeeperCacheReport.repairsAfterRead
    (seen : AlignedKeeperCacheReport finish view init cacheEntry seed callbacks entry)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) :
    finishBoundedMarkedOpen directory layout.boundedPlan reads.wal.keeper.calls.metadata.byteSize.toNat
      remove write (callbacks.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef) rename
      seen.remembered = .ok () seen.reached := by
  let sync := callbacks.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef
  have bytes : layout.boundedPlan.keeperBytes.size = layout.boundedPlan.keeperSize := layout.target.trimmedSize
  have sizeEq := (alignedExtent finish).symm.trans bytes
  have noLater : layout.boundedPlan.newer = [] := finish.repair.noLater
  have valid : layout.boundedPlan.valid = true :=
    (Plan.valid_iff _).mpr ⟨layout.target.firstCovered, Nat.le_of_eq bytes.symm, by simp [noLater]⟩
  have separate := file_ne_directory directory (.walSegment layout.keeper.first)
  have directorySelected : sync #[directory.path] seen.remembered = .ok () seen.authorized :=
    callbacks.syncsDirectory seen.directoryLoad seen.directorySync
  have selectedKeeper : sync #[directory.file (.walSegment layout.keeper.first)] seen.authorized = .ok () seen.reached :=
    callbacks.syncsPendingKeeper separate seen.pendingLoad seen.consume seen.keeperSync
  change finishBoundedMarkedOpen directory layout.boundedPlan reads.wal.keeper.calls.metadata.byteSize.toNat
      remove write sync rename seen.remembered = _
  simp only [finishBoundedMarkedOpen, sizeEq, valid, bytes, Bind.bind, EStateM.bind,
    beq_self_eq_true, decide_eq_true (Nat.le_refl _), Bool.and_self, ↓reduceIte, noLater, List.isEmpty_nil,
    directorySelected]
  exact selectedKeeper

/-- Read the marked prefix and execute the two actual aligned barriers.
The sync of the original keeper consumes its remembered reference before
issuing fsync on that same handle. -/
theorem AlignedKeeperCacheReport.returns
    (seen : AlignedKeeperCacheReport finish view init cacheEntry seed callbacks entry)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) :
    seen.schedule remove write rename entry = .ok () seen.reached ∧
    view.handle seen.consumed seen.keeper = (reads.wal.keeper.calls.inventory, reads.wal.keeper.calls.slot, 0) ∧
    view.files seen.consumed = { admission.held with image := retry.image.syncDirectory } ∧
    view.descriptors seen.consumed = finish.readCustody.afterRead.afterDrops finish.repair.afterAuthorization ∧
    (view.cacheAt seen.reached seed.directoryRef seed.activeRef seed.pendingRef,
      view.descriptors seen.reached, view.files seen.reached) =
      (admission.cache, finish.census, { admission.held with image := retry.image.syncDirectory.syncKeeper }) := by
  refine ⟨?_, seen.sameKeeper.trans seen.rawKeeper, seen.consumeFrame.1.trans seen.authorizedFiles,
    seen.consumeFrame.2.trans seen.authorizedCensus, ?_⟩
  · simpa only [schedule, keeperPath, Bind.bind, EStateM.bind, seen.readsKeeper] using
      seen.repairsAfterRead remove write rename
  · simp only [OpenCloseHeapView.cacheAt, seen.directoryKept, seen.entryDirectory,
      seed.directoryKept, seed.directorySet, seen.activeKept, seen.entryActive, seed.activeKept, seed.activeSet,
      seen.pendingConsumed, Option.map_some, Option.map_none, List.map_nil, seen.directoryHandleKept, seen.sameDirectory,
      seen.reachedFiles, seen.reachedCensus, CensusOpenAdmissionReports.cache]

end Alvoki.Storage.DiskSession
