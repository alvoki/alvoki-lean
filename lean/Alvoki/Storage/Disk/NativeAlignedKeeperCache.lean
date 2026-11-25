import Alvoki.Storage.Disk.NativeOpenCacheReferences
import Alvoki.Storage.Disk.CapturedAlignedInstallation

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

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
  · unfold schedule
    let path := keeperPath directory layout.keeper.first
    let size := reads.wal.keeper.calls.metadata.byteSize.toNat
    let sync := callbacks.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef
    change (do
      let _ ← callbacks.readKeeper seed.pendingRef path layout.keeper.bytes.size size
      finishBoundedMarkedOpen directory layout.boundedPlan size remove write sync rename :
      EStateM IO.Error heap Unit) entry = _
    have aligned : layout.keeper.bytes.size = size := by
      have exactSize := finish.repair.aligned
      rw [finish.sameKeeper] at exactSize
      exact exactSize
    have fits := reads.wal.keeperFits
    have bytes : layout.boundedPlan.keeperBytes.size = layout.boundedPlan.keeperSize := layout.target.trimmedSize
    have sizeEq : size = layout.boundedPlan.keeperSize := aligned.symm.trans bytes
    have noLater : layout.boundedPlan.newer = [] := finish.repair.noLater
    have valid : layout.boundedPlan.valid = true :=
      (Plan.valid_iff _).mpr ⟨layout.target.firstCovered, Nat.le_of_eq bytes.symm, by simp [noLater]⟩
    have separate : path ≠ directory.path := file_ne_directory directory (.walSegment layout.keeper.first)
    have directorySelected : sync #[directory.path] seen.remembered = .ok () seen.authorized :=
      callbacks.syncsDirectory seen.directoryLoad seen.directorySync
    have selectedKeeper : sync #[path] seen.authorized = .ok () seen.reached :=
      callbacks.syncsPendingKeeper separate seen.pendingLoad seen.consume seen.keeperSync
    have readReturned : callbacks.readKeeper seed.pendingRef path layout.keeper.bytes.size size entry =
        .ok layout.keeper.bytes seen.remembered := by
      rw [← aligned]
      exact callbacks.readsAligned fits seen.rawOpen seen.rawRead seen.rawRemember
    simp only [Bind.bind, EStateM.bind, readReturned]
    simp only [finishBoundedMarkedOpen, sizeEq, valid, bytes, Bind.bind, EStateM.bind,
      beq_self_eq_true, decide_eq_true (Nat.le_refl _), Bool.and_self, ↓reduceIte, noLater, List.isEmpty_nil,
      directorySelected]
    exact selectedKeeper
  · simp only [OpenCloseHeapView.cacheAt, seen.directoryKept, seen.entryDirectory,
      seed.directoryKept, seed.directorySet, seen.activeKept, seen.entryActive, seed.activeKept, seed.activeSet,
      seen.pendingConsumed, Option.map_some, Option.map_none, List.map_nil, seen.directoryHandleKept, seen.sameDirectory,
      seen.reachedFiles, seen.reachedCensus, CensusOpenAdmissionReports.cache]

end Alvoki.Storage.DiskSession
