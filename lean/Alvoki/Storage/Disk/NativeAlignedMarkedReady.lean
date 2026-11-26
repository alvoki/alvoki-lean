import Alvoki.Storage.Disk.NativeAlignedKeeperStorage
import Alvoki.Storage.Disk.NativeSelectedWriteReopen
import Alvoki.Storage.Disk.NativeRetainedOpenStorage
import Alvoki.Storage.Disk.NativeReadyWriteStorage
import Alvoki.Storage.Disk.NativeMarkedKeeperLinks
import Alvoki.Storage.Disk.NativeMarkedScanFrame
import Alvoki.Storage.Disk.NativeOpenAdmissionStorage

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair CheckpointPublication

variable {heap stream : Type} {prior : NativeReadyState} {input : FilePath}
  {inventory : DescriptorInventory} {retry : LockedFileState FileImage}
  {vacant : TryLockObserves retry.owners prior.session.directory (.ok true)}
  {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {selected : SelectedIntegrityCheckpoint prior.writer.published.durable
    retry.image.directory.active.manifest prior.writer.checkpoint}
  {opening : MarkedReadyOpenObservations input prior.session.directory inventory retry layout
    prior.writer.published vacant selected}
  {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
  {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)} {stage : LongKeeperStageCallbacks heap}
  {rename : FilePath → FilePath → EStateM IO.Error heap Unit}

local notation "dir" => prior.session.directory

/-- An actual returned writer with the physical storage and cache identity
needed at its next append. -/
def RawHealthyMarkedOpenEffects.ReadyWriterReturn
    (raw : RawHealthyMarkedOpenEffects opening view calls init entry phaseIdentity tokenIdentity
      allocatePhase allocateToken stream remove stage rename)
    (log : List DatabaseSubmissions) (reads : List RecordedSnapshotRead)
    (execute : (IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles) → EStateM.Result IO.Error heap DiskTable)
    (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
    (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray) : Prop :=
    ∃ (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
      (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle)
      (cache : OpenSyncCacheRefs handle.files start.current.ready.state.session.directory.path),
      execute makeCache = .ok handle.table start.reached ∧
      start.current.history = history ∧ start.current.submissions = log ∧ start.current.ready.reads = reads ∧
      handle.lock = raw.raw.lock ∧ handle.get = get ∧ handle.set = set ∧
      cache.directory = raw.seed.directoryRef ∧ cache.active = raw.seed.activeRef ∧ cache.pending = raw.seed.pendingRef ∧
      start.current.ready.state.cache = opening.admission.cache ∧
      start.current.ready.state.session.directory = dir ∧ start.current.ready.state.directorySlot = opening.admission.cached ∧
      start.WriteStorageEntry view cache (observe start.reached) (visible start.reached)

/-- Physical facts for the selected writer arise at the actual repair heap.
The same installation transports them through both reference allocations. -/
theorem RawHealthyMarkedOpenEffects.SelectedReturn.readyAfterRepair
    {raw : RawHealthyMarkedOpenEffects opening view calls init entry phaseIdentity tokenIdentity
      allocatePhase allocateToken stream remove stage rename}
    {log : List DatabaseSubmissions} {reads : List RecordedSnapshotRead}
    {execute : (IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles) → EStateM.Result IO.Error heap DiskTable}
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    {ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool}
    (returned : raw.SelectedReturn log reads execute get set ptrEq)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (sameObjects : opening.finish.census.inode = opening.admission.reached.inode)
    (atRepair : ∀ next : NativeReadPosition history log,
      next.state.session.directory = dir → next.state.census = opening.finish.census →
      next.state.owner = opening.admission.owner → next.state.directorySlot = opening.admission.cached →
      next.state.writer.target = layout.target → next.state.files.image.kept = retry.image.kept →
      next.state.writer.published.durable = prior.writer.published.durable →
      next.state.writer.wal.active.first = layout.keeper.first → next.state.writer.wal.active.bytes = layout.keeper.bytes →
      NativeReadyStorage next.state (observe raw.repaired) ∧
      ∀ inode, (observe raw.repaired).files.names (next.state.session.directory.file
        (.walSegment next.state.writer.wal.active.first)) = some inode →
        visible raw.repaired inode = next.state.writer.wal.active.bytes)
    (phaseFrames : ∀ (state : NativeReadyState) ref reached,
      allocatePhase (.ready state.writer.installed) raw.repaired = .ok ref reached →
      (observe raw.repaired).Frames state.crashPath (observe reached) ∧ visible reached = visible raw.repaired)
    (tokenFrames : ∀ (state : NativeReadyState) before ref reached,
      allocateToken () before = .ok ref reached →
      (observe before).Frames state.crashPath (observe reached) ∧ visible reached = visible before) :
    raw.ReadyWriterReturn log reads execute get set observe visible := by
  obtain ⟨_, next, makeCache, handle, start, _, _, ran, position, recorded, _, target, _, _, durable,
    lock, refs, atDirectory, _, sameGet, sameSet, _, _, _, _, _, _, _, census, cache, directory, modeledCensus, owner, slot,
    capturedCache, kept, first, bytes, allocation, returnedAt⟩ := returned
  obtain ⟨ready, issuedKeeper⟩ := atRepair next directory modeledCensus owner slot target kept durable first bytes
  obtain ⟨phaseFrame, phaseKeeps⟩ := phaseFrames next.state allocation.phase allocation.afterPhase allocation.phaseAllocated
  obtain ⟨tokenFrame, tokenKeeps⟩ :=
    tokenFrames next.state allocation.afterPhase allocation.token allocation.afterToken allocation.tokenAllocated
  have final := allocation.framesReadyStorage observe visible ready issuedKeeper
    phaseFrame tokenFrame (fun inode _ => congrFun phaseKeeps inode) (fun inode _ => congrFun tokenKeeps inode)
  have reached : start.reached = allocation.afterToken := congrArg (fun result => result.2.2) returnedAt
  have returnedState : start.current.ready.state = next.state := congrArg (fun position => position.ready.state) position
  have returnedDirectory : start.current.ready.state.session.directory = dir := by
    rw [returnedState]
    exact directory
  let cacheRefs : OpenSyncCacheRefs handle.files start.current.ready.state.session.directory.path :=
    ⟨raw.seed.directoryRef, raw.seed.activeRef, raw.seed.pendingRef, refs, by rw [returnedDirectory]; exact atDirectory⟩
  refine ⟨makeCache, handle, start, cacheRefs, ran, ?_, ?_, ?_, lock, sameGet, sameSet,
    rfl, rfl, rfl, ?_, returnedDirectory, ?_, ?_⟩
  · rw [position]
  · rw [position]
  · rw [position]
    exact recorded
  · rw [returnedState]
    exact capturedCache
  · rw [returnedState]
    exact slot
  · have physical : NativeReadyStorage start.current.ready.state (observe start.reached) := by
      rw [returnedState, reached]
      exact final.1
    refine ⟨census.trans (congrArg NativeReadyState.census returnedState.symm),
      cache.trans (congrArg NativeReadyState.cache returnedState.symm), physical, ?_, ?_⟩
    · rw [returnedState, reached]
      exact final.2
    · intro literal found
      rw [returnedState]
      have atStart : NativeReadyStorage next.state (observe start.reached) := reached.symm ▸ final.1
      exact atStart.bindsOpenCacheDirectory view cache (by rw [capturedCache, slot]; rfl)
        (sameObjects.symm.trans (congrArg DescriptorInventory.inode modeledCensus).symm) found

/-- Recover the selected, durable retry footprint as the physical
footprint of the actual returned writer. The remembered keeper is the
one whose committed bytes are issued to the final file sync. -/
theorem RawHealthyMarkedOpenEffects.SelectedReturn.readyAfterAlignedRetry
    {raw : RawHealthyMarkedOpenEffects opening view calls init entry phaseIdentity tokenIdentity
      allocatePhase allocateToken stream remove stage rename}
    {log : List DatabaseSubmissions} {reads : List RecordedSnapshotRead}
    {execute : (IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles) → EStateM.Result IO.Error heap DiskTable}
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    {ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool}
    (returned : raw.SelectedReturn log reads execute get set ptrEq)
    {finish : CapturedAlignedFinish opening.callbacks opening.reads vacant selected}
    (seen : AlignedKeeperCacheReport finish view init raw.raw.afterFlock raw.seed
      (raw.callbacks.withFileReads raw.fileCalls) raw.beforeKeeper)
    (aligned : (⟨opening.finish, raw.repaired, raw.keeper⟩ :
      Σ finish : CapturedKeeperFinish opening.callbacks opening.reads vacant selected, Σ reached : heap,
        NativeHealthyMarkedKeeperReport raw.seed raw.fileCalls raw.callbacks raw.beforeKeeper remove stage rename finish reached) =
      ⟨.aligned finish, seen.reached, .aligned seen⟩)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (priorReady : prior.Valid) (durable : prior.SelectedRetryDurability layout.target (observe entry))
    (kept : retry.image.kept = prior.writer.files.kept)
    (manifest : layout.target.pair.manifest = prior.writer.target.pair.manifest)
    (root : (observe entry).files.names (dir).path = some ((view.handle raw.seed.afterPending raw.seed.handle).1.inode
      (view.handle raw.seed.afterPending raw.seed.handle).2.1.description))
    (lock : (observe entry).files.names ((dir).file .lock) = some ((view.handle raw.raw.afterFlock raw.raw.lock).1.inode
      (view.handle raw.raw.afterFlock raw.raw.lock).2.1.description))
    (admissionEffects :
      let path := (dir).file (.walSegment layout.keeper.first)
      let live (atHeap : heap) : CheckpointSurvivingFiles :=
        ⟨(observe atHeap).files.names, fun inode => [visible atHeap inode]⟩
      raw.raw.CacheFrames raw.seed fun before after =>
        (observe before).Frames prior.selectedRetryPath (observe after) ∧
        (live before).Frames (· = path) (live after))
    (readEffects :
      let keeperPath := (dir).file (.walSegment layout.keeper.first)
      let frame before after :=
        MarkedOpenReadFrame dir prior.selectedRetryPath keeperPath (observe before) (observe after)
          (visible before) (visible after)
      raw.fileCalls.ScopeFrames frame ∧ raw.directoryCalls.ScopeFrames dir frame ∧
      ((raw.callbacks.withFileReads raw.fileCalls).modifyPending raw.seed.pendingRef
        (SyncHandleRouting.pushPending keeperPath seen.keeper) seen.read = .ok () seen.remembered → frame seen.read seen.remembered))
    (effects : ∀ state : NativeReadyState, state.session.directory = dir → seen.StorageEffects observe visible state)
    (keeperRead :
      let path := (dir).file (.walSegment layout.keeper.first)
      let inode := opening.reads.wal.keeper.observesFile.object
      let live (atHeap : heap) : CheckpointSurvivingFiles :=
        ⟨(observe atHeap).files.names, fun file => [visible atHeap file]⟩
      (live entry).names path = some inode ∧
      visible entry inode = layout.keeper.bytes ++ layout.tail ∧
      ((raw.callbacks.withFileReads raw.fileCalls).sync raw.seed.handle seen.remembered = .ok () seen.authorized →
        (live seen.remembered).Frames (· = path) (live seen.authorized)) ∧
      ((raw.callbacks.withFileReads raw.fileCalls).setPending raw.seed.pendingRef [] seen.authorized =
        .ok () seen.consumed → (live seen.authorized).Frames (· = path) (live seen.consumed)))
    (links : RunOpenLinkCensus (path := (dir).file (.walSegment layout.keeper.first))
      (before := raw.listing.reached) raw.fileCalls.stat (observe raw.listing.reached).files.names
      opening.reads.wal.keeper.observesFile.object)
    (phaseFrames : ∀ (state : NativeReadyState) ref reached,
      allocatePhase (.ready state.writer.installed) raw.repaired = .ok ref reached →
      (observe raw.repaired).Frames state.crashPath (observe reached) ∧ visible reached = visible raw.repaired)
    (tokenFrames : ∀ (state : NativeReadyState) before ref reached,
      allocateToken () before = .ok ref reached →
      (observe before).Frames state.crashPath (observe reached) ∧ visible reached = visible before) :
    raw.ReadyWriterReturn log reads execute get set observe visible := by
  have alignedFinish : opening.finish = .aligned finish := congrArg Sigma.fst aligned
  have sameObjects : opening.finish.census.inode = opening.admission.reached.inode := by
    simpa only [alignedFinish, CapturedKeeperFinish.census] using finish.sameCensusObjects
  let keeperPath := (dir).file (.walSegment layout.keeper.first)
  let frame before after :=
    MarkedOpenReadFrame dir prior.selectedRetryPath keeperPath (observe before) (observe after)
      (visible before) (visible after)
  obtain ⟨fileEffects, listingEffects, rememberEffect⟩ := readEffects
  obtain ⟨toListing, afterListing⟩ := raw.framesReadPrefix frame (fun _ => .refl _ _ _ _ _)
    MarkedOpenReadFrame.trans fileEffects listingEffects
  have readKeeper := seen.framesRemembered (frame := frame) (fun _ => .refl _ _ _ _ _)
    MarkedOpenReadFrame.trans
    (fun opened => by
      have effect := fileEffects.openRead keeperPath raw.beforeKeeper
      change raw.fileCalls.openRead keeperPath raw.beforeKeeper = .ok seen.keeper seen.opened at opened
      simpa only [opened, SyncHandleRouting.reachedState] using effect)
    (fileEffects.readChunk seen.keeper) rememberEffect
  obtain ⟨admission, entryKeeper⟩ := raw.raw.framesThroughCache raw.seed
    (fun first last => ⟨first.1.trans last.1, first.2.trans last.2⟩) admissionEffects
  have scans := toListing.trans afterListing
  have frames := admission.trans (scans.trans readKeeper).durable
  have afterCensus := afterListing.trans readKeeper
  obtain ⟨bound, payload, dirFrame, consumeFrame⟩ := keeperRead
  obtain ⟨nameAtRead, bytesAtRead⟩ := entryKeeper.trans scans.keeper keeperPath rfl
  have exactKeeperBytes := (List.cons.inj (bytesAtRead _ bound)).1.trans payload
  have keeperAtIssue := seen.keeperAtIssue (fun heap => (observe heap).files.names) visible
    (nameAtRead.trans bound) exactKeeperBytes readKeeper.keeper dirFrame consumeFrame
  rw [seen.keeperIssueInode, ← opening.reads.wal.keeper.observesFile.sameObject] at keeperAtIssue
  have repairHeap : raw.repaired = seen.reached := congrArg (fun route => route.2.1) aligned
  refine returned.readyAfterRepair observe visible sameObjects ?_ phaseFrames tokenFrames
  intro next directory modeledCensus owner slot target retained published first bytes
  have census : next.state.census = finish.census := by
    simpa only [alignedFinish, CapturedKeeperFinish.census] using modeledCensus
  have valid := next.readPrefix.refines.1
  obtain ⟨protectedFiles, marker, parent⟩ :=
    raw.reopenedFootprintAt observe durable frames.visible (frames.weaken fun _ same => .inr (.inl same))
      root lock sameObjects priorReady valid directory modeledCensus owner slot target manifest published (retained.trans kept)
  have apart : ∀ path, next.state.selectedRetryPath path →
      (observe seen.remembered).files.names path ≠
        some (opening.reads.wal.keeper.calls.inventory.inode opening.reads.wal.keeper.calls.slot.description) := by
    intro path selectedPath bound
    have crashPath : next.state.crashPath path := NativeReadyState.crashPath_iff_write.mpr
      (selectedPath.imp id Or.inr)
    have framedPath := NativeReadyState.crashPath_rootOrChild crashPath
    rw [directory] at framedPath
    have privateAtListing := raw.keeperPrivateBinding (names := fun heap => (observe heap).files.names) links
    have canonical := privateAtListing path ((afterCensus.names path framedPath).symm.trans
      (bound.trans (congrArg some opening.reads.wal.keeper.observesFile.sameObject)))
    exact NativeReadyState.protectedPathNeWalFromActive valid selectedPath (Nat.le_refl _)
      (by rw [directory, first]; exact canonical)
  obtain ⟨_, ready, issuedKeeper⟩ := seen.readyStorage observe visible directory census slot first bytes protectedFiles
    marker parent (effects next.state directory) keeperAtIssue apart
  exact ⟨repairHeap.symm ▸ ready, repairHeap.symm ▸ issuedKeeper⟩

end Alvoki.Storage.DiskSession
