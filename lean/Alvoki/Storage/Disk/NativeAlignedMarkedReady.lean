import Alvoki.Storage.Disk.NativeAlignedKeeperStorage
import Alvoki.Storage.Disk.NativeSelectedWriteReopen

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

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
      (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      execute makeCache = .ok handle.table start.reached ∧
      start.current.history = history ∧ start.current.submissions = log ∧ start.current.ready.reads = reads ∧
      handle.lock = raw.raw.lock ∧ handle.files.UsesCacheReferences raw.seed.activeRef raw.seed.pendingRef
        raw.seed.directoryRef ∧ handle.files.AtDirectory (dir).path ∧ handle.get = get ∧ handle.set = set ∧
      view.descriptors start.reached = start.current.ready.state.census ∧
      view.cacheAt start.reached raw.seed.directoryRef raw.seed.activeRef raw.seed.pendingRef = start.current.ready.state.cache ∧
      start.current.ready.state.cache = opening.admission.cache ∧
      start.current.ready.state.session.directory = dir ∧ start.current.ready.state.directorySlot = opening.admission.cached ∧
      (∀ literal, view.directory start.reached raw.seed.directoryRef = some literal →
        (observe start.reached).files.names start.current.ready.state.session.directory.path =
          some ((view.handle start.reached literal).1.inode (view.handle start.reached literal).2.1.description)) ∧
      NativeReadyStorage start.current.ready.state (observe start.reached) ∧
      ∀ inode, (observe start.reached).files.names (start.current.ready.state.session.directory.file
        (.walSegment start.current.ready.state.writer.wal.active.first)) = some inode →
        visible start.reached inode = start.current.ready.state.writer.wal.active.bytes

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
  refine ⟨makeCache, handle, start, ran, ?_, ?_, ?_, lock, refs, atDirectory, sameGet, sameSet,
    census.trans (congrArg NativeReadyState.census returnedState.symm),
    cache.trans (congrArg NativeReadyState.cache returnedState.symm), ?_, ?_, ?_, ?_, ?_⟩
  · rw [position]
  · rw [position]
  · rw [position]
    exact recorded
  · rw [returnedState]
    exact capturedCache
  · rw [returnedState]
    exact directory
  · rw [returnedState]
    exact slot
  · intro literal found
    rw [returnedState]
    have physical : NativeReadyStorage next.state (observe start.reached) := reached.symm ▸ final.1
    exact physical.bindsOpenCacheDirectory view cache (by rw [capturedCache, slot]; rfl)
      (sameObjects.symm.trans (congrArg DescriptorInventory.inode modeledCensus).symm) found
  · rw [returnedState, reached]
    exact final

/-- The selected aligned repair supplies physical readiness to the very
writer installed by the original successful open. The two reference
allocations carry it to that call's returned heap. -/
theorem RawHealthyMarkedOpenEffects.SelectedReturn.readyAfterAlignedRepair
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
    (before : ∀ next : NativeReadPosition history log,
      next.state.session.directory = dir → next.state.census = finish.census →
      next.state.owner = opening.admission.owner → next.state.directorySlot = opening.admission.cached →
      next.state.writer.target = layout.target → next.state.files.image.kept = retry.image.kept →
      next.state.writer.published.durable = prior.writer.published.durable →
      NativeReadyProtectedStorage next.state (observe seen.remembered).files ∧
      ∀ path, path = (dir).file .walBoundary ∨ next.state.writeFramePath path →
        (observe seen.consumed).files.names path ≠
          some (opening.reads.wal.keeper.calls.inventory.inode opening.reads.wal.keeper.calls.slot.description))
    (marker : (observe seen.remembered).files.Stored ((dir).file .walBoundary)
      (WAL.Boundary.encode (WAL.encode history).size.toUInt64))
    (rootSettled : ∀ names ∈ (observe seen.remembered).crashNames,
      names (dir).path = (observe seen.remembered).files.names (dir).path)
    (effects : ∀ state : NativeReadyState, state.session.directory = dir → seen.StorageEffects observe visible state)
    (keeperLive : visible seen.consumed
      (opening.reads.wal.keeper.calls.inventory.inode opening.reads.wal.keeper.calls.slot.description) = layout.keeper.bytes)
    (phaseFrames : ∀ (state : NativeReadyState) ref reached,
      allocatePhase (.ready state.writer.installed) raw.repaired = .ok ref reached →
      (observe raw.repaired).Frames state.crashPath (observe reached) ∧ visible reached = visible raw.repaired)
    (tokenFrames : ∀ (state : NativeReadyState) before ref reached,
      allocateToken () before = .ok ref reached →
      (observe before).Frames state.crashPath (observe reached) ∧ visible reached = visible before) :
    raw.ReadyWriterReturn log reads execute get set observe visible := by
  have alignedFinish : opening.finish = .aligned finish := congrArg Sigma.fst aligned
  have repairHeap : raw.repaired = seen.reached := congrArg (fun route => route.2.1) aligned
  refine returned.readyAfterRepair observe visible ?_ ?_ phaseFrames tokenFrames
  · simpa only [alignedFinish, CapturedKeeperFinish.census] using finish.sameCensusObjects
  · intro next directory modeledCensus owner slot target kept durable first bytes
    have chosenCensus : next.state.census = finish.census := by
      simpa only [alignedFinish, CapturedKeeperFinish.census] using modeledCensus
    obtain ⟨protectedFiles, apart⟩ := before next directory chosenCensus owner slot target kept durable
    have exactHistory := next.readPrefix.refines.2.1
    obtain ⟨_, ready, issuedKeeper⟩ := seen.readyStorage observe visible directory chosenCensus slot first bytes protectedFiles
      (by simpa only [directory, exactHistory] using marker)
      (by simpa only [directory] using rootSettled)
      (effects next.state directory) keeperLive
      (by simpa only [directory] using apart)
    exact ⟨repairHeap.symm ▸ ready, repairHeap.symm ▸ issuedKeeper⟩

end Alvoki.Storage.DiskSession
