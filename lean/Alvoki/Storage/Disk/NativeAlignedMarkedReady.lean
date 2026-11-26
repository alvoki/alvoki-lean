import Alvoki.Storage.Disk.NativeAlignedKeeperStorage
import Alvoki.Storage.Disk.NativeSelectedWriteReopen
import Alvoki.Storage.Disk.NativeRetainedOpenStorage
import Alvoki.Storage.Disk.NativeReadyWriteStorage
import Alvoki.Storage.Disk.NativeMarkedKeeperLinks
import Alvoki.Storage.Disk.NativeMarkedScanFrame
import Alvoki.Storage.Disk.NativeOpenAdmissionStorage
import Alvoki.Storage.Disk.NativeAlignedCheckpointReopenEffects

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair CheckpointPublication

section CheckpointReturn

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory}
  {history modelHistory : List WAL.Write} {log : List DatabaseSubmissions}
  {inventory : DescriptorInventory} {retry : LockedFileState FileImage}
  {layout : CanonicalKeeperLayout retry.image modelHistory} {published : Image}
  {vacant : TryLockObserves retry.owners directory (.ok true)} {checkpoint : Option (PackedTable × UInt64)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {bindings : FilePath → Option Nat}
  {opening : CheckpointBarrierAlignedReports input directory inventory retry layout published vacant selected bindings}
  {chronology : CapturedMarkedReadCensus opening.reads opening.finish.readCustody}
  {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
  {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
  {raw : RawAlignedCheckpointReopenEffects opening chronology view calls init entry phaseIdentity tokenIdentity
    allocatePhase allocateToken stream}
  {next : NativeReadPosition history log}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)}
  {write : FilePath → ByteArray → EStateM IO.Error heap Unit}
  {rename : FilePath → FilePath → EStateM IO.Error heap Unit}
  {bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened}
  {assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable}
  {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
  {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
  {ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool}

local notation "reopened" => next.state
local notation "keeperPath" => next.state.session.directory.file (DiskFile.walSegment next.state.writer.wal.active.first)
local notation "keeperInode" => opening.reads.wal.keeper.calls.inventory.inode opening.reads.wal.keeper.calls.slot.description

/-- The actual aligned syncs establish the next write entry for the selected
writer. The phase and token allocations frame those facts up to the
returned heap. All protected files refer to the selected checkpoint. -/
theorem RawAlignedCheckpointReopenEffects.ReturnedAt.writeStorageEntry
    (returned : raw.ReturnedAt next remove write rename bootstrap assemble get set ptrEq)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (sameFirst : (reopened).writer.wal.active.first = layout.keeper.first)
    (sameBytes : (reopened).writer.wal.active.bytes = layout.keeper.bytes)
    (protectedFiles : NativeReadyProtectedStorage reopened (observe raw.keeper.remembered).files)
    (marker : (observe raw.keeper.remembered).files.Stored ((reopened).session.directory.file .walBoundary)
      (WAL.Boundary.encode (WAL.encode (reopened).writer.history).size.toUInt64))
    (rootSettled : ∀ names ∈ (observe raw.keeper.remembered).crashNames,
      names (reopened).session.directory.path = (observe raw.keeper.remembered).files.names (reopened).session.directory.path)
    (effects : raw.keeper.StorageEffects observe visible reopened)
    (keeperAtIssue : (observe raw.keeper.consumed).files.names (directory.file (.walSegment layout.keeper.first)) =
      some (keeperInode) ∧ visible raw.keeper.consumed (keeperInode) = layout.keeper.bytes)
    (apart : ∀ path, path = (reopened).session.directory.file .walBoundary ∨ (reopened).writeFramePath path →
      (observe raw.keeper.remembered).files.names path ≠ some (keeperInode))
    (phaseFrames : ∀ ref after, allocatePhase (.ready (reopened).writer.installed) raw.keeper.reached = .ok ref after →
      (observe raw.keeper.reached).Frames (reopened).crashPath (observe after) ∧
      ∀ inode, (observe raw.keeper.reached).files.names (keeperPath) = some inode →
        visible after inode = visible raw.keeper.reached inode)
    (tokenFrames : ∀ before ref after, allocateToken () before = .ok ref after →
      (observe before).Frames (reopened).crashPath (observe after) ∧
      ∀ inode, (observe before).files.names (keeperPath) = some inode → visible after inode = visible before inode) :
    ∃ cache : OpenSyncCacheRefs returned.handle.files returned.start.current.ready.state.session.directory.path,
      cache.directory = raw.seed.directoryRef ∧ cache.active = raw.seed.activeRef ∧ cache.pending = raw.seed.pendingRef ∧
      returned.start.WriteStorageEntry view cache (observe returned.start.reached) (visible returned.start.reached) := by
  obtain ⟨_, settled, keeper⟩ := raw.keeper.readyStorage observe visible returned.resolvedDirectory
    returned.repairCensus returned.directorySlot sameFirst sameBytes protectedFiles marker rootSettled effects keeperAtIssue apart
  obtain ⟨allocation, sameAllocation⟩ := returned.allocation
  obtain ⟨phase, phaseKeeper⟩ := phaseFrames _ _ allocation.phaseAllocated
  obtain ⟨token, tokenKeeper⟩ := tokenFrames _ _ _ allocation.tokenAllocated
  obtain ⟨physical, bytes⟩ := allocation.framesReadyStorage observe visible settled keeper phase token phaseKeeper tokenKeeper
  have stateAtReturn := congrArg (fun position : NativeExecutionPosition => position.ready.state) returned.position
  have reached : returned.start.reached = allocation.afterToken := congrArg (fun allocated => allocated.2.2) sameAllocation
  have atPath : returned.handle.files.AtDirectory returned.start.current.ready.state.session.directory.path := by
    rw [stateAtReturn, returned.resolvedDirectory]
    exact returned.directory
  let cache : OpenSyncCacheRefs returned.handle.files returned.start.current.ready.state.session.directory.path :=
    ⟨raw.seed.directoryRef, raw.seed.activeRef, raw.seed.pendingRef, returned.references, atPath⟩
  have cached : (reopened).cache.directory = some (opening.admission.reached, (reopened).directorySlot, 0) := by
    rw [returned.capturedCache, returned.directorySlot]
    rfl
  have sameObjects := (congrArg DescriptorInventory.inode returned.repairCensus).trans opening.finish.sameCensusObjects
  refine ⟨cache, rfl, rfl, rfl, ⟨returned.census.trans (congrArg NativeReadyState.census stateAtReturn.symm),
    returned.cache.trans (congrArg NativeReadyState.cache stateAtReturn.symm), ?_, ?_, ?_⟩⟩
  · rw [stateAtReturn, reached]
    exact physical
  · rw [stateAtReturn, reached]
    exact bytes
  · intro literal found
    rw [stateAtReturn]
    exact (reached.symm ▸ physical).bindsOpenCacheDirectory view returned.cache cached sameObjects.symm found

/-- The reopened writer's own selected map determines which physical
payloads it keeps through a subsequent append. -/
theorem NativeReadyProtectedStorage.ofCheckpointSample {state : NativeReadyState}
    {files : CheckpointSurvivingFiles}
    (names : FilePath → Option Nat) (contents : Nat → ByteArray)
    (physicalFrame : (⟨names, fun inode => [contents inode]⟩ : CheckpointSurvivingFiles).Frames
      state.writeFramePath files)
    (authority : RebootDirectoryBindings state names)
    (manifest : (names (state.session.directory.file .manifest)).map contents = state.writer.target.pair.manifest)
    (sealed : ∀ segment ∈ state.writer.wal.sealed,
      (names (state.session.directory.file (.walSegment segment.first))).map contents = some segment.bytes)
    (runs : ∀ generation index, state.writer.published.durable generation index =
      (names (state.session.directory.file (.run generation index))).map contents) :
    NativeReadyProtectedStorage state files := by
  have stored {path : FilePath} {payload : ByteArray} (inside : state.writeFramePath path)
      (sampled : (names path).map contents = some payload) : files.Stored path payload := by
    obtain ⟨inode, bound, exactPayload⟩ := Option.map_eq_some_iff.mp sampled
    obtain ⟨name, bytes⟩ := physicalFrame path inside
    exact ⟨inode, name.trans bound, (bytes inode bound).trans (congrArg (fun payload => [payload]) exactPayload)⟩
  refine ⟨(physicalFrame _ (.inl rfl)).1.trans authority.directory,
    (physicalFrame _ (.inr (.inl rfl))).1.trans authority.lock, ?_, ?_, ?_⟩
  · cases selected : state.writer.target.pair.manifest with
    | none => exact (physicalFrame _ (.inr (.inr (.inl rfl)))).1.trans (Option.map_eq_none_iff.mp (manifest.trans selected))
    | some bytes => exact stored (.inr (.inr (.inl rfl))) (manifest.trans selected)
  · intro segment included
    exact stored (.inr (.inr (.inr (.inl ⟨segment, included, rfl⟩)))) (sealed segment included)
  · intro bytes metadata selected decoded index within payload storedPayload
    exact stored (.inr (.inr (.inr (.inr ⟨bytes, metadata, index, selected, decoded, within, rfl⟩))))
      ((runs metadata.header.generation index).symm.trans storedPayload)

/-- The sampled files at the healthy entry survive the exact admission,
listing and reads. The same keeper inode then supplies the write entry. -/
theorem RawAlignedCheckpointReopenEffects.ReturnedAt.writeStorageFromCheckpointSample
    (returned : raw.ReturnedAt next remove write rename bootstrap assemble get set ptrEq)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (contents : Nat → ByteArray)
    (sameFirst : (reopened).writer.wal.active.first = layout.keeper.first)
    (sameBytes : (reopened).writer.wal.active.bytes = layout.keeper.bytes)
    (authority : RebootDirectoryBindings reopened bindings)
    (manifest : (bindings ((reopened).session.directory.file .manifest)).map contents =
      (reopened).writer.target.pair.manifest)
    (sealed : ∀ segment ∈ (reopened).writer.wal.sealed,
      (bindings ((reopened).session.directory.file (.walSegment segment.first))).map contents = some segment.bytes)
    (runs : ∀ generation index, (reopened).writer.published.durable generation index =
      (bindings ((reopened).session.directory.file (.run generation index))).map contents)
    (sampled : (⟨bindings, fun inode => [contents inode]⟩ : CheckpointSurvivingFiles).Frames
      (reopened).crashPath (observe entry).files)
    (marker : (bindings ((reopened).session.directory.file .walBoundary)).map contents =
      some (WAL.Boundary.encode (WAL.encode (reopened).writer.history).size.toUInt64))
    (rootSettled : ∀ names ∈ (observe entry).crashNames, names (reopened).session.directory.path =
      (observe entry).files.names (reopened).session.directory.path)
    (keeperLive :
      let path := directory.file (.walSegment layout.keeper.first)
      let object := opening.reads.wal.keeper.observesFile.object
      (observe entry).files.names path = some object ∧ visible entry object = layout.keeper.bytes ++ layout.tail)
    (admissionEffects : raw.raw.CacheFrames raw.seed (fun before after =>
      MarkedOpenReadFrame directory (reopened).crashPath (directory.file (.walSegment layout.keeper.first))
        (observe before) (observe after) (visible before) (visible after)))
    (readEffects :
      let path := directory.file (.walSegment layout.keeper.first)
      let frame before after := MarkedOpenReadFrame directory (reopened).crashPath path
        (observe before) (observe after) (visible before) (visible after)
      raw.fileCalls.ScopeFrames frame ∧ raw.directoryCalls.ScopeFrames directory frame ∧
      ((raw.callbacks.withFileReads raw.fileCalls).modifyPending raw.seed.pendingRef
        (SyncHandleRouting.pushPending path raw.keeper.keeper) raw.keeper.read =
        .ok () raw.keeper.remembered → frame raw.keeper.read raw.keeper.remembered))
    (directoryLive :
      (raw.callbacks.withFileReads raw.fileCalls).sync raw.seed.handle raw.keeper.remembered = .ok () raw.keeper.authorized →
      (⟨(observe raw.keeper.remembered).files.names, fun inode => [visible raw.keeper.remembered inode]⟩ :
        CheckpointSurvivingFiles).Frames (· = directory.file (.walSegment layout.keeper.first))
        ⟨(observe raw.keeper.authorized).files.names, fun inode => [visible raw.keeper.authorized inode]⟩)
    (pendingLive :
      (raw.callbacks.withFileReads raw.fileCalls).setPending raw.seed.pendingRef [] raw.keeper.authorized =
        .ok () raw.keeper.consumed →
      (⟨(observe raw.keeper.authorized).files.names, fun inode => [visible raw.keeper.authorized inode]⟩ :
        CheckpointSurvivingFiles).Frames (· = directory.file (.walSegment layout.keeper.first))
        ⟨(observe raw.keeper.consumed).files.names, fun inode => [visible raw.keeper.consumed inode]⟩)
    (links : RunOpenLinkCensus (path := directory.file (.walSegment layout.keeper.first))
      (before := raw.listing.reached) raw.fileCalls.stat (observe raw.listing.reached).files.names
      opening.reads.wal.keeper.observesFile.object)
    (effects : raw.keeper.StorageEffects observe visible reopened)
    (phaseFrames : ∀ ref after, allocatePhase (.ready (reopened).writer.installed) raw.keeper.reached = .ok ref after →
      (observe raw.keeper.reached).Frames (reopened).crashPath (observe after) ∧
      ∀ inode, (observe raw.keeper.reached).files.names (keeperPath) = some inode →
        visible after inode = visible raw.keeper.reached inode)
    (tokenFrames : ∀ before ref after, allocateToken () before = .ok ref after →
      (observe before).Frames (reopened).crashPath (observe after) ∧
      ∀ inode, (observe before).files.names (keeperPath) = some inode → visible after inode = visible before inode) :
    ∃ cache : OpenSyncCacheRefs returned.handle.files returned.start.current.ready.state.session.directory.path,
      cache.directory = raw.seed.directoryRef ∧ cache.active = raw.seed.activeRef ∧ cache.pending = raw.seed.pendingRef ∧
      returned.start.WriteStorageEntry view cache (observe returned.start.reached) (visible returned.start.reached) := by
  let path := directory.file (.walSegment layout.keeper.first)
  let frame before after := MarkedOpenReadFrame directory (reopened).crashPath path
    (observe before) (observe after) (visible before) (visible after)
  have refl : ∀ atHeap, frame atHeap atHeap := fun _ => .refl _ _ _ _ _
  obtain ⟨fileEffects, listingEffects, remembered⟩ := readEffects
  have admission := raw.raw.framesThroughCache raw.seed (frame := frame) MarkedOpenReadFrame.trans admissionEffects
  obtain ⟨toListing, afterListing⟩ := raw.listing.framesThroughSeals selected raw.seals frame refl
    MarkedOpenReadFrame.trans fileEffects listingEffects
  have readKeeper := raw.keeper.framesRemembered refl MarkedOpenReadFrame.trans (fun opened => by
    have effect := fileEffects.openRead path raw.beforeKeeper
    change raw.fileCalls.openRead path raw.beforeKeeper = .ok raw.keeper.keeper raw.keeper.opened at opened
    simpa only [opened, SyncHandleRouting.reachedState] using effect)
    (fileEffects.readChunk raw.keeper.keeper) remembered
  have listedToRemembered := afterListing.trans readKeeper
  have all := admission.trans (toListing.trans listedToRemembered)
  have writtenPath {file} (holds : (reopened).writeFramePath file) :
      (reopened).crashPath file := NativeReadyState.crashPath_iff_write.mpr (.inr (.inr holds))
  have protectedAtSync := (NativeReadyProtectedStorage.ofCheckpointSample bindings contents
    (fun file valid => sampled file (writtenPath valid)) authority manifest sealed runs).frame
      (fun file valid => all.durable.visible file (writtenPath valid))
  let markerPath := (reopened).session.directory.file .walBoundary
  have keepsMarker : (reopened).crashPath markerPath := NativeReadyState.crashPath_iff_write.mpr (.inl rfl)
  have markerAtEntry : (observe entry).files.Stored markerPath
      (WAL.Boundary.encode (WAL.encode (reopened).writer.history).size.toUInt64) := by
    obtain ⟨inode, bound, observed⟩ := Option.map_eq_some_iff.mp marker
    obtain ⟨sameName, kept⟩ := sampled markerPath keepsMarker
    exact ⟨inode, sameName.trans bound, (kept inode bound).trans (congrArg (fun bytes => [bytes]) observed)⟩
  have markerAtSync := all.durable.visible.stored keepsMarker markerAtEntry
  have parent := all.durable.weaken (scope := (· = (reopened).session.directory.path))
    (fun _ same => .inl same)
  have stableRoot := parent.settledFrom (fun names member file same => same.symm ▸ rootSettled names member)
  obtain ⟨keeperName, keeperBytes⟩ := (admission.trans (toListing.trans afterListing)).keeper path rfl
  have keeperAtEntry := keeperName.trans keeperLive.1
  have visibleAtEntry := (List.cons.inj (keeperBytes _ keeperLive.1)).1.trans keeperLive.2
  have keeperAtIssue := raw.keeper.keeperAtIssue (fun atHeap => (observe atHeap).files.names) visible
    keeperAtEntry visibleAtEntry readKeeper.keeper directoryLive pendingLive
  rw [raw.keeper.keeperIssueInode, ← opening.reads.wal.keeper.observesFile.sameObject] at keeperAtIssue
  have valid := next.readPrefix.refines.1
  have apart : ∀ file, file = markerPath ∨ (reopened).writeFramePath file →
      (observe raw.keeper.remembered).files.names file ≠ some (keeperInode) := by
    intro file selectedPath bound
    have crashPath : (reopened).crashPath file := NativeReadyState.crashPath_iff_write.mpr (selectedPath.imp id Or.inr)
    have declared := NativeReadyState.crashPath_rootOrChild crashPath
    rw [returned.resolvedDirectory] at declared
    have privateAtListing := raw.extents.keeperPrivateBinding (names := fun atHeap => (observe atHeap).files.names) links
    have canonical := privateAtListing file ((listedToRemembered.names file declared).symm.trans
      (bound.trans (congrArg some opening.reads.wal.keeper.observesFile.sameObject)))
    exact NativeReadyState.protectedPathNeWalFromActive valid selectedPath (Nat.le_refl _)
      (by rw [returned.resolvedDirectory, sameFirst]; exact canonical)
  exact returned.writeStorageEntry observe visible sameFirst sameBytes protectedAtSync markerAtSync
    (fun names member => stableRoot names member _ rfl) effects keeperAtIssue apart phaseFrames tokenFrames

end CheckpointReturn

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
