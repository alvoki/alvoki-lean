import Alvoki.Storage.Disk.NativeCheckpointSourceCrash
import Alvoki.Storage.Disk.NativeOpenReferences
import Alvoki.Storage.Disk.NativeWalPublicationTail

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

section OpenInstallation

variable {heap : Type} {view : OpenCloseHeapView heap FileImage}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
  {installed : Installed} {repaired : heap}

/-- These are the heap projections a reference allocation leaves in
place. Phase-cell contents and the newly allocated token are separate. -/
structure OpenInstallHeapFrame (view : OpenCloseHeapView heap FileImage) (lock : IO.FS.Handle)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (before reached : heap) : Prop where
  files : view.files reached = view.files before
  census : view.descriptors reached = view.descriptors before
  cache : view.cacheAt reached cached active pending = view.cacheAt before cached active pending
  lock : (view.handle reached lock).2.1 = (view.handle before lock).2.1

/-- Use the repaired census and cache and the identities of the actual
phase and token cells. The writer value comes from the completed replay. -/
def OpenReferenceAllocations.readyState
    (allocation : OpenReferenceAllocations allocatePhase allocateToken view.phase installed repaired)
    (writer : SegmentedWriterState) (directory : DiskDirectory) (owner directorySlot : DescriptorSlot)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat) : NativeReadyState :=
  ⟨⟨directory, owner.description, .ready installed, phaseIdentity allocation.phase, tokenIdentity allocation.token⟩,
    writer, view.descriptors repaired, view.cacheAt repaired cached active pending, owner, directorySlot⟩

/-- Assemble a valid writer and the literal table from the same two
successful allocations. The local frames identify the caller-visible
descriptor census, files, lock slot, and cache with their repair state. -/
theorem OpenReferenceAllocations.installsReadyState
    (allocation : OpenReferenceAllocations allocatePhase allocateToken view.phase installed repaired)
    (writer : SegmentedWriterState) (directory : DiskDirectory) (owner directorySlot : DescriptorSlot)
    {lock : IO.FS.Handle} {syncFiles : DiskTable.OpenSyncFiles}
    {assemble : IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable}
    (constructor : DiskTable.OpenReferenceAssembly directory lock syncFiles assemble)
    (cache : OpenSyncCacheRefs syncFiles directory.path)
    (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat)
    (sameInstalled : installed = writer.installed)
    (retained : writer.RetainedReady directory owner.description)
    (files : view.files repaired = ⟨writer.files, writer.owners⟩)
    (ownsSlot : (view.handle repaired lock).2.1 = owner)
    (ownerLive : owner ∈ (view.descriptors repaired).slots)
    (directoryLive : directorySlot ∈ (view.descriptors repaired).slots)
    (directoryCached : ∃ captured, (view.cacheAt repaired cache.directory cache.active cache.pending).directory =
      some (captured, directorySlot, 0))
    (phaseFrame : OpenInstallHeapFrame view lock cache.directory cache.active cache.pending repaired allocation.afterPhase)
    (tokenFrame : OpenInstallHeapFrame view lock cache.directory cache.active cache.pending allocation.afterPhase allocation.afterToken) :
    let state := allocation.readyState writer directory owner directorySlot cache.directory cache.active cache.pending
      phaseIdentity tokenIdentity
    let db := assemble allocation.phase allocation.token
    state.Valid ∧
    installReady installed allocatePhase allocateToken (fun phase token => pure (assemble phase token)) repaired =
      .ok db allocation.afterToken ∧
    db.UsesOpenReferences directory lock syncFiles allocation.phase allocation.token ∧
    view.phase allocation.afterToken allocation.phase = some state.session.phase ∧
    view.files allocation.afterToken = state.files ∧
    view.descriptors allocation.afterToken = state.census ∧
    view.cacheAt allocation.afterToken cache.directory cache.active cache.pending = state.cache ∧
    (view.handle allocation.afterToken lock).2.1 = state.owner := by
  intro state db
  obtain ⟨returned, references, phase⟩ := allocation.installs constructor
  have ready : state.Valid := ⟨congrArg Phase.ready sameInstalled, rfl, ownerLive, directoryLive, directoryCached, retained⟩
  exact ⟨ready, returned, references, phase, tokenFrame.files.trans (phaseFrame.files.trans files),
    tokenFrame.census.trans phaseFrame.census, tokenFrame.cache.trans phaseFrame.cache,
    tokenFrame.lock.trans (phaseFrame.lock.trans ownsSlot)⟩

end OpenInstallation

theorem NativeReadyState.crashPath_rootOrChild {state : NativeReadyState} {path : FilePath}
    (selected : state.crashPath path) :
    path = state.session.directory.path ∨ ∃ file, path = state.session.directory.file file := by
  rcases NativeReadyState.crashPath_iff_write.mp selected with rfl | rfl | frame
  · exact .inr ⟨.walBoundary, rfl⟩
  · exact .inr ⟨.walSegment _, rfl⟩
  · rcases frame with rfl | rfl | rfl | ⟨segment, _, rfl⟩ | ⟨_, metadata, index, _, _, _, rfl⟩
    · exact .inl rfl
    · exact .inr ⟨.lock, rfl⟩
    · exact .inr ⟨.manifest, rfl⟩
    · exact .inr ⟨.walSegment segment.first, rfl⟩
    · exact .inr ⟨.run metadata.header.generation index, rfl⟩

/-- A directory fsync preserves the already durable ready files whether
or not the call settles its children. The directory's own name is a
parent entry and uses its independently observed binding. -/
theorem WalRootSyncEffect.preservesReadyStorage
    {state : NativeReadyState} {effective : Bool} {issued failed : CheckpointStorageObservation}
    (effect : WalRootSyncEffect state.session.directory effective issued failed)
    (ready : NativeReadyStorage state issued)
    (rootLive : failed.files.names state.session.directory.path =
      issued.files.names state.session.directory.path)
    (rootSurvives : ∀ names ∈ failed.crashNames,
      names state.session.directory.path = failed.files.names state.session.directory.path) :
    NativeReadyStorage state failed := by
  have liveChildren : issued.files.Frames
      (fun path => ∃ file, path = state.session.directory.file file) failed.files := by
    rintro _ ⟨file, rfl⟩
    exact ⟨effect.visible file, fun inode named =>
      effect.bytes _ (.inl rfl) file inode ((effect.visible file).trans named)⟩
  refine ⟨ready.toNativeReadyProtectedStorage.frameChildren (rootLive.trans ready.directoryBound)
    (fun path kept => liveChildren path kept.2), liveChildren.stored ⟨.walBoundary, rfl⟩ ready.marker,
    liveChildren.stored ⟨.walSegment _, rfl⟩ ready.keeper, ?_⟩
  intro names chosen path protectedPath
  rcases NativeReadyState.crashPath_rootOrChild protectedPath with rfl | ⟨file, rfl⟩
  · exact rootSurvives names chosen
  · cases applied : effective with
    | true => exact effect.settled applied names chosen file
    | false =>
      obtain ⟨prior, available, same⟩ := effect.unchanged applied names chosen
      exact (same file).trans ((ready.settled prior available _ protectedPath).trans (effect.visible file).symm)

/-- A directory fsync settles its children. Its own name is an entry in
the parent, whose independent settlement must survive the call. -/
theorem NativeReadyState.settledByDirectory {state : NativeReadyState} {issued reached : CheckpointStorageObservation}
    (parent : issued.Frames (· = state.session.directory.path) reached)
    (rootSettled : ∀ names ∈ issued.crashNames, names state.session.directory.path =
      issued.files.names state.session.directory.path)
    (children : ∀ names ∈ reached.crashNames, ∀ file, names (state.session.directory.file file) =
      reached.files.names (state.session.directory.file file)) :
    ∀ names ∈ reached.crashNames, ∀ path, state.crashPath path → names path = reached.files.names path := by
  intro names member path selected
  rcases NativeReadyState.crashPath_rootOrChild selected with same | ⟨file, rfl⟩
  · exact parent.settledFrom (by intro prior allowed name eq; cases eq; exact rootSettled prior allowed)
      names member path same
  · exact children names member file

/-- Project the observed directory barrier onto the ready writer's files.
The parent frame and its prior settlement account for the directory's own name. -/
theorem NativeReadyState.framesByDirectory {state : NativeReadyState} {directory : DiskDirectory}
    {issued reached : CheckpointStorageObservation} (sameDirectory : state.session.directory = directory)
    (parent : issued.Frames (· = state.session.directory.path) reached)
    (childFiles : issued.files.Frames (fun path => ∃ file, path = directory.file file) reached.files)
    (rootSettled : ∀ names ∈ issued.crashNames, names state.session.directory.path =
      issued.files.names state.session.directory.path)
    (children : ∀ names ∈ reached.crashNames, ∀ file, names (state.session.directory.file file) =
      reached.files.names (state.session.directory.file file)) :
    issued.files.Frames state.crashPath reached.files ∧
    ∀ names ∈ reached.crashNames, ∀ path, state.crashPath path → names path = reached.files.names path := by
  refine ⟨?_, settledByDirectory parent rootSettled children⟩
  intro path selected
  rcases crashPath_rootOrChild selected with root | ⟨file, child⟩
  · exact parent.visible path root
  · exact childFiles path ⟨file, child.trans (congrArg (·.file file) sameDirectory)⟩

/-- The final regular-file barrier establishes keeper bytes. Earlier
directory settlement and the durable unrelated files are preserved. -/
theorem NativeReadyStorage.afterKeeperSync {state : NativeReadyState} {issued reached : CheckpointStorageObservation}
    {inode : Nat} (sync : RegularFileSyncEffect inode [state.writer.wal.active.bytes] issued reached)
    (keeper : issued.files.names (state.session.directory.file (.walSegment state.writer.wal.active.first)) = some inode)
    (protectedFiles : NativeReadyProtectedStorage state issued.files)
    (marker : issued.files.Stored (state.session.directory.file .walBoundary)
      (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64))
    (apart : ∀ path, path = state.session.directory.file .walBoundary ∨ state.writeFramePath path →
      issued.files.names path ≠ some inode)
    (settled : ∀ names ∈ issued.crashNames, ∀ path, state.crashPath path → names path = issued.files.names path) :
    NativeReadyStorage state reached := by
  have frame := sync.frames (footprint := fun path =>
    path = state.session.directory.file .walBoundary ∨ state.writeFramePath path)
      (fun path selected other bound same => apart path selected (bound.trans (congrArg some same)))
  refine ⟨protectedFiles.frame (fun path keep => frame.visible path (.inr keep)),
    frame.visible.stored (.inl rfl) marker, sync.stored keeper, ?_⟩
  intro names allowed path selected
  rw [sync.crashNames] at allowed
  exact (settled names allowed path selected).trans (congrFun sync.names path).symm

/-- Once the directory barrier settles the protected names, frame them
through cache effects and settle the selected keeper on its own inode. -/
theorem NativeReadyStorage.afterAlignedBarriers {state : NativeReadyState}
    {entry authorized consumed repaired : CheckpointStorageObservation} {inode : Nat}
    (directoryFrame : entry.files.Frames state.crashPath authorized.files)
    (settled : ∀ names ∈ authorized.crashNames, ∀ path, state.crashPath path → names path = authorized.files.names path)
    (consumeFrame : authorized.Frames state.crashPath consumed)
    (protectedFiles : NativeReadyProtectedStorage state entry.files)
    (marker : entry.files.Stored (state.session.directory.file .walBoundary)
      (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64))
    (apart : ∀ path, path = state.session.directory.file .walBoundary ∨ state.writeFramePath path →
      entry.files.names path ≠ some inode)
    (bound : consumed.files.names (state.session.directory.file (.walSegment state.writer.wal.active.first)) = some inode)
    (sync : RegularFileSyncEffect inode [state.writer.wal.active.bytes] consumed repaired) :
    NativeReadyStorage state repaired := by
  have frame := directoryFrame.trans consumeFrame.visible
  refine NativeReadyStorage.afterKeeperSync sync bound
    (protectedFiles.frame (fun path kept => frame path (NativeReadyState.crashPath_iff_write.mpr (.inr (.inr kept)))))
    (frame.stored (NativeReadyState.crashPath_iff_write.mpr (.inl rfl)) marker) ?_ (consumeFrame.settledFrom settled)
  intro path kept named
  have same := (frame path (NativeReadyState.crashPath_iff_write.mpr (kept.imp id Or.inr))).1
  exact apart path kept (same.symm.trans named)

/-- The ready phase and token allocations preserve settled files and the
visible keeper bytes that the next append uses. Their local frames start
at the repaired heap and end at the heap returned by the installer. -/
theorem OpenReferenceAllocations.framesReadyStorage {heap : Type}
    {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
    {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
    {contents : heap → IO.Ref (Phase Installed) → Option (Phase Installed)} {before : heap}
    {installed : Installed} {state : NativeReadyState}
    (allocation : OpenReferenceAllocations allocatePhase allocateToken contents installed before)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (ready : NativeReadyStorage state (observe before))
    (keeperLive : ∀ inode, (observe before).files.names
      (state.session.directory.file (.walSegment state.writer.wal.active.first)) = some inode →
      visible before inode = state.writer.wal.active.bytes)
    (phaseFrame : (observe before).Frames state.crashPath (observe allocation.afterPhase))
    (tokenFrame : (observe allocation.afterPhase).Frames state.crashPath (observe allocation.afterToken))
    (phaseKeeper : ∀ inode, (observe before).files.names
      (state.session.directory.file (.walSegment state.writer.wal.active.first)) = some inode →
      visible allocation.afterPhase inode = visible before inode)
    (tokenKeeper : ∀ inode, (observe allocation.afterPhase).files.names
      (state.session.directory.file (.walSegment state.writer.wal.active.first)) = some inode →
      visible allocation.afterToken inode = visible allocation.afterPhase inode) :
    NativeReadyStorage state (observe allocation.afterToken) ∧
    ∀ inode, (observe allocation.afterToken).files.names
      (state.session.directory.file (.walSegment state.writer.wal.active.first)) = some inode →
      visible allocation.afterToken inode = state.writer.wal.active.bytes := by
  let path := state.session.directory.file (.walSegment state.writer.wal.active.first)
  have selected : state.crashPath path := NativeReadyState.crashPath_iff_write.mpr (.inr (.inl rfl))
  refine ⟨ready.frame (phaseFrame.trans tokenFrame), ?_⟩
  intro inode bound
  have atPhase := ((tokenFrame.visible path selected).1).symm.trans bound
  have atRepair := ((phaseFrame.visible path selected).1).symm.trans atPhase
  exact (tokenKeeper inode atPhase).trans ((phaseKeeper inode atRepair).trans (keeperLive inode atRepair))

/-- The literal cached directory handle still identifies the named root
when its captured inventory and the ready census agree on inode identity. -/
theorem NativeReadyStorage.bindsOpenCacheDirectory {heap image : Type}
    {state : NativeReadyState} {storage : CheckpointStorageObservation}
    (ready : NativeReadyStorage state storage) (view : OpenCloseHeapView heap image) {reached : heap}
    {directory : IO.Ref (Option IO.FS.Handle)} {active : IO.Ref (Option (FilePath × IO.FS.Handle))}
    {pending : IO.Ref (List (FilePath × IO.FS.Handle))} {captured : DescriptorInventory}
    (cache : view.cacheAt reached directory active pending = state.cache)
    (atOpen : state.cache.directory = some (captured, state.directorySlot, 0))
    (inode : captured.inode state.directorySlot.description = state.census.inode state.directorySlot.description)
    {literal : IO.FS.Handle} (found : view.directory reached directory = some literal) :
    storage.files.names state.session.directory.path =
      some ((view.handle reached literal).1.inode (view.handle reached literal).2.1.description) := by
  have same := (congrArg SyncHandleRouting.Cache.directory cache).trans atOpen
  change (view.directory reached directory).map (view.handle reached) = _ at same
  rw [found] at same
  rw [Option.some.inj same, inode]
  exact ready.directoryBound

end Alvoki.Storage.DiskSession
