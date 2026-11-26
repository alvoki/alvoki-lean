import Alvoki.Storage.Disk.NativeCheckpointSourceCrash
import Alvoki.Storage.Disk.NativeOpenReferences

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

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
