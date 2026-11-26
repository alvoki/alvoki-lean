import Alvoki.Storage.Disk.NativeDurableWriteReboot
import Alvoki.Storage.Disk.NativeMarkedEntryObservations

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WAL.Boundary

/-- A retained writer's file map contains the bytes of every immutable
seal, including segments covered by the chosen checkpoint. -/
theorem SegmentedWriterState.RetainedReady.keptSeal {state : SegmentedWriterState}
    {directory : DiskDirectory} {descriptor : Nat} (valid : state.RetainedReady directory descriptor)
    {segment : WalSegment} (member : segment ∈ state.wal.sealed) :
    state.files.kept segment.first = some segment.bytes := by
  have ordered := ((List.pairwise_append.mp valid.layout.ordered).1).imp (fun relation => relation.1)
  rw [valid.sealedFiles]
  change (state.wal.sealed.find? (·.first == segment.first)).map WalSegment.bytes = _
  rw [WalSegment.findSealedStart ordered member]
  rfl

/-- The mutable keeper and later WAL paths are outside the immutable footprint.
Every retained seal starts strictly before the keeper. -/
theorem NativeReadyState.protectedPathNeWalFromActive {state : NativeReadyState} (ready : state.Valid)
    {path : FilePath} (selected : state.selectedRetryPath path) {first : Nat}
    (atOrAfter : state.writer.wal.active.first ≤ first) :
    path ≠ state.session.directory.file (.walSegment first) := by
  rcases selected with marker | protectedPath
  · intro equal
    obtain ⟨_, collision⟩ := DiskDirectory.walSegment_exclusive (marker.symm.trans equal)
    cases collision
  · rcases protectedPath with rfl | rfl | rfl | ⟨segment, member, rfl⟩ | ⟨_, metadata, index, _, _, _, rfl⟩
    · exact (SyncHandleRouting.file_ne_directory _ _).symm
    · intro equal
      obtain ⟨_, collision⟩ := DiskDirectory.walSegment_exclusive equal
      cases collision
    · intro equal
      obtain ⟨_, collision⟩ := DiskDirectory.walSegment_exclusive equal
      cases collision
    · have ordered := (List.pairwise_append.mp ready.retained.layout.ordered).2.2 _ member
          state.writer.wal.active (List.mem_singleton_self _)
      exact fun same => Nat.ne_of_lt (Nat.lt_of_lt_of_le ordered.1 atOrAfter) (state.session.directory.walSegment_path_injective same)
    · intro equal
      obtain ⟨_, collision⟩ := DiskDirectory.walSegment_exclusive equal
      cases collision

/-- Reindex the durable immutable footprint to the reopened writer. The
root and lock are checked against the new descriptions. Manifest, runs
and all retained seals use the same exact contents. -/
theorem NativeReadyProtectedStorage.forReopenedWriter
    {prior next : NativeReadyState} {files : CheckpointSurvivingFiles}
    (previous : NativeReadyProtectedStorage prior files)
    (oldReady : prior.Valid) (newReady : next.Valid)
    (directory : next.session.directory = prior.session.directory)
    (manifest : next.writer.target.pair.manifest = prior.writer.target.pair.manifest)
    (published : next.writer.published.durable = prior.writer.published.durable)
    (kept : next.writer.files.kept = prior.writer.files.kept)
    (root : files.names next.session.directory.path = some (next.census.inode next.directorySlot.description))
    (lock : files.names (next.session.directory.file .lock) = some (next.census.inode next.owner.description)) :
    NativeReadyProtectedStorage next files := by
  refine ⟨root, lock, ?_, ?_, ?_⟩
  · rw [directory, manifest]
    exact previous.manifest
  · intro segment member
    have same := newReady.retained.keptSeal member
    rw [kept, oldReady.retained.sealedFiles] at same
    change (prior.writer.wal.sealed.find? (·.first == segment.first)).map WalSegment.bytes = _ at same
    cases found : prior.writer.wal.sealed.find? (·.first == segment.first) with
    | none => simp [found] at same
    | some older =>
      have oldMember := List.mem_of_find?_eq_some found
      have sameKey : (older.first == segment.first) = true := List.find?_some (p := fun item : WalSegment => item.first == segment.first) found
      have sameFirst : older.first = segment.first := beq_iff_eq.mp sameKey
      have sameBytes : older.bytes = segment.bytes := by simpa only [found, Option.map_some, Option.some.injEq] using same
      rw [directory, ← sameFirst, ← sameBytes]
      exact previous.sealedFiles older oldMember
  · intro bytes metadata selected decoded index bounded payload stored
    rw [directory]
    exact previous.runs bytes metadata (manifest.symm.trans selected) decoded index bounded payload (published ▸ stored)

/-- Instantiate the immutable retry footprint for the selected reopened
writer. The observed marker has the canonical count of its history. -/
theorem NativeReadyState.SelectedRetryDurability.forReopenedWriter
    {prior next : NativeReadyState} {target : Target} {storage : CheckpointStorageObservation}
    (previous : prior.SelectedRetryDurability target storage)
    (oldReady : prior.Valid) (newReady : next.Valid)
    (directory : next.session.directory = prior.session.directory)
    (selected : next.writer.target = target)
    (manifest : target.pair.manifest = prior.writer.target.pair.manifest)
    (published : next.writer.published.durable = prior.writer.published.durable)
    (kept : next.writer.files.kept = prior.writer.files.kept)
    (root : storage.files.names next.session.directory.path = some (next.census.inode next.directorySlot.description))
    (lock : storage.files.names (next.session.directory.file .lock) = some (next.census.inode next.owner.description)) :
    NativeReadyProtectedStorage next storage.files ∧
      storage.files.Stored (next.session.directory.file .walBoundary)
        (WAL.Boundary.encode (WAL.encode next.writer.history).size.toUInt64) ∧
      ∀ names ∈ storage.crashNames,
        names next.session.directory.path = storage.files.names next.session.directory.path := by
  have marker := congrArg Publication.Image.active newReady.retained.resumed.markerImage
  change (next.writer.files.directory.project .walBoundary).active = _ at marker
  simp only [DirectoryPublication.Image.project, newReady.retained.resumed.ready.selected,
    DirectoryPublication.Bindings.get, WriteFiles.initial] at marker
  rw [selected] at marker
  refine ⟨previous.protectedFiles.forReopenedWriter oldReady newReady directory
    ((congrArg (fun target : Target => target.pair.manifest) selected).trans manifest)
    published kept root lock, ?_, ?_⟩
  · rw [directory]
    exact previous.marker _ marker
  · rw [directory]
    exact previous.rootSettled

/-- Carry the durable footprint to a repair stage that frames the
retained files and the parent binding. Reindex it to the selected
writer using the root and lock of this actual admission. -/
theorem RawHealthyMarkedOpenEffects.reopenedFootprintAt
    {heap stream : Type} {prior next : NativeReadyState} {input : FilePath}
    {inventory : DescriptorInventory} {retry : LockedFileState FileImage}
    {vacant : TryLockObserves retry.owners prior.session.directory (.ok true)}
    {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
    {selected : SelectedIntegrityCheckpoint prior.writer.published.durable
      retry.image.directory.active.manifest prior.writer.checkpoint}
    {opening : MarkedReadyOpenObservations input prior.session.directory inventory retry layout
      prior.writer.published vacant selected}
    {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
    {init : OpenSyncCacheCallbacks heap} {entry atHeap : heap}
    {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
    {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
    {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
    {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)} {stage : LongKeeperStageCallbacks heap}
    {rename : FilePath → FilePath → EStateM IO.Error heap Unit}
    (raw : RawHealthyMarkedOpenEffects opening view calls init entry phaseIdentity tokenIdentity
      allocatePhase allocateToken stream remove stage rename)
    (observe : heap → CheckpointStorageObservation)
    (durable : prior.SelectedRetryDurability layout.target (observe entry))
    (files : (observe entry).files.Frames prior.selectedRetryPath (observe atHeap).files)
    (parent : (observe entry).Frames (· = prior.session.directory.path) (observe atHeap))
    (root : (observe entry).files.names prior.session.directory.path =
      some ((view.handle raw.seed.afterPending raw.seed.handle).1.inode
        (view.handle raw.seed.afterPending raw.seed.handle).2.1.description))
    (lock : (observe entry).files.names (prior.session.directory.file .lock) =
      some ((view.handle raw.raw.afterFlock raw.raw.lock).1.inode (view.handle raw.raw.afterFlock raw.raw.lock).2.1.description))
    (sameObjects : opening.finish.census.inode = opening.admission.reached.inode)
    (priorReady : prior.Valid) (nextReady : next.Valid)
    (directory : next.session.directory = prior.session.directory)
    (census : next.census = opening.finish.census)
    (owner : next.owner = opening.admission.owner) (slot : next.directorySlot = opening.admission.cached)
    (target : next.writer.target = layout.target)
    (manifest : layout.target.pair.manifest = prior.writer.target.pair.manifest)
    (published : next.writer.published.durable = prior.writer.published.durable)
    (kept : next.writer.files.kept = prior.writer.files.kept) :
    NativeReadyProtectedStorage next (observe atHeap).files ∧
      (observe atHeap).files.Stored (next.session.directory.file .walBoundary)
        (WAL.Boundary.encode (WAL.encode next.writer.history).size.toUInt64) ∧
      ∀ names ∈ (observe atHeap).crashNames,
        names next.session.directory.path = (observe atHeap).files.names next.session.directory.path := by
  obtain ⟨boundRoot, boundLock⟩ := raw.reopenedAuthority (fun heap => (observe heap).files) root lock
    (fun path selected => files path (.inr (selected.imp id (fun same => .inl same)))) sameObjects
  exact (durable.frame files parent).forReopenedWriter priorReady nextReady directory target manifest published kept
    (by rw [directory, census, slot]; exact boundRoot) (by rw [directory, census, owner]; exact boundLock)

end Alvoki.Storage.DiskSession
