import Alvoki.Storage.Disk.NativeDurableWriteReboot

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

/-- The guarded keeper's path is outside the immutable footprint:
distinct WAL starts and file kinds give distinct canonical paths. -/
theorem NativeReadyState.protectedPathNeKeeper {state : NativeReadyState} (ready : state.Valid)
    {path : FilePath}
    (selected : state.selectedRetryPath path) :
    path ≠ state.session.directory.file (.walSegment state.writer.wal.active.first) := by
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
      exact fun same => Nat.ne_of_lt ordered.1 (state.session.directory.walSegment_path_injective same)
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

end Alvoki.Storage.DiskSession
