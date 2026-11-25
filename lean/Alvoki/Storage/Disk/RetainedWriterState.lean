import Alvoki.Storage.Disk.WalSegmentCollectionMetadata

namespace Alvoki.Storage.DiskSession

open WalSegmentRepair WAL.Boundary Sequential

/-- Readiness for the same installed writer when covered segment files
can have been removed. The selected WAL suffix still covers every frame
needed for recovery from the strict checkpoint. -/
structure SegmentedWriterState.RetainedReady (directory : DiskDirectory) (descriptor : Nat)
    (state : SegmentedWriterState) : Prop where
  resumed : ResumedAppendReady state.installed state.files state.target state.history state.published state.checkpoint
  layout : state.wal.ReadLayout state.history
  valid : state.wal.Valid state.history
  spans : ∀ segment ∈ state.wal.sealed, segment.bytes.size = (segment.last - segment.first) * WAL.frameSize
  directoryFiles : state.files.directory = state.wal.directory
  sealedFiles : state.files.kept = (state.wal.checkpointReopenFiles state.wal.directory none).kept
  active : state.target.first = state.wal.active.first
  manifestFiles : state.published.manifest = state.files.directory.project .manifest
  held : state.owners.Owns directory descriptor

theorem SegmentedWriterState.Ready.toRetained {directory descriptor state}
    (ready : SegmentedWriterState.Ready directory descriptor state) : state.RetainedReady directory descriptor :=
  ⟨ready.resumed, ready.layout, ready.walValid, fun _ member => ready.chain.member_byteSize (List.mem_append_left _ member),
    ready.directoryFiles, ready.sealedFiles, ready.active, ready.manifestFiles, ready.held⟩

/-- The full-chain theorem adds physical provenance to the shared readiness facts. -/
theorem SegmentedWriterState.RetainedReady.withChain {directory descriptor} {state : SegmentedWriterState}
    (ready : state.RetainedReady directory descriptor)
    (chain : WalSegment.Chain state.history 0 state.wal.segments) : state.Ready directory descriptor :=
  ⟨ready.resumed, ready.layout, chain, ready.directoryFiles, ready.sealedFiles,
    ready.active, ready.manifestFiles, ready.held⟩

theorem SegmentedWriterState.RetainedReady.walPair {directory descriptor state}
    (ready : SegmentedWriterState.RetainedReady directory descriptor state) :
    state.wal.directory.active = state.target.pair :=
  (congrArg DirectoryPublication.Image.active ready.directoryFiles.symm).trans ready.resumed.ready.selected

theorem SegmentedWriterState.RetainedReady.walDirectorySettled {directory descriptor state}
    (ready : SegmentedWriterState.RetainedReady directory descriptor state) :
    state.wal.directory.crashImages = [state.wal.directory.active] := by
  rw [← ready.directoryFiles, ready.resumed.ready.settled, ready.resumed.ready.selected]

/-- A new collection pass after an earlier one uses the same exact
per-file lengths. Use the held stat report for physical sizes. -/
theorem SegmentedWriterState.RetainedReady.collectionOffsets_exact {directory descriptor state after tail}
    (ready : SegmentedWriterState.RetainedReady directory descriptor state)
    (retry : WalSegmentCollectionRetry state.wal after)
    (raw : HealthyBoundedWalReports directory state.owners descriptor after state.target.pair
      state.target.range.watermark state.published.durable tail)
    (physical : ∀ segment ∈ after.sealed, ∀ metadata,
      raw.reports.lstat (directory.file (.walSegment segment.first)) = .ok metadata →
        metadata.byteSize.toNat = segment.bytes.size) :
    (raw.reports.walSegmentOffsets directory (raw.entries.toList.map (·.fileName))).map
        (fun offsets => raw.reports.walCollectionOffsets directory offsets state.installed.activeFirst state.target.pair) =
      .ok after.collectionOffsets := by
  have ⟨pair, settled⟩ := retry.keepsSettledPair ready.walDirectorySettled
  have keeper : after.active.first = state.installed.activeFirst := by
    rw [retry.keepsActive, ← ready.active, ready.resumed.keeper]
  rw [← keeper]
  exact raw.collectionOffsets_exact (retry.readLayout ready.layout) (pair.trans ready.walPair)
    (by rw [settled, ready.walPair]) state.target.decoded physical
    (fun _ member => ready.spans _ (retry.sealedSublist.subset member))

/-- The observed manifest's strict checkpoint and installed generation
provide the generation check in the executable WAL planner. -/
theorem SelectedIntegrityCheckpoint.collectionGeneration {durable binding checkpoint}
    (selected : SelectedIntegrityCheckpoint durable binding checkpoint) :
    let generation := (checkpoint.getD (.empty, 0)).2
    validateIntegrityRunCollectionGeneration generation binding = .ok (binding.map fun _ => generation) := by
  cases selected with
  | absent => rfl
  | present decoded _ _ =>
    exact validateIntegrityRunCollectionGeneration_some.mpr ⟨_, decoded, rfl, rfl⟩

/-- Accepted, complete observations on the executable planner's callbacks
give the complete unlink plan for this exact retained writer. -/
theorem SegmentedWriterState.RetainedReady.reportedCollectionPlan {directory descriptor state tail}
    (ready : SegmentedWriterState.RetainedReady directory descriptor state)
    (raw : HealthyBoundedWalReports directory state.owners descriptor state.wal state.target.pair
      state.target.range.watermark state.published.durable tail)
    (physical : ∀ segment ∈ state.wal.sealed, ∀ metadata,
      raw.reports.lstat (directory.file (.walSegment segment.first)) = .ok metadata →
        metadata.byteSize.toNat = segment.bytes.size)
    {extents : List (Nat × IO.FS.Metadata)}
    (scan : readWalSegmentExtentsWith (m := Except IO.Error) directory
      (fun path => .ok (raw.reports.lstat path)) (raw.entries.toList.map (·.fileName)) = .ok extents)
    (healthy : checkWalCollectionInventory extents state.installed.activeFirst state.target.range = true) :
    planWalCollectionWith directory state.installed.generation state.installed.walBytes
      state.installed.activeFirst raw.reports.readOptional raw.list (fun path => .ok (raw.reports.lstat path)) =
        .ok state.wal.collectionOffsets := by
  have generation := SelectedIntegrityCheckpoint.collectionGeneration ready.resumed.selected
  dsimp only at generation
  rw [← ready.resumed.generation] at generation
  have count : state.installed.walBytes = state.target.range.through * WAL.frameSize := by
    rw [ready.resumed.bytes, ready.resumed.through, WAL.encode_size, Nat.mul_comm]
  exact (planWalCollectionWith_reported raw.reports directory _ _ _ raw.list raw.manifest raw.marker
    generation state.target.decoded count raw.listing scan healthy).trans
      (ready.collectionOffsets_exact .start raw physical)

theorem SegmentedWriterState.RetainedReady.pinnedReads {directory descriptor state}
    (ready : SegmentedWriterState.RetainedReady directory descriptor state) :
    ∃ reference : SnapshotTable UInt64, SnapshotWalReplay .empty state.history reference ∧
      ∀ pin ∈ state.installed.table.pins.active,
        (∀ key, state.installed.table.lookup pin.handle key = some (reference.table.lookup key pin.sequence)) ∧
        ∀ start stop, state.installed.table.range pin.handle start stop =
          some (reference.table.range start stop pin.sequence) := by
  obtain ⟨_, refined, represented⟩ := ready.resumed.canonical
  obtain ⟨reference, replayed⟩ := SnapshotWalReplay.fromEmpty state.history ready.resumed.ordered
  exact ⟨reference, replayed, fun _ active => represented.packedPinnedReads refined replayed active⟩

/-- A supported snapshot of a retained writer, including one returned
by recovery, has the same reads as replay of the full logical history. -/
theorem SegmentedWriterState.RetainedReady.acquireReads {directory descriptor state}
    (ready : SegmentedWriterState.RetainedReady directory descriptor state) {snapshot : UInt64}
    (retained : state.installed.table.pins.floor ≤ snapshot) (committed : snapshot ≤ state.installed.table.committed) :
    ∃ reference : SnapshotTable UInt64, SnapshotWalReplay .empty state.history reference ∧
      ∃ pin pinned, state.installed.table.acquireAt snapshot = some (pin, pinned) ∧
        (∀ key, pinned.lookup pin.handle key = some (reference.table.lookup key snapshot)) ∧
        ∀ start stop, pinned.range pin.handle start stop = some (reference.table.range start stop snapshot) := by
  obtain ⟨_, refined, represented⟩ := ready.resumed.canonical
  obtain ⟨reference, replayed⟩ := SnapshotWalReplay.fromEmpty state.history ready.resumed.ordered
  exact ⟨reference, replayed, represented.acquireReads refined ready.resumed.bounds replayed retained committed⟩

/-- A sequence still above the retention floor has the same reads after
reacquisition, even if collection removed physical files covering it. -/
theorem SegmentedWriterState.RetainedReady.reacquireReadsStable {directory initialDescriptor descriptor initial last}
    (initialReady : SegmentedWriterState.RetainedReady directory initialDescriptor initial)
    (ready : SegmentedWriterState.RetainedReady directory descriptor last) {suffix : List WAL.Write}
    (history : last.history = initial.history ++ suffix) {oldPin : SnapshotPin}
    (active : oldPin ∈ initial.installed.table.pins.active)
    (retained : last.installed.table.pins.floor ≤ oldPin.sequence) :
    ∃ newPin pinned, last.installed.table.acquireAt oldPin.sequence = some (newPin, pinned) ∧
      newPin.sequence = oldPin.sequence ∧
      (∀ key, pinned.lookup newPin.handle key = initial.installed.table.lookup oldPin.handle key) ∧
      ∀ start stop, pinned.range newPin.handle start stop = initial.installed.table.range oldPin.handle start stop := by
  obtain ⟨initialModel, initialRefines, previous⟩ := initialReady.resumed.canonical
  obtain ⟨_, lastRefines, represented⟩ := ready.resumed.canonical
  have oldCommitted := initialModel.pins_committed oldPin (initialRefines.pins ▸ active)
  have nowCommitted : oldPin.sequence ≤ last.installed.table.committed := by
    rw [UInt64.le_iff_toNat_le, previous.committed_count] at oldCommitted
    rw [lastRefines.committed, UInt64.le_iff_toNat_le, represented.committed_count, history]
    exact Nat.le_trans oldCommitted (by simp)
  obtain ⟨_, replayed, newPin, pinned, acquired, _, _⟩ := ready.acquireReads retained nowCommitted
  obtain ⟨_, refined, next⟩ := represented.acquireAt lastRefines ready.resumed.bounds acquired
  have pinSpec := PackedTable.acquireAt_spec acquired
  rw [history] at next replayed
  exact ⟨newPin, pinned, acquired, pinSpec.sequence,
    previous.packedPinnedReadsAfterAppend next initialRefines refined replayed active pinSpec.active pinSpec.sequence⟩

end Alvoki.Storage.DiskSession
