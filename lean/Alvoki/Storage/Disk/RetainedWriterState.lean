import Alvoki.Storage.Disk.WalSegmentCollectionMetadata

namespace Alvoki.Storage.DiskSession

open WalSegmentRepair

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

end Alvoki.Storage.DiskSession
