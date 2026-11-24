import Alvoki.Storage.Disk.SegmentedWriterState

namespace Alvoki.Storage

private theorem WalSegmentDeletion.sublist {eligible : WalSegment → Prop} {before after : List WalSegment}
    (deleted : WalSegmentDeletion eligible before after) : after.Sublist before := by
  induction deleted with
  | empty => exact .slnil
  | keep _ rest => exact rest.cons_cons _
  | remove _ _ rest => exact rest.cons _

private theorem WalSegmentCollectionRetry.sealedSublist {initial after : WalSegmentImage}
    (retry : WalSegmentCollectionRetry initial after) : after.sealed.Sublist initial.sealed := by
  induction retry with
  | start => exact List.Sublist.refl _
  | unlink _ deleted earlier => exact deleted.sublist.trans earlier
  | settle _ earlier | crash _ _ earlier => exact earlier

/-- Unlinks preserve the read layout, even when the older covered files
left by an interrupted pass have gaps. -/
theorem WalSegmentCollectionRetry.readLayout {initial after : WalSegmentImage} {history : List WAL.Write}
    (retry : WalSegmentCollectionRetry initial after) (layout : initial.ReadLayout history) :
    after.ReadLayout history := by
  have segments : after.segments.Sublist initial.segments := by
    simpa only [WalSegmentImage.segments, retry.keepsActive] using
      retry.sealedSublist.append_right [initial.active]
  exact ⟨layout.ordered.sublist segments, fun segment member => layout.forward segment (segments.subset member),
    retry.keepsActive.symm ▸ layout.activeEnd, retry.keepsActive.symm ▸ layout.activeBytes⟩

/-- The read descriptors keep the active file even at a fully covered
watermark, where the logical replay suffix can be empty. -/
theorem WalSegmentCollectionRetry.keepsReadDescriptors {initial after : WalSegmentImage}
    (retry : WalSegmentCollectionRetry initial after) {pair : DirectoryPublication.Bindings}
    (chosen : after.Selects pair) {range : MarkedWalRange} (decoded : pair.walRange = some range) :
    after.readDescriptors range.watermark = initial.readDescriptors range.watermark := by
  simp only [WalSegmentImage.readDescriptors, retry.keepsActive, (retry.preservesSelected chosen).2 range decoded]

namespace DiskSession

/-- A settled writer supplies the same strict checkpoint on its original
durable run map and the same physical read descriptors for every collection
retry outcome. The WAL may no longer have a physical chain from zero. -/
theorem SegmentedWriterState.Ready.collectionReadPlan {directory descriptor state after}
    (ready : SegmentedWriterState.Ready directory descriptor state)
    (retry : WalSegmentCollectionRetry state.wal after) {pair : DirectoryPublication.Bindings}
    (chosen : after.Selects pair) :
    pair = state.target.pair ∧ after.active = state.wal.active ∧
      after.readDescriptors state.target.range.watermark = state.wal.readDescriptors state.target.range.watermark ∧
      SelectedIntegrityCheckpoint state.published.durable pair.manifest state.checkpoint := by
  have original := (retry.preservesSelected chosen).1
  have visible : pair = state.wal.directory.active := by
    simpa [WalSegmentImage.Selects, ready.walDirectorySettled] using original
  have samePair : pair = state.target.pair := by
    rw [visible, ← ready.directoryFiles, ready.resumed.ready.selected]
  have decoded : pair.walRange = some state.target.range := samePair.symm ▸ state.target.decoded
  exact ⟨samePair, retry.keepsActive, retry.keepsReadDescriptors chosen decoded,
    samePair.symm ▸ ready.resumed.selected⟩

/-- The retained offsets passed to the read planner still select the same
ordered physical descriptors, with their exact encoded history suffix. -/
theorem SegmentedWriterState.Ready.collectionSelectsReads {directory descriptor state after}
    (ready : SegmentedWriterState.Ready directory descriptor state)
    (retry : WalSegmentCollectionRetry state.wal after) :
    ∃ first, first ≤ state.target.range.watermark ∧
      selectWalSegmentReads (after.segments.map (·.first)) state.target.range.watermark =
        some (first, (state.wal.readDescriptors state.target.range.watermark).map (·.first)) ∧
      WalSegment.Chain state.history first (after.readDescriptors state.target.range.watermark) ∧
      WalSegment.concatenate (after.readDescriptors state.target.range.watermark) =
        WAL.encode (state.history.drop first) := by
  have chosen : after.Selects after.directory.active := List.mem_cons_self ..
  obtain ⟨samePair, _, sameReads, _⟩ := ready.collectionReadPlan retry chosen
  have decoded : after.directory.active.walRange = some state.target.range := samePair.symm ▸ state.target.decoded
  obtain ⟨first, covered, _, selected, chain, bytes⟩ :=
    (retry.readLayout ready.layout).selects (retry.valid ready.walValid) chosen decoded
  exact ⟨first, covered, by simpa only [sameReads] using selected, chain, bytes⟩

end DiskSession
end Alvoki.Storage
