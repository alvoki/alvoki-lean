import Alvoki.Storage.Disk.SegmentedCollectionReadPlan

namespace Alvoki.Storage

theorem WalSegmentCollectionRetry.trans {initial middle after : WalSegmentImage}
    (first : WalSegmentCollectionRetry initial middle) (rest : WalSegmentCollectionRetry middle after) :
    WalSegmentCollectionRetry initial after := by
  induction rest with
  | start => exact first
  | unlink _ removed earlier => exact .unlink earlier removed
  | settle _ earlier => exact .settle earlier
  | crash _ survives earlier => exact .crash earlier survives

/-- Later unlink cuts, directory barriers and crashes keep the original
metadata pair when collection starts with it settled. -/
theorem WalSegmentCollectionRetry.keepsSettledPair {initial after : WalSegmentImage}
    (retry : WalSegmentCollectionRetry initial after)
    (settled : initial.directory.crashImages = [initial.directory.active]) :
    after.directory.active = initial.directory.active ∧ after.directory.crashImages = [initial.directory.active] := by
  induction retry with
  | start => exact ⟨rfl, settled⟩
  | unlink _ _ earlier => exact earlier
  | settle _ earlier => exact ⟨earlier.1, congrArg (fun pair => [pair]) earlier.1⟩
  | crash _ survives earlier =>
    rw [earlier.2] at survives
    have same := List.mem_singleton.mp survives
    exact ⟨same, congrArg (fun pair => [pair]) same⟩

namespace DiskSession

private theorem SegmentedWriterState.Ready.checkpointWatermark {directory descriptor state}
    (ready : SegmentedWriterState.Ready directory descriptor state) :
    state.target.range.watermark = (state.checkpoint.getD (.empty, 0)).1.committed.toNat :=
  Option.some.inj ((DirectoryPublication.Bindings.walRange_accounting state.target.decoded).1.symm.trans
    ready.resumed.selected.watermark)

/-- The modeled deletion test uses the settled strict checkpoint's
loaded watermark, even after prior cuts. Unlinking also requires that the
candidate denotes an actual sealed file in the locked inventory. -/
theorem SegmentedWriterState.Ready.collectionCanRemove {directory descriptor state after}
    (ready : SegmentedWriterState.Ready directory descriptor state)
    (retry : WalSegmentCollectionRetry state.wal after) (segment : WalSegment) :
    after.canRemove segment = true ↔
      segment.first < segment.last ∧ segment.last ≤ state.installed.activeFirst ∧
        segment.last ≤ (state.checkpoint.getD (.empty, 0)).1.committed.toNat := by
  have chosen : after.Selects after.directory.active := List.mem_cons_self ..
  have visible := (ready.collectionReadPlan retry chosen).1
  have settled := retry.keepsSettledPair ready.walDirectorySettled
  have survivors : after.directory.crashImages = [state.target.pair] :=
    settled.2.trans (congrArg (fun pair => [pair]) (settled.1.symm.trans visible))
  have keeper : after.active.first = state.installed.activeFirst := by
    rw [retry.keepsActive, ready.resumed.keeper, ready.active]
  simp [WalSegmentImage.canRemove, keeper, visible, survivors, state.target.decoded,
    ready.checkpointWatermark, and_assoc]

/-- The planned retained files form an exact chain whose start is covered
by the loaded strict checkpoint. The byte accounting describes the read
suffix and allows covered files outside the plan to remain on disk. -/
theorem SegmentedWriterState.Ready.collectionSuffixBounds {directory descriptor state after}
    (ready : SegmentedWriterState.Ready directory descriptor state)
    (retry : WalSegmentCollectionRetry state.wal after) :
    let covered := (state.checkpoint.getD (.empty, 0)).1.committed.toNat
    let reads := after.readDescriptors state.target.range.watermark
    let retained := (WalSegment.concatenate reads).size
    ∃ first, first ≤ covered ∧ WalSegment.Chain state.history first reads ∧
      first * WAL.frameSize + retained = state.installed.walBytes ∧
      (state.history.length - covered) * WAL.frameSize ≤ retained := by
  intro covered reads retained
  obtain ⟨first, starts, _, chain, suffix⟩ := ready.collectionSelectsReads retry
  have loaded : state.target.range.watermark = covered := ready.checkpointWatermark
  have within := (DirectoryPublication.Bindings.walRange_accounting state.target.decoded).2.1
  rw [ready.resumed.through] at within
  have firstWithin := Nat.le_trans starts within
  have size : retained = (state.history.length - first) * WAL.frameSize := by
    change (WalSegment.concatenate (after.readDescriptors state.target.range.watermark)).size = _
    rw [suffix, WAL.encode_size, List.length_drop, Nat.mul_comm]
  refine ⟨first, loaded ▸ starts, chain, ?_, ?_⟩
  · rw [size, ready.resumed.bytes, WAL.encode_size, Nat.mul_comm WAL.frameSize,
      ← Nat.add_mul, Nat.add_sub_of_le firstWithin]
  · rw [size]
    exact Nat.mul_le_mul_right _ (Nat.sub_le_sub_left (loaded ▸ starts) _)

end DiskSession
end Alvoki.Storage
