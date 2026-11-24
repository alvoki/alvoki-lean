import Alvoki.Storage.Disk.WalSegmentCheckpointPublication

namespace Alvoki.Storage.CheckpointPublication

open Manifest
open WAL (frameSize)

private theorem coveredAtHistoryEnd {image : WalSegmentImage}
    {history : List WAL.Write} (layout : image.ReadLayout history) :
    image.afterWatermark history.length = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro segment included
  change segment ∈ (image.sealed ++ [image.active]).filter (fun item => decide (history.length < item.last)) at included
  obtain ⟨present, needed⟩ := List.mem_filter.mp included
  have needed : history.length < segment.last := of_decide_eq_true needed
  have activeInSegments : image.active ∈ image.segments := by simp [WalSegmentImage.segments]
  have endsByKeeper : segment.last ≤ image.active.last := by
    rcases List.mem_append.mp present with sealed | active
    · have endsBeforeKeeper := (List.pairwise_append.mp layout.ordered).2.2
        segment sealed image.active (List.mem_singleton_self _)
      exact Nat.le_trans endsBeforeKeeper.2 (layout.forward image.active activeInSegments)
    · obtain rfl : segment = image.active := List.mem_singleton.mp active
      exact Nat.le_refl _
  rw [layout.activeEnd] at endsByKeeper
  exact Nat.not_lt_of_ge endsByKeeper needed

private theorem fullCheckpointCoverage {image : WalSegmentImage} {history : List WAL.Write}
    (layout : image.ReadLayout history) {pair : DirectoryPublication.Bindings}
    (decoded : pair.walRange = some ⟨history.length, history.length⟩) :
    ∃ range first,
      pair.walRange = some range ∧ first ≤ range.watermark ∧ range.through ≤ history.length ∧
        WalSegment.Chain history first (image.afterWatermark range.watermark) := by
  refine ⟨_, history.length, decoded, Nat.le_refl _, Nat.le_refl _, ?_⟩
  rw [coveredAtHistoryEnd layout]
  exact .endOfHistory

/-- Checkpoint publication can preserve the exact selected WAL suffix
after eligible files have been collected. The old pair retains its
previous proof, and the new pair's checkpoint covers the entire history.
The availability of covered segment names is irrelevant in either case. -/
theorem Image.segmentedCheckpointView_retained {published : Image} {before : WalSegmentImage}
    {history : List WAL.Write} (layout : before.ReadLayout history) (valid : before.Valid history)
    (choices : ∀ pair, (published.segmentedCheckpointView before).Selects pair →
      pair = before.directory.active ∨ pair.walRange = some ⟨history.length, history.length⟩) :
    let after := published.segmentedCheckpointView before
    after.ReadLayout history ∧ after.Valid history := by
  intro after
  have afterLayout : after.ReadLayout history :=
    ⟨layout.ordered, layout.forward, layout.activeEnd, layout.activeBytes⟩
  refine ⟨afterLayout, ?_⟩
  intro pair selected
  rcases choices pair selected with rfl | covered
  · exact valid before.directory.active (List.mem_cons_self ..)
  · exact fullCheckpointCoverage afterLayout covered

/-- A newly settled strict checkpoint covers all acknowledged frames.
Its exact metadata pair makes the current segment the sole planned WAL
read, even when covered segment names have gaps. -/
theorem Image.segmentedCheckpointView_settledRetained
    {published : Image} {before : WalSegmentImage} {history : List WAL.Write} (layout : before.ReadLayout history)
    (marker : before.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64))
    (walFits : (WAL.encode history).size < UInt64.size)
    {manifest : ByteArray} {metadata : IntegrityCheckpoint}
    (settled : published.manifest = .settled (some manifest))
    (decoded : IntegrityCheckpoint.decode manifest = .ok metadata)
    (watermark : metadata.header.committed.toNat = history.length) :
    let after := published.segmentedCheckpointView before
    after.directory.active = ⟨some manifest, before.directory.active.walBoundary⟩ ∧
    after.directory.crashImages = [after.directory.active] ∧
    published.manifest = after.directory.project .manifest ∧
    after.directory.active.walRange = some ⟨history.length, history.length⟩ ∧
    after.ReadLayout history ∧ after.Valid history ∧ after.readDescriptors history.length = [before.active] := by
  intro after
  have active : after.directory.active = ⟨some manifest, before.directory.active.walBoundary⟩ := by
    simp [after, Image.segmentedCheckpointView, Image.markedReopenImage, settled, Publication.Image.settled]
  have crashes : after.directory.crashImages = [after.directory.active] := by
    simp [after, Image.segmentedCheckpointView, Image.markedReopenImage, settled, Publication.Image.settled]
  have projected : published.manifest = after.directory.project .manifest := by
    simp [after, Image.segmentedCheckpointView, Image.markedReopenImage, settled, Publication.Image.settled,
      DirectoryPublication.Image.project, DirectoryPublication.Bindings.get]
  have checkpoint : selectedCheckpointWatermark after.directory.active.manifest = some history.length := by
    rw [active]
    exact selectedCheckpointWatermark_present_iff.mpr ⟨metadata, decoded, watermark⟩
  have markerSize : (WAL.encode history).size.toUInt64.toNat = history.length * frameSize := by
    rw [UInt64.toNat_ofNat_of_lt' walFits, WAL.encode_size, Nat.mul_comm]
  have range : after.directory.active.walRange = some ⟨history.length, history.length⟩ :=
    walRange_of_reports checkpoint (by rw [active]; exact marker)
      (WAL.Boundary.decode_encode _) markerSize (Nat.le_refl _)
  have afterLayout : after.ReadLayout history :=
    ⟨layout.ordered, layout.forward, layout.activeEnd, layout.activeBytes⟩
  refine ⟨active, crashes, projected, range, afterLayout, ?_, ?_⟩
  · intro pair selected
    change pair ∈ after.directory.active :: after.directory.crashImages at selected
    rw [crashes] at selected
    obtain rfl : pair = after.directory.active := by simpa using selected
    exact fullCheckpointCoverage afterLayout range
  · rw [WalSegmentImage.readDescriptors, afterLayout.activeEnd, ite_eq_right (Nat.lt_irrefl _)]
    rfl

end Alvoki.Storage.CheckpointPublication
