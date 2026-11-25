import Alvoki.Storage.Disk.SegmentedCollectionStep
import Alvoki.Storage.Disk.WalSegmentCachedExtentReports

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open WAL (frameSize)

private theorem concatenate_append (left right : List WalSegment) :
    WalSegment.concatenate (left ++ right) = WalSegment.concatenate left ++ WalSegment.concatenate right := by
  induction left with
  | nil => simp [WalSegment.concatenate]
  | cons _ _ ih => simp [WalSegment.concatenate, ih, ByteArray.append_assoc]

private theorem concatenate_filter_empty (segments : List WalSegment) (keep : WalSegment → Bool)
    (empty : ∀ segment ∈ segments, keep segment = false → segment.bytes = ByteArray.empty) :
    WalSegment.concatenate (segments.filter keep) = WalSegment.concatenate segments := by
  induction segments with
  | nil => rfl
  | cons segment rest ih =>
    have tail := ih (fun old member => empty old (List.mem_cons_of_mem _ member))
    cases kept : keep segment with
    | false =>
      simp [kept, WalSegment.concatenate, empty segment List.mem_cons_self kept, tail]
    | true => simp [kept, WalSegment.concatenate, tail]

private theorem selectedBytes_concat (segments : List WalSegment) :
    walSegmentPayloadBytes (segments.map (fun segment => (segment.first, segment.bytes))) =
      WalSegment.concatenate segments := by
  induction segments with
  | nil => rfl
  | cons segment rest ih =>
    change segment.bytes ++ walSegmentPayloadBytes _ = segment.bytes ++ WalSegment.concatenate rest
    rw [ih]

private theorem collectedPayload_selected {directory : DiskDirectory} {before after : SegmentedWriterState}
    {report : SegmentedCollectionReport directory before} (installed : report.Installs after)
    {descriptor : Nat} (ready : before.RetainedReady directory descriptor)
    (complete : report.offsets = before.wal.collectionOffsets) :
    WalSegment.concatenate after.wal.segments =
      WalSegment.concatenate (after.wal.readDescriptors before.target.range.watermark) := by
  let watermark := before.target.range.watermark
  have retained := (installed.reclaimsPlan ready complete).1
  obtain ⟨nextReady, _, _, _, _, _, _, _⟩ := installed.outcome ready
  have coveredEmpty (segment : WalSegment) (member : segment ∈ after.wal.sealed)
      (covered : segment.last ≤ watermark) : segment.bytes = ByteArray.empty := by
    rw [retained] at member
    obtain ⟨present, kept⟩ := List.mem_filter.mp member
    have earlier : segment.last ≤ before.wal.active.first :=
      (List.pairwise_append.mp ready.layout.ordered).2.2 _ present _ (by simp) |>.2
    by_cases nonempty : segment.first < segment.last
    · have eligible : before.wal.Eligible segment := ⟨⟨nonempty, earlier⟩, fun pair chosen => by
        have current : pair = before.wal.directory.active := by
          simpa [WalSegmentImage.Selects, ready.walDirectorySettled] using chosen
        rw [current, ready.walPair]
        exact ⟨before.target.range, before.target.decoded, covered⟩⟩
      simp [WalSegmentImage.canRemove_iff.mpr eligible] at kept
    · rw [← ByteArray.size_eq_zero_iff, ready.spans _ present]
      rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_gt nonempty), Nat.zero_mul]
  by_cases needed : watermark < after.wal.active.last
  · have sameSealed := concatenate_filter_empty after.wal.sealed (fun segment => decide (watermark < segment.last))
      (fun segment member rejected => coveredEmpty segment member (by simpa using rejected))
    simp [WalSegmentImage.readDescriptors, WalSegmentImage.afterWatermark, WalSegmentImage.segments, needed,
      watermark, List.filter_append, concatenate_append, sameSealed]
  · have empty := concatenate_filter_empty after.wal.sealed (fun _ => false) (fun segment member _ => by
      apply coveredEmpty segment member
      have earlier : segment.last ≤ after.wal.active.first :=
        (List.pairwise_append.mp nextReady.layout.ordered).2.2 _ member _ (by simp) |>.2
      have forward := nextReady.layout.forward after.wal.active (List.mem_append_right _ (by simp))
      omega)
    have none : after.wal.sealed.filter (fun _ => false) = [] := by simp
    rw [none, WalSegment.concatenate] at empty
    simp [WalSegmentImage.readDescriptors, WalSegmentImage.segments, needed, watermark, concatenate_append,
      ← empty]

/-- When the checkpoint covers the complete marked history, the remaining
named WAL payload is exactly the active segment. Empty sealed segments can
contribute names, with zero payload. -/
theorem SegmentedCollectionReport.Installs.collectedWalPayload_checkpointCovered
    {directory descriptor} {before after : SegmentedWriterState}
    {report : SegmentedCollectionReport directory before} (installed : report.Installs after)
    (ready : before.RetainedReady directory descriptor) (complete : report.offsets = before.wal.collectionOffsets)
    (covered : before.target.range.through = before.target.range.watermark) :
    WalSegment.concatenate after.wal.segments = before.wal.active.bytes := by
  obtain ⟨nextReady, _, keeper, _, _, _, _, _⟩ := installed.outcome ready
  have keeperEnd : after.wal.active.last = before.target.range.watermark := by
    calc
      after.wal.active.last = after.history.length := nextReady.layout.activeEnd
      _ = before.history.length := congrArg List.length installed.history
      _ = before.target.range.through := ready.resumed.through.symm
      _ = before.target.range.watermark := covered
  rw [collectedPayload_selected installed ready complete, WalSegmentImage.readDescriptors, keeperEnd,
    ite_eq_right (Nat.lt_irrefl _), keeper]
  simp [WalSegment.concatenate]

/-- After a healthy complete collection, the ordered payload under the
remaining WAL names equals the selected recovery payload. A later healthy
cached read of the same marker returns that exact payload. -/
theorem SegmentedCollectionReport.Installs.collectedWalPayload
    {directory : DiskDirectory} {before after : SegmentedWriterState}
    {report : SegmentedCollectionReport directory before} (installed : report.Installs after)
    {descriptor : Nat} (ready : before.RetainedReady directory descriptor)
    (complete : report.offsets = before.wal.collectionOffsets) :
    ∃ first, first ≤ before.target.range.watermark ∧
      let bytes := WalSegment.concatenate after.wal.segments
      bytes = WAL.encode (before.history.drop first) ∧
      bytes.size = (before.target.range.through - first) * frameSize ∧
      (∀ cap, (∀ segment ∈ after.wal.segments, segment.last - segment.first ≤ cap) →
        bytes.size ≤ (before.target.range.through - before.target.range.watermark + cap) * frameSize) ∧
      ∀ {owners nextDescriptor tail}
        (raw : HealthyBoundedWalReports directory owners nextDescriptor after.wal before.target.pair
          before.target.range.watermark after.published.durable tail)
        (cached : CachedWalFileReports directory raw.reports after.wal before.target.range.watermark tail)
        {count : UInt64} (_absolute : count.toNat = before.target.range.through * frameSize) (initial : FileImage),
        ∃ reads, (readSelectedWithCachedExtents directory before.target.range.watermark count
          (fun path => liftExcept (raw.list path))
          (fun path => liftExcept (.ok (raw.reports.lstat path) : Except IO.Error _))
          (fun path size => liftExcept (cached.readSeal path size))
          (fun path size physical => liftExcept (cached.readKeeper path size physical)) :
            EStateM IO.Error FileImage (WalSegmentMarkerReads × Nat)) initial =
          .ok (reads, (after.wal.active.bytes ++ tail).size) initial ∧
        walSegmentPayloadBytes reads.files = bytes := by
  obtain ⟨nextReady, sameDirectory, _, _, _, _, _, _⟩ := installed.outcome ready
  have history := installed.history
  have atEnd : before.target.range.through = after.history.length := history.symm ▸ ready.resumed.through
  have chosen : after.wal.Selects before.target.pair := by
    rw [WalSegmentImage.Selects, sameDirectory, ready.walPair]
    exact List.mem_cons_self
  obtain ⟨first, begins, through, addresses, chain, payload⟩ :=
    nextReady.layout.selects nextReady.valid chosen before.target.decoded
  have equals := collectedPayload_selected installed ready complete
  have size : (WalSegment.concatenate after.wal.segments).size =
      (before.target.range.through - first) * frameSize := by
    rw [equals, payload, WAL.encode_size, List.length_drop, ← atEnd, Nat.mul_comm]
  refine ⟨first, begins, equals.trans (payload.trans (congrArg (fun history => WAL.encode (history.drop first)) history)),
    size, ?_, ?_⟩
  · intro cap capped
    obtain ⟨seals, ends⟩ := after.wal.readDescriptors_endsActive before.target.range.watermark
    cases selected : after.wal.readDescriptors before.target.range.watermark with
    | nil => simp [selected] at ends
    | cons head rest =>
      have headMember : head ∈ after.wal.readDescriptors before.target.range.watermark := selected ▸ List.mem_cons_self
      have headStart : first = head.first := by
        rw [selected] at chain
        cases chain
        rfl
      have lead : head ∈ after.wal.segments ∧ before.target.range.watermark ≤ head.last := by
        unfold WalSegmentImage.readDescriptors at headMember
        split at headMember
        · obtain ⟨member, newer⟩ := List.mem_filter.mp headMember
          exact ⟨member, Nat.le_of_lt (of_decide_eq_true newer)⟩
        · have headEq := List.mem_singleton.mp headMember
          have covered := (DirectoryPublication.Bindings.walRange_accounting before.target.decoded).2.1
          exact ⟨headEq ▸ List.mem_append_right _ (by simp),
            by rw [headEq, nextReady.layout.activeEnd, ← atEnd]; exact covered⟩
      have width := capped head lead.1
      rw [size]
      apply Nat.mul_le_mul_right
      omega
  · intro owners nextDescriptor tail raw cached count absolute initial
    let reads : WalSegmentMarkerReads :=
      ⟨(after.wal.readDescriptors before.target.range.watermark).map (fun segment => (segment.first, segment.bytes)), []⟩
    refine ⟨reads, ?_, (selectedBytes_concat _).trans equals.symm⟩
    have covered := (DirectoryPublication.Bindings.walRange_accounting before.target.decoded).2.1
    rw [raw.readSelectedCached cached nextReady.layout nextReady.valid chosen before.target.decoded rfl atEnd absolute,
      readSelectedWithPrefix_liftReports, raw.readSelectedBounded nextReady.layout atEnd covered absolute addresses]
    rfl

end Alvoki.Storage.DiskSession
