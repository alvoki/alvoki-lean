import Alvoki.Storage.Disk.SegmentedCollectionReadPlan
import Alvoki.Storage.Disk.WalSegmentBoundedOpenReports
import Alvoki.Storage.Disk.WalSegmentPathIdentity

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

private theorem readDescriptorMember {image : WalSegmentImage} {watermark : Nat} {segment : WalSegment}
    (selected : segment ∈ image.readDescriptors watermark) : segment ∈ image.segments := by
  unfold WalSegmentImage.readDescriptors at selected
  split at selected
  · exact (List.mem_filter.mp selected).1
  · exact List.mem_append_right _ selected

/-- A healthy observation under the current lock reads the exact strict
checkpoint and the same marker after collection. The canonical, private
paths selected by the bounded worker still give the exact contiguous read
suffix, even when prior covered segment names are missing. -/
theorem SegmentedWriterState.Ready.collectionReadsBounded {directory descriptor state after}
    (ready : SegmentedWriterState.Ready directory descriptor state)
    (retry : WalSegmentCollectionRetry state.wal after) {readerOwners readerDescriptor tail}
    (raw : HealthyBoundedWalReports directory readerOwners readerDescriptor after after.directory.active
      state.target.range.watermark state.published.durable tail) :
    let inventory : LockedWalSegmentInventory directory :=
      ⟨readerOwners, readerDescriptor, raw.held, raw.entries.toList.map (·.fileName), raw.reports⟩
    let selected := after.readDescriptors state.target.range.watermark
    ∃ first marker count,
      first ≤ state.target.range.watermark ∧
      inventory.offsets = .ok (after.segments.map WalSegment.first) ∧
      selectWalSegmentReads (after.segments.map WalSegment.first) state.target.range.watermark =
        some (first, selected.map WalSegment.first) ∧
      (∀ segment ∈ selected, renderWalSegmentName segment.first ∈ inventory.names ∧
        ∃ metadata, inventory.reports.lstat (directory.file (.walSegment segment.first)) = .ok metadata ∧
          metadata.type = .file ∧ metadata.numLinks = 1) ∧
      (selected.map (fun segment => directory.file (.walSegment segment.first))).Nodup ∧
      readIntegrityCheckpoint (raw.reports.readOptional (directory.file .manifest))
        (fun generation index => raw.reports.readBin (directory.file (.run generation index)))
        (fun result => result.mapError IO.userError) = .ok state.checkpoint ∧
      raw.reports.readOptional (directory.file .walBoundary) = .ok (some marker) ∧
      WAL.Boundary.decode marker = .ok count ∧ count.toNat = state.installed.walBytes ∧
      readSelectedWithPrefix directory state.target.range.watermark count raw.list
        (fun path => .ok (raw.reports.lstat path)) raw.reports.readBin raw.readPrefix =
        .ok (⟨selected.map (fun segment => (segment.first, segment.bytes)), []⟩,
          (after.active.bytes ++ tail).size) ∧
      WalSegment.concatenate selected = WAL.encode (state.history.drop first) := by
  intro inventory selected
  have chosen : after.Selects after.directory.active := List.mem_cons_self ..
  obtain ⟨samePair, _, sameReads, strict⟩ := ready.collectionReadPlan retry chosen
  have decoded : after.directory.active.walRange = some state.target.range := samePair.symm ▸ state.target.decoded
  obtain ⟨_, covered, marker, count, visible, readCount, absolute⟩ :=
    DirectoryPublication.Bindings.walRange_accounting decoded
  have installedCount : count.toNat = state.installed.walBytes := by
    rw [absolute, ready.resumed.through, ready.resumed.bytes, WAL.encode_size, Nat.mul_comm]
  obtain ⟨first, starts, planned, chain, suffix⟩ := ready.collectionSelectsReads retry
  have exactPlan : selectWalSegmentReads (after.segments.map WalSegment.first) state.target.range.watermark =
      some (first, (after.readDescriptors state.target.range.watermark).map WalSegment.first) := by
    simpa only [sameReads] using planned
  have layout := retry.readLayout ready.layout
  refine ⟨first, marker, count, starts, raw.scan layout, exactPlan, ?_, chain.filesNodup directory,
    raw.readCheckpoint strict, by rw [raw.marker, visible], readCount, installedCount, ?_, suffix⟩
  · intro segment member
    have present : segment.first ∈ after.segments.map WalSegment.first :=
      List.mem_map_of_mem (readDescriptorMember member)
    exact ⟨(raw.names segment.first).mpr present, raw.regular segment.first present⟩
  · exact raw.readSelectedBounded layout ready.resumed.through covered absolute exactPlan

end Alvoki.Storage.DiskSession
