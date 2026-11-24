import Alvoki.Storage.Disk.SegmentedRetainedWriter
import Alvoki.Storage.Disk.WalSegmentUnlinkSchedule

namespace Alvoki.Storage

open WAL (frameSize)

/-- A sealed file's end comes from its own size. After a partial collection,
the next observed filename can be separated from this file by a gap. -/
def walCollectionEnd (first keeper : Nat) (range : MarkedWalRange) (metadata : IO.FS.Metadata) :
    Option Nat :=
  let bytes := metadata.byteSize.toNat
  let last := first + bytes / frameSize
  if (metadata.type == .file) ∧ metadata.numLinks = 1 ∧ 0 < bytes ∧ bytes % frameSize = 0 ∧
      last ≤ keeper ∧ last ≤ range.watermark then some last else none

/-- An accepted no-follow report gives a positive exact span wholly before
the keeper and covered by the strict checkpoint and marker. -/
theorem walCollectionEnd_covered {pair : DirectoryPublication.Bindings} {range : MarkedWalRange}
    (decoded : pair.walRange = some range) {first keeper last : Nat} {metadata : IO.FS.Metadata}
    (accepted : walCollectionEnd first keeper range metadata = some last) :
    metadata.type = .file ∧ metadata.numLinks = 1 ∧ last = first + metadata.byteSize.toNat / frameSize ∧
      metadata.byteSize.toNat = (last - first) * frameSize ∧
      first < last ∧ last ≤ keeper ∧ first ≠ keeper ∧ last ≤ range.watermark ∧ last ≤ range.through := by
  unfold walCollectionEnd at accepted
  dsimp only at accepted
  split at accepted
  · rename_i checked
    obtain ⟨regular, links, positive, aligned, before, covered⟩ := checked
    have kind : metadata.type = .file := by
      cases kind : metadata.type <;> first | rfl | (rw [kind] at regular; cases regular)
    cases accepted
    have exactBytes : metadata.byteSize.toNat = metadata.byteSize.toNat / frameSize * frameSize := by
      simpa only [aligned, Nat.zero_add, Nat.mul_comm] using (Nat.mod_add_div metadata.byteSize.toNat frameSize).symm
    have nonempty : first < first + metadata.byteSize.toNat / frameSize := by
      have frames : 0 < metadata.byteSize.toNat / frameSize := by
        apply Nat.pos_of_ne_zero
        intro zero
        rw [zero, Nat.zero_mul] at exactBytes
        omega
      omega
    exact ⟨kind, links, rfl, by simpa using exactBytes, nonempty, before,
      Nat.ne_of_lt (Nat.lt_of_lt_of_le nonempty before), covered,
      Nat.le_trans covered (DirectoryPublication.Bindings.walRange_accounting decoded).2.1⟩
  · contradiction

/-- Filter the sorted canonical inventory using the settled pair and the
same no-follow reports. The keeper is skipped before any size lookup. -/
def OpenPathReadReports.walCollectionOffsets (reports : OpenPathReadReports) (directory : DiskDirectory)
    (offsets : List Nat) (keeper : Nat) (pair : DirectoryPublication.Bindings) : List Nat :=
  match pair.walRange with
  | none => []
  | some range => offsets.filter fun first =>
    if first = keeper then false
    else
      match reports.lstat (directory.file (.walSegment first)) with
      | .ok metadata => (walCollectionEnd first keeper range metadata).isSome
      | .error _ => false

/-- The exact stored payload of a chain member has the length given by its
absolute endpoints. This fact survives unlinking other members. -/
theorem WalSegment.Chain.member_byteSize {history : List WAL.Write} {first : Nat} {segments : List WalSegment}
    (chain : Chain history first segments) {segment : WalSegment} (member : segment ∈ segments) :
    segment.bytes.size = (segment.last - segment.first) * frameSize := by
  have startsWithin {start : Nat} {rest : List WalSegment} (tail : Chain history start rest) :
      start ≤ history.length := by
    induction tail with
    | endOfHistory => exact Nat.le_refl _
    | cons ordered _ _ _ ih => exact Nat.le_trans ordered ih
  induction chain with
  | endOfHistory => simp at member
  | @cons head rest _ _ payload tail ih =>
    rcases List.mem_cons.mp member with same | later
    · subst segment
      have count : head.last - head.first ≤ (history.drop head.first).length := by
        rw [List.length_drop]
        exact Nat.sub_le_sub_right (startsWithin tail) head.first
      rw [payload, WAL.encode_size, List.length_take, Nat.min_eq_left count, Nat.mul_comm]
    · exact ih later

private theorem walCollectionEnd_isSome {segment : WalSegment} {keeper : Nat} {range : MarkedWalRange}
    {metadata : IO.FS.Metadata} (ordered : segment.first ≤ segment.last)
    (kind : metadata.type = .file) (links : metadata.numLinks = 1)
    (extent : metadata.byteSize.toNat = (segment.last - segment.first) * frameSize) :
    (walCollectionEnd segment.first keeper range metadata).isSome =
      decide (segment.first < segment.last ∧ segment.last ≤ keeper ∧ segment.last ≤ range.watermark) := by
  have frames := Nat.mul_div_cancel (segment.last - segment.first) (show 0 < frameSize by decide)
  have endpoint : segment.first + metadata.byteSize.toNat / frameSize = segment.last := by
    rw [extent, frames, Nat.add_sub_of_le ordered]
  have positive : 0 < metadata.byteSize.toNat ↔ segment.first < segment.last := by
    rw [extent, Nat.mul_pos_iff_of_pos_right (show 0 < frameSize by decide), Nat.sub_pos_iff_lt]
  have regular : (metadata.type == .file) = true := by rw [kind]; rfl
  have aligned : metadata.byteSize.toNat % frameSize = 0 := by rw [extent, Nat.mul_mod_left]
  simp only [walCollectionEnd, regular, true_and, links, aligned, endpoint, positive]
  split <;> simp_all

namespace WalSegmentRepair

/-- A complete held inventory, with true physical sizes for the exact
immutable payloads, yields the model's entire unlink plan. An earlier
collection may have removed arbitrary covered sealed names. -/
theorem HealthyBoundedWalReports.collectionOffsets_exact {directory owners descriptor wal pair watermark durable tail}
    (raw : HealthyBoundedWalReports directory owners descriptor wal pair watermark durable tail)
    {history : List WAL.Write} (layout : wal.ReadLayout history)
    (visible : wal.directory.active = pair) (settled : wal.directory.crashImages = [pair])
    {range : MarkedWalRange} (decoded : pair.walRange = some range)
    (physical : ∀ segment ∈ wal.sealed, ∀ metadata,
      raw.reports.lstat (directory.file (.walSegment segment.first)) = .ok metadata →
        metadata.byteSize.toNat = segment.bytes.size)
    (spans : ∀ segment ∈ wal.sealed, segment.bytes.size = (segment.last - segment.first) * frameSize) :
    (raw.reports.walSegmentOffsets directory (raw.entries.toList.map (·.fileName))).map
        (fun offsets => raw.reports.walCollectionOffsets directory offsets wal.active.first pair) =
      .ok wal.collectionOffsets := by
  rw [raw.scan layout]
  simp only [Except.map, Except.ok.injEq]
  have test (segment : WalSegment) (member : segment ∈ wal.sealed) :
      (if segment.first = wal.active.first then false
       else match raw.reports.lstat (directory.file (.walSegment segment.first)) with
         | .ok metadata => (walCollectionEnd segment.first wal.active.first range metadata).isSome
         | .error _ => false) = wal.canRemove segment := by
    have ordered := List.pairwise_append.mp layout.ordered
    have before := ordered.2.2 segment member _ List.mem_cons_self
    have present := List.mem_map_of_mem (f := WalSegment.first) (List.mem_append_left [wal.active] member)
    obtain ⟨metadata, observed, kind, links⟩ := raw.regular segment.first present
    have forward := layout.forward segment (List.mem_append_left _ member)
    have extent := (physical segment member metadata observed).trans (spans segment member)
    have permitted := walCollectionEnd_isSome forward kind links extent (keeper := wal.active.first) (range := range)
    simp [Nat.ne_of_lt before.1, observed, permitted, WalSegmentImage.canRemove, visible, settled, decoded,
      Bool.and_assoc]
  unfold OpenPathReadReports.walCollectionOffsets WalSegmentImage.collectionOffsets
  rw [decoded]
  simp only [WalSegmentImage.segments, List.map_append, List.map_cons, List.map_nil,
    List.filter_append, List.filter_cons, Bool.false_eq_true, ↓reduceIte, List.filter_nil,
    List.append_nil]
  rw [List.filter_map]
  congr 1
  exact List.filter_congr test

end WalSegmentRepair

namespace DiskSession

/-- A settled writer authenticates the strict pair, and its original chain
fixes the lengths of the sealed payloads that survive earlier unlinks. The
fresh held observations supply the physical size of each surviving file. -/
theorem SegmentedWriterState.Ready.collectionOffsets_exact {directory descriptor state after tail}
    (ready : SegmentedWriterState.Ready directory descriptor state)
    (retry : WalSegmentCollectionRetry state.wal after)
    (raw : WalSegmentRepair.HealthyBoundedWalReports directory state.owners descriptor after state.target.pair
      state.target.range.watermark state.published.durable tail)
    (physical : ∀ segment ∈ after.sealed, ∀ metadata,
      raw.reports.lstat (directory.file (.walSegment segment.first)) = .ok metadata →
        metadata.byteSize.toNat = segment.bytes.size) :
    (raw.reports.walSegmentOffsets directory (raw.entries.toList.map (·.fileName))).map
        (fun offsets => raw.reports.walCollectionOffsets directory offsets state.installed.activeFirst state.target.pair) =
      .ok after.collectionOffsets := by
  have visible := (ready.collectionReadPlan retry (pair := after.directory.active) (List.mem_cons_self ..)).1
  have ⟨samePair, settled⟩ := retry.keepsSettledPair ready.walDirectorySettled
  rw [← samePair, visible] at settled
  have keeper : after.active.first = state.installed.activeFirst := by
    rw [retry.keepsActive, ready.resumed.keeper, ready.active]
  rw [← keeper]
  exact raw.collectionOffsets_exact (retry.readLayout ready.layout) visible settled state.target.decoded physical
    (fun _ member => ready.chain.member_byteSize (List.mem_append_left _ (retry.sealedSublist.subset member)))

end DiskSession
end Alvoki.Storage
