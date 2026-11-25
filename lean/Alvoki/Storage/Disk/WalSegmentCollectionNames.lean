import Alvoki.Storage.Disk.SegmentedCollectionStep

namespace Alvoki.Storage

open WalSegmentRepair

/-- Count the canonical segment names in the complete checked listing.
Unrelated directory entries do not contribute to the count. -/
theorem WalSegmentRepair.HealthyBoundedWalReports.canonicalWalNames
    {directory owners descriptor wal pair watermark durable tail} {history : List WAL.Write}
    (raw : HealthyBoundedWalReports directory owners descriptor wal pair watermark durable tail)
    (layout : wal.ReadLayout history) :
    ((raw.entries.toList.map (·.fileName)).filterMap parseWalSegmentName).Perm (wal.segments.map WalSegment.first) := by
  have uniqueNames : ((raw.entries.toList.map (·.fileName)).filterMap parseWalSegmentName).Nodup := by
    apply raw.unique.filterMap parseWalSegmentName
    intro left right different start leftParsed other rightParsed equal
    subst other
    exact different ((parseWalSegmentName_eq_some_iff.mp leftParsed).trans
      (parseWalSegmentName_eq_some_iff.mp rightParsed).symm)
  have uniqueStarts : (wal.segments.map WalSegment.first).Nodup :=
    (layout.ordered.map WalSegment.first (fun _ _ order => Nat.ne_of_lt order.1))
  apply (List.perm_ext_iff_of_nodup uniqueNames uniqueStarts).mpr
  intro first
  rw [← raw.names first]
  exact ⟨fun member => by
      obtain ⟨name, listed, parsed⟩ := List.mem_filterMap.mp member
      exact (parseWalSegmentName_eq_some_iff.mp parsed) ▸ listed,
    fun listed => List.mem_filterMap.mpr ⟨_, listed, parseWalSegmentName_render first⟩⟩

/-- Every canonical start is a distinct natural number no greater than the
active start, so even empty seals contribute to this absolute count. -/
theorem WalSegmentImage.ReadLayout.nameCount_le {wal : WalSegmentImage} {history : List WAL.Write}
    (layout : wal.ReadLayout history) : wal.segments.length ≤ wal.active.first + 1 := by
  have distinct : (wal.segments.map WalSegment.first).Nodup :=
    layout.ordered.map WalSegment.first (fun _ _ order => Nat.ne_of_lt order.1)
  have starts : wal.segments.map WalSegment.first ⊆ List.range (wal.active.first + 1) := by
    intro first member
    obtain ⟨segment, present, rfl⟩ := List.mem_map.mp member
    apply List.mem_range.mpr
    rcases List.mem_append.mp present with sealed | active
    · have prior := (List.pairwise_append.mp layout.ordered).2.2 _ sealed _ (List.mem_singleton_self _)
      omega
    · obtain rfl := List.mem_singleton.mp active
      omega
  simpa using distinct.length_le_of_subset starts

namespace DiskSession

private theorem SegmentedWriterState.RetainedReady.sealEnd {directory descriptor} {state : SegmentedWriterState}
    (ready : state.RetainedReady directory descriptor) {segment : WalSegment} (sealed : segment ∈ state.wal.sealed) :
    segment.last ≤ state.wal.active.first :=
  ((List.pairwise_append.mp ready.layout.ordered).2.2 _ sealed _ (List.mem_singleton_self _)).2

/-- A complete successful WAL pass removes every covered positive seal.
The actual planner leaves zero-width seals at their existing addresses. -/
theorem SegmentedCollectionReport.Installs.retainedSealedNames {directory descriptor}
    {before after : SegmentedWriterState} {report : SegmentedCollectionReport directory before}
    (installed : report.Installs after) (ready : before.RetainedReady directory descriptor)
    (complete : report.offsets = before.wal.collectionOffsets) :
    after.wal.sealed = before.wal.sealed.filter fun segment =>
      decide (segment.first = segment.last ∨ before.target.range.watermark < segment.last) := by
  rw [(installed.reclaimsPlan ready complete).1]
  apply List.filter_congr
  intro segment sealed
  have last := ready.sealEnd sealed
  have forward := ready.layout.forward segment (List.mem_append_left _ sealed)
  have eligible : before.wal.Eligible segment ↔
      segment.first < segment.last ∧ segment.last ≤ before.target.range.watermark := by
    constructor
    · intro allowed
      obtain ⟨range, decoded, covered⟩ := allowed.covered before.target.pair
        (ready.walPair ▸ List.mem_cons_self ..)
      rw [before.target.decoded] at decoded
      exact ⟨allowed.sealedBeforeActive.1, (Option.some.inj decoded).symm ▸ covered⟩
    · rintro ⟨positive, covered⟩
      refine ⟨⟨positive, last⟩, ?_⟩
      intro pair chosen
      have original : pair = before.target.pair := by
        simpa [WalSegmentImage.Selects, ready.walDirectorySettled, ready.walPair] using chosen
      exact ⟨before.target.range, original.symm ▸ before.target.decoded, covered⟩
  rw [Bool.eq_iff_iff, Bool.not_eq_true', ← Bool.not_eq_true,
    WalSegmentImage.canRemove_iff, eligible, decide_eq_true_iff]
  omega

/-- Charge each surviving positive seal to its distinct final frame after
the watermark, and each remaining empty seal to its original name. The
active segment contributes one name even when it has no frames. -/
theorem SegmentedCollectionReport.Installs.retainedWalNameCount {directory descriptor}
    {before after : SegmentedWriterState} {report : SegmentedCollectionReport directory before}
    (installed : report.Installs after) (ready : before.RetainedReady directory descriptor)
    (complete : report.offsets = before.wal.collectionOffsets) :
    after.wal.segments.length ≤
      (before.wal.sealed.filter fun segment => decide (segment.first = segment.last)).length +
        (before.wal.active.first - before.target.range.watermark) + 1 := by
  let zero := fun segment : WalSegment => decide (segment.first = segment.last)
  let positive := after.wal.sealed.filter fun segment => !zero segment
  have retained := installed.retainedSealedNames ready complete
  have sameEmpty : after.wal.sealed.filter zero = before.wal.sealed.filter zero := by
    rw [retained, List.filter_filter]
    apply List.filter_congr
    intro segment _
    by_cases empty : segment.first = segment.last <;> simp [zero, empty]
  have beforeSeal (segment : WalSegment) (present : segment ∈ positive) : segment ∈ before.wal.sealed := by
    have afterSeal := (List.mem_filter.mp present).1
    rw [retained] at afterSeal
    exact (List.mem_filter.mp afterSeal).1
  have positiveWidth (segment : WalSegment) (present : segment ∈ positive) : segment.first < segment.last := by
    have forward := ready.layout.forward segment (List.mem_append_left _ (beforeSeal segment present))
    have different : segment.first ≠ segment.last := by
      simpa [zero] using (List.mem_filter.mp present).2
    omega
  have later (segment : WalSegment) (present : segment ∈ positive) :
      before.target.range.watermark < segment.last := by
    have afterSeal := (List.mem_filter.mp present).1
    rw [retained] at afterSeal
    exact (of_decide_eq_true (List.mem_filter.mp afterSeal).2).resolve_left
      (Nat.ne_of_lt (positiveWidth segment present))
  have ordered := (installed.preservesRetained ready).layout.ordered
  have byStart := (List.pairwise_append.mp ordered).1.filter (fun segment => !zero segment)
  have byEnd : positive.Pairwise (fun left right => left.last < right.last) :=
    byStart.imp_of_mem fun _ present order => Nat.lt_of_le_of_lt order.2 (positiveWidth _ present)
  have distinct : (positive.map WalSegment.last).Nodup :=
    byEnd.map WalSegment.last (fun _ _ order => Nat.ne_of_lt order)
  have ends : positive.map WalSegment.last ⊆
      List.range' (before.target.range.watermark + 1) (before.wal.active.first - before.target.range.watermark) := by
    intro endpoint member
    obtain ⟨segment, present, rfl⟩ := List.mem_map.mp member
    have high := ready.sealEnd (beforeSeal segment present)
    have low := later segment present
    exact List.mem_range'_1.mpr (by omega)
  have count : positive.length ≤ before.wal.active.first - before.target.range.watermark :=
    by simpa only [List.length_map, List.length_range'] using distinct.length_le_of_subset ends
  have parts : after.wal.sealed.length = (after.wal.sealed.filter zero).length + positive.length := by
    simpa [positive, List.countP_eq_length_filter] using
      List.length_eq_countP_add_countP zero (l := after.wal.sealed)
  rw [sameEmpty] at parts
  simp only [WalSegmentImage.segments, List.length_append, List.length_singleton, parts, zero]
  omega

/-- If the checkpoint reaches the keeper start, the pass leaves the
original empty seals and the current keeper. A namespace whose sealed
segments all have positive width therefore has exactly one WAL name. -/
theorem SegmentedCollectionReport.Installs.retainedWalNames_keeperCovered {directory descriptor}
    {before after : SegmentedWriterState} {report : SegmentedCollectionReport directory before}
    (installed : report.Installs after) (ready : before.RetainedReady directory descriptor)
    (complete : report.offsets = before.wal.collectionOffsets)
    (covered : before.wal.active.first ≤ before.target.range.watermark) :
    after.wal.segments =
      (before.wal.sealed.filter fun segment => decide (segment.first = segment.last)) ++ [before.wal.active] := by
  rw [WalSegmentImage.segments, (installed.outcome ready).2.2.1, installed.retainedSealedNames ready complete]
  congr 1
  apply List.filter_congr
  intro segment member
  have ends := Nat.le_trans (ready.sealEnd member) covered
  simp [Nat.not_lt_of_ge ends]

/-- Apply the count to the canonical names in the exact reached checked
listing. Its duplicate and namespace-agreement reports exclude extra
canonical names that the logical segment inventory did not account for. -/
theorem SegmentedCollectionReport.Installs.retainedWalNameCount_fromListing {directory descriptor}
    {before after : SegmentedWriterState} {report : SegmentedCollectionReport directory before}
    (installed : report.Installs after) (ready : before.RetainedReady directory descriptor)
    (complete : report.offsets = before.wal.collectionOffsets) {tail : ByteArray}
    (raw : HealthyBoundedWalReports directory after.owners descriptor after.wal after.target.pair
      after.target.range.watermark after.published.durable tail) :
    ((raw.entries.toList.map (·.fileName)).filterMap parseWalSegmentName).length ≤
      min (before.wal.active.first + 1)
        ((before.wal.sealed.filter fun segment => decide (segment.first = segment.last)).length +
          (before.wal.active.first - before.target.range.watermark) + 1) := by
  obtain ⟨reached, _, sameActive, _⟩ := installed.outcome ready
  have exactCount := (raw.canonicalWalNames reached.layout).length_eq
  rw [List.length_map] at exactCount
  have absolute := reached.layout.nameCount_le
  rw [sameActive] at absolute
  exact exactCount ▸ Nat.le_min.mpr ⟨absolute, installed.retainedWalNameCount ready complete⟩

/-- With positive sealed spans and a checkpoint reaching the keeper,
the next complete checked listing has only the keeper's canonical name. -/
theorem SegmentedCollectionReport.Installs.singleObservedWalName {directory descriptor}
    {before after : SegmentedWriterState} {report : SegmentedCollectionReport directory before}
    (installed : report.Installs after) (ready : before.RetainedReady directory descriptor)
    (complete : report.offsets = before.wal.collectionOffsets)
    (covered : before.wal.active.first ≤ before.target.range.watermark)
    (positive : ∀ segment ∈ before.wal.sealed, segment.first < segment.last) {tail : ByteArray}
    (raw : HealthyBoundedWalReports directory after.owners descriptor after.wal after.target.pair
      after.target.range.watermark after.published.durable tail) :
    (raw.entries.toList.map (·.fileName)).filterMap parseWalSegmentName = [before.wal.active.first] := by
  have exactNames := raw.canonicalWalNames (installed.preservesRetained ready).layout
  have noEmpty : (before.wal.sealed.filter fun segment => decide (segment.first = segment.last)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro segment member
    simp [Nat.ne_of_lt (positive segment member)]
  rw [installed.retainedWalNames_keeperCovered ready complete covered, noEmpty, List.nil_append, List.map_cons,
    List.map_nil] at exactNames
  exact exactNames.eq_singleton

end DiskSession
end Alvoki.Storage
