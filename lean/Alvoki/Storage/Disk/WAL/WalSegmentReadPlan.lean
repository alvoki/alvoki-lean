import Alvoki.Storage.Disk.Proofs.Collection.WalSegmentCollection
import Alvoki.Storage.Disk.WAL.WalSegmentInventory
import Alvoki.Storage.Disk.Proofs.WAL.WalSegmentRecovery

namespace Alvoki.Storage

def WalSegmentImage.segments (image : WalSegmentImage) : List WalSegment := image.sealed ++ [image.active]

def WalSegmentImage.readDescriptors (image : WalSegmentImage) (watermark : Nat) : List WalSegment :=
  if watermark < image.active.last then image.afterWatermark watermark else [image.active]

/-- The bounded reader can select only seals from the original WAL. -/
theorem WalSegmentImage.selectedSeals_subset {wal : WalSegmentImage} {watermark : Nat}
    {sealed : List WalSegment} {keeper : WalSegment}
    (descriptors : sealed ++ [keeper] = wal.readDescriptors watermark) : sealed ⊆ wal.sealed := by
  intro segment chosen
  rw [WalSegmentImage.readDescriptors] at descriptors
  split at descriptors
  · rename_i covered
    have fromSeals : sealed = wal.sealed.filter (fun s => decide (watermark < s.last)) :=
      (List.append_singleton_inj.mp (by simpa [WalSegmentImage.afterWatermark, WalSegmentImage.segments,
        List.filter_append, covered] using descriptors)).1
    rw [fromSeals] at chosen
    exact (List.mem_filter.mp chosen).1
  · have empty := (List.append_singleton_inj.mp (show sealed ++ [keeper] = [] ++ [wal.active] from descriptors)).1
    simp [empty] at chosen

/-- Available descriptors are increasing and nonoverlapping. Payloads of
covered older segments need no validation here. The active descriptor
records the complete encoded frames, separately from a possible torn tail. -/
structure WalSegmentImage.ReadLayout (image : WalSegmentImage) (history : List WAL.Write) : Prop where
  ordered : image.segments.Pairwise (fun left right => left.first < right.first ∧ left.last ≤ right.first)
  forward : ∀ segment ∈ image.segments, segment.first ≤ segment.last
  activeEnd : image.active.last = history.length
  activeBytes : image.active.bytes = WAL.encode (history.drop image.active.first)

private theorem follows_or_same {segments : List WalSegment}
    (ordered : segments.Pairwise (fun left right => left.first < right.first ∧ left.last ≤ right.first))
    {left right : WalSegment} (first : left ∈ segments) (second : right ∈ segments)
    (ascending : left.first ≤ right.first) : left = right ∨ left.last ≤ right.first := by
  induction segments with
  | nil => simp at first
  | cons segment rest ih =>
    obtain ⟨before, remaining⟩ := List.pairwise_cons.mp ordered
    rcases List.mem_cons.mp first with rfl | earlier <;> rcases List.mem_cons.mp second with rfl | later
    · exact .inl rfl
    · exact .inr (before _ later).2
    · exact False.elim (Nat.not_le_of_gt (before _ earlier).1 ascending)
    · exact ih remaining earlier later

private theorem select_exact_suffix {segments : List WalSegment} {watermark : Nat} {first : WalSegment}
    {rest : List WalSegment}
    (ordered : segments.Pairwise (fun left right => left.first < right.first ∧ left.last ≤ right.first))
    (forward : ∀ segment ∈ segments, segment.first ≤ segment.last)
    (startsBefore : first.first ≤ watermark)
    (required : segments.filter (fun segment => decide (watermark < segment.last)) = first :: rest) :
    selectWalSegmentReads (segments.map (·.first)) watermark = some (first.first, (first :: rest).map (·.first)) := by
  let needed := fun segment : WalSegment => decide (watermark < segment.last)
  have firstNeeded : first ∈ segments.filter needed := required.symm ▸ List.mem_cons_self ..
  obtain ⟨firstMember, firstReaches⟩ := List.mem_filter.mp firstNeeded
  have greaterReaches : ∀ segment ∈ segments, first.first ≤ segment.first → watermark < segment.last := by
    intro segment member starts
    rcases follows_or_same ordered firstMember member starts with rfl | separated
    · exact of_decide_eq_true firstReaches
    · exact Nat.lt_of_lt_of_le (of_decide_eq_true firstReaches) (Nat.le_trans separated (forward segment member))
  have requiredStartsAfter : ∀ segment ∈ segments, watermark < segment.last → first.first ≤ segment.first := by
    intro segment member reaches
    have requiredMember : segment ∈ segments.filter needed := List.mem_filter.mpr ⟨member, decide_eq_true reaches⟩
    rw [show segments.filter needed = first :: rest from required] at requiredMember
    have orderedRequired := ordered.filter needed
    rw [show segments.filter needed = first :: rest from required] at orderedRequired
    rcases List.mem_cons.mp requiredMember with rfl | later
    · exact Nat.le_refl _
    · exact Nat.le_of_lt ((List.pairwise_cons.mp orderedRequired).1 segment later).1
  have best : ((segments.map (·.first)).filter (fun offset => decide (offset ≤ watermark))).max? =
      some first.first := by
    apply List.max?_eq_some_iff.mpr
    refine ⟨List.mem_filter.mpr ⟨List.mem_map.mpr ⟨first, firstMember, rfl⟩, decide_eq_true startsBefore⟩, ?_⟩
    intro offset included
    obtain ⟨member, covers⟩ := List.mem_filter.mp included
    obtain ⟨segment, stored, rfl⟩ := List.mem_map.mp member
    apply Nat.le_of_not_gt
    intro newer
    rcases follows_or_same ordered firstMember stored (Nat.le_of_lt newer) with rfl | separated
    · exact Nat.lt_irrefl _ newer
    · exact Nat.not_lt_of_ge (Nat.le_trans separated (of_decide_eq_true covers)) (of_decide_eq_true firstReaches)
  have orderedReads : (segments.map (·.first)).filter (fun start => decide (first.first ≤ start)) =
      (first :: rest).map (·.first) := by
    rw [List.filter_map, ← required]
    apply congrArg (List.map WalSegment.first)
    apply List.filter_congr
    intro segment member
    change decide (first.first ≤ segment.first) = decide (watermark < segment.last)
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
    exact ⟨greaterReaches segment member, requiredStartsAfter segment member⟩
  simp [selectWalSegmentReads, best, orderedReads, Bind.bind, Option.bind, Pure.pure]

private theorem WalSegmentImage.ReadLayout.beforeActive {image : WalSegmentImage} {history : List WAL.Write}
    (layout : image.ReadLayout history) {segment : WalSegment} (old : segment ∈ image.sealed) :
    segment.first < image.active.first := by
  have ordered := List.pairwise_append.mp layout.ordered
  exact (ordered.2.2 segment old image.active (List.mem_singleton_self _)).1

private theorem WalSegmentImage.ReadLayout.selectActive {image : WalSegmentImage} {history : List WAL.Write}
    (layout : image.ReadLayout history) {watermark : Nat} (covered : image.active.first ≤ watermark) :
    selectWalSegmentReads (image.segments.map (·.first)) watermark = some (image.active.first, [image.active.first]) := by
  have best : ((image.segments.map (·.first)).filter (fun offset => decide (offset ≤ watermark))).max? =
      some image.active.first := by
    apply List.max?_eq_some_iff.mpr
    refine ⟨?_, ?_⟩
    · exact List.mem_filter.mpr ⟨List.mem_map.mpr ⟨image.active, List.mem_append_right _ (by simp), rfl⟩,
        decide_eq_true covered⟩
    · intro offset selected
      obtain ⟨segment, stored, rfl⟩ := List.mem_map.mp (List.mem_filter.mp selected).1
      rcases List.mem_append.mp stored with old | active
      · exact Nat.le_of_lt (layout.beforeActive old)
      · exact List.mem_singleton.mp active ▸ Nat.le_refl _
  have olderGone : image.sealed.filter (fun segment => decide (image.active.first ≤ segment.first)) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro segment selected
    obtain ⟨old, tooLate⟩ := List.mem_filter.mp selected
    exact Nat.not_le_of_gt (layout.beforeActive old) (of_decide_eq_true tooLate)
  unfold selectWalSegmentReads
  rw [best]
  change some (image.active.first, (image.segments.map WalSegment.first).filter
    (fun offset => decide (image.active.first ≤ offset))) = some (image.active.first, [image.active.first])
  rw [List.filter_map]
  simp [WalSegmentImage.segments, List.filter_append, Function.comp_def, olderGone]

/-- Accepted layouts yield a contiguous requested chain and exact bytes.
At a checkpoint equal to the physical end the only requested address is
the active file, which can be the empty successor of a rotation. -/
theorem WalSegmentImage.ReadLayout.selects {image : WalSegmentImage} {history : List WAL.Write}
    (layout : image.ReadLayout history) (valid : image.Valid history)
    {pair : DirectoryPublication.Bindings} (chosen : image.Selects pair)
    {range : MarkedWalRange} (decoded : pair.walRange = some range) :
    ∃ first, first ≤ range.watermark ∧ range.through ≤ history.length ∧
      selectWalSegmentReads (image.segments.map (·.first)) range.watermark =
        some (first, (image.readDescriptors range.watermark).map (·.first)) ∧
      WalSegment.Chain history first (image.readDescriptors range.watermark) ∧
      WalSegment.concatenate (image.readDescriptors range.watermark) = WAL.encode (history.drop first) := by
  obtain ⟨actual, start, accepted, begins, through, chain⟩ := valid pair chosen
  have same := Option.some.inj (accepted.symm.trans decoded)
  subst actual
  by_cases needPrefix : range.watermark < image.active.last
  · have nonempty : image.active ∈ image.afterWatermark range.watermark :=
      List.mem_filter.mpr ⟨List.mem_append_right _ (by simp), decide_eq_true needPrefix⟩
    cases required : image.afterWatermark range.watermark with
    | nil => simp [required] at nonempty
    | cons first rest =>
      have requiredChain : WalSegment.Chain history start (first :: rest) := required ▸ chain
      have firstStart : start = first.first := by cases requiredChain; rfl
      have selection := select_exact_suffix layout.ordered layout.forward (firstStart ▸ begins) required
      exact ⟨start, begins, through, by simpa [WalSegmentImage.readDescriptors, needPrefix, required, firstStart]
        using selection, by simpa [WalSegmentImage.readDescriptors, needPrefix] using chain,
        by simpa [WalSegmentImage.readDescriptors, needPrefix] using chain.concatenate_eq⟩
  · have activeBounds := layout.forward image.active (List.mem_append_right _ (by simp))
    have coversActive := Nat.le_trans activeBounds (Nat.le_of_not_gt needPrefix)
    have closed : WalSegment.Chain history image.active.last [] := layout.activeEnd.symm ▸ .endOfHistory
    have exactActive : image.active.bytes = WAL.encode ((history.drop image.active.first).take
        (image.active.last - image.active.first)) := by
      rw [layout.activeBytes, layout.activeEnd, List.take_of_length_le (by simp)]
    have singleton : WalSegment.Chain history image.active.first [image.active] :=
      .cons activeBounds (fun _ => rfl) exactActive closed
    refine ⟨image.active.first, coversActive, through, ?_, ?_, ?_⟩
    · simpa [WalSegmentImage.readDescriptors, needPrefix] using layout.selectActive coversActive
    · simpa [WalSegmentImage.readDescriptors, needPrefix] using singleton
    · simpa [WalSegmentImage.readDescriptors, needPrefix] using singleton.concatenate_eq

private theorem strictOffsets_eq {left right : List Nat} (leftSorted : left.Pairwise (· < ·))
    (rightSorted : right.Pairwise (· < ·)) (members : ∀ start, start ∈ left ↔ start ∈ right) : left = right := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => rfl
    | cons start tail => have impossible := (members start).mpr (List.mem_cons_self ..); simp at impossible
  | cons first rest ih =>
    cases right with
    | nil => have impossible := (members first).mp (List.mem_cons_self ..); simp at impossible
    | cons start tail =>
      have firstThere := (members first).mp (List.mem_cons_self ..)
      have startHere := (members start).mpr (List.mem_cons_self ..)
      have equal : first = start := by
        rcases List.mem_cons.mp firstThere with same | later
        · exact same
        rcases List.mem_cons.mp startHere with same | laterHere
        · exact same.symm
        exact False.elim (Nat.lt_asymm ((List.pairwise_cons.mp rightSorted).1 first later)
          ((List.pairwise_cons.mp leftSorted).1 start laterHere))
      subst start
      apply congrArg (first :: ·)
      apply ih leftSorted.tail rightSorted.tail
      intro start
      by_cases same : start = first
      · subst start
        have absent {offsets : List Nat} (sorted : (first :: offsets).Pairwise (· < ·)) : first ∉ offsets :=
          fun present => Nat.lt_irrefl _ ((List.pairwise_cons.mp sorted).1 first present)
        simp [absent leftSorted, absent rightSorted]
      · simpa [List.mem_cons, same] using members start

/-- The actual sorted scan can be compared to the verified descriptor set
by address membership alone. Its resulting read order and all recovered
payload expectations then follow from the same selected pair. -/
theorem LockedWalSegmentInventory.selectsReads {directory : DiskDirectory}
    (inventory : LockedWalSegmentInventory directory) {offsets : List Nat}
    (scanned : inventory.offsets = .ok offsets) (unique : inventory.names.Nodup)
    {image : WalSegmentImage} {history : List WAL.Write}
    (layout : image.ReadLayout history) (valid : image.Valid history)
    (exactStarts : ∀ first, first ∈ offsets ↔ first ∈ image.segments.map (·.first))
    {pair : DirectoryPublication.Bindings} (chosen : image.Selects pair)
    {range : MarkedWalRange} (decoded : pair.walRange = some range) :
    ∃ first, first ≤ range.watermark ∧ range.through ≤ history.length ∧
      selectWalSegmentReads offsets range.watermark = some (first, (image.readDescriptors range.watermark).map (·.first)) ∧
      WalSegment.Chain history first (image.readDescriptors range.watermark) ∧
      WalSegment.concatenate (image.readDescriptors range.watermark) = WAL.encode (history.drop first) := by
  have listed := OpenPathReadReports.walSegmentOffsets_strict scanned unique
  have expected := layout.ordered.map (·.first) (fun _ _ relation => relation.1)
  have sorted := strictOffsets_eq listed expected exactStarts
  rw [sorted]
  exact layout.selects valid chosen decoded

/-- The selected physical read list always ends at the active descriptor. -/
theorem WalSegmentImage.readDescriptors_endsActive (image : WalSegmentImage) (watermark : Nat) :
    ∃ sealed, image.readDescriptors watermark = sealed ++ [image.active] := by
  by_cases needed : watermark < image.active.last
  · refine ⟨image.sealed.filter (fun segment => decide (watermark < segment.last)), ?_⟩
    simp [WalSegmentImage.readDescriptors, WalSegmentImage.afterWatermark, List.filter_append, needed]
  · exact ⟨[], by simp [WalSegmentImage.readDescriptors, needed]⟩

/-- Interpret the primitive payload reads only at the planned canonical
paths, in the order in which replay concatenates those files. -/
def OpenPathReadReports.readWalSegmentPayloads (reports : OpenPathReadReports) (directory : DiskDirectory)
    (offsets : List Nat) : Except IO.Error (List ByteArray) :=
  readWalSegmentPayloadsWith directory reports.readBin offsets

/-- The native sequence interpreted with successful or failed primitive
reports uses the existing inventory and ordered payload operations. -/
theorem OpenPathReadReports.readWalSegmentsWith_reports (reports : OpenPathReadReports)
    (directory : DiskDirectory) (watermark : Nat) (listing : Except IO.Error (Array IO.FS.DirEntry)) :
    readWalSegmentsWith directory watermark (fun _ => listing) (fun path => pure (reports.lstat path)) reports.readBin =
      (do
        let entries ← listing
        let offsets ← reports.walSegmentOffsets directory (entries.toList.map (·.fileName))
        let some (first, selected) := selectWalSegmentReads offsets watermark
          | throw (IO.userError "no WAL segment covers the checkpoint watermark")
        let payloads ← reports.readWalSegmentPayloads directory selected
        pure (first, selected, payloads)) := by
  have probe : probeWalSegmentWith directory (fun path => pure (reports.lstat path)) =
      reports.probeWalSegment directory := by
    funext first
    simp only [probeWalSegmentWith, OpenPathReadReports.probeWalSegment, pure, Except.pure, bind, Except.bind]
    cases classifyWalSegmentLookup (directory.file (.walSegment first)) first
      (reports.lstat (directory.file (.walSegment first))) <;> rfl
  simp only [readWalSegmentsWith, probe, walSegmentOffsets, readWalSegmentPayloads]
  rfl

private theorem readClosedSegmentPayloads {reports : OpenPathReadReports} {directory : DiskDirectory}
    {sealed : List WalSegment} (reads : ∀ segment ∈ sealed,
      reports.readBin (directory.file (.walSegment segment.first)) = .ok segment.bytes) :
    reports.readWalSegmentPayloads directory (sealed.map (·.first)) = .ok (sealed.map (·.bytes)) := by
  induction sealed with
  | nil => rfl
  | cons head rest ih =>
    have first := reads head (List.mem_cons_self ..)
    have next := ih (fun segment member => reads segment (List.mem_cons_of_mem _ member))
    simp only [OpenPathReadReports.readWalSegmentPayloads, readWalSegmentPayloadsWith, List.map_cons, List.mapM_cons, first,
      Bind.bind, Except.bind]
    change (Except.map (head.bytes :: ·)
      (reports.readWalSegmentPayloads directory (rest.map (·.first)))) = .ok (head.bytes :: rest.map (·.bytes))
    rw [next]
    rfl

/-- Closed files supply their verified payloads. The active file may have
arbitrary extra bytes after its last complete validated frame. -/
theorem OpenPathReadReports.readWalSegmentPayloads_exact {reports : OpenPathReadReports} {directory : DiskDirectory}
    {sealed : List WalSegment} {active : WalSegment} {tail : ByteArray}
    (reads : ∀ segment ∈ sealed, reports.readBin (directory.file (.walSegment segment.first)) = .ok segment.bytes)
    (readActive : reports.readBin (directory.file (.walSegment active.first)) = .ok (active.bytes ++ tail)) :
    reports.readWalSegmentPayloads directory ((sealed ++ [active]).map (·.first)) =
      .ok (sealed.map (·.bytes) ++ [active.bytes ++ tail]) := by
  have closed := readClosedSegmentPayloads reads
  have opened : reports.readWalSegmentPayloads directory [active.first] = .ok [active.bytes ++ tail] := by
    simp [OpenPathReadReports.readWalSegmentPayloads, readWalSegmentPayloadsWith, readActive, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  simp only [OpenPathReadReports.readWalSegmentPayloads, readWalSegmentPayloadsWith, List.map_append, List.map_cons,
    List.map_nil, List.mapM_append]
  change (do
    let earlierPayloads ← reports.readWalSegmentPayloads directory (sealed.map WalSegment.first)
    let last ← reports.readWalSegmentPayloads directory [active.first]
    pure (earlierPayloads ++ last)) = .ok (sealed.map WalSegment.bytes ++ [active.bytes ++ tail])
  rw [closed, opened]
  rfl

theorem concatenateReadWalSegmentPayloads (sealed : List WalSegment) (active : WalSegment) (tail : ByteArray) :
    (sealed.map (·.bytes) ++ [active.bytes ++ tail]).foldr (· ++ ·) ByteArray.empty =
      WalSegment.concatenate (sealed ++ [active]) ++ tail := by
  induction sealed with
  | nil => simp [WalSegment.concatenate]
  | cons _ _ ih => simp [WalSegment.concatenate, ih, ByteArray.append_assoc]

private theorem selectFullWalPrefix {history : List WAL.Write} {through : Nat} {length : UInt64}
    (bounded : through ≤ history.length) (markerCount : length.toNat = through * WAL.frameSize) (tail : ByteArray) :
    WAL.Boundary.select length (WAL.encode history ++ tail) = .ok (WAL.encode (history.take through)) := by
  have size : (WAL.encode (history.take through)).size = length.toNat := by
    simp [WAL.encode_size, Nat.min_eq_left bounded, markerCount, Nat.mul_comm]
  have count : length = (WAL.encode (history.take through)).size.toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [size, UInt64.toNat_ofNat_of_lt' length.toNat_lt_size]
  have encoded := WAL.Boundary.select_encoded (history.take through) (WAL.encode (history.drop through) ++ tail)
    (size.symm ▸ length.toNat_lt_size)
  rw [← count, ← ByteArray.append_assoc, ← WAL.encode_append, List.take_append_drop] at encoded
  exact encoded

/-- The planned read can start at a different covering segment and can
contain arbitrary bytes beyond the marker. Selection trims the same exact
logical history, so the retained decoder still returns the same table and
the exact physical repair bytes for that start. -/
theorem WalSegmentRecovery.recoversReadBytes {image : WalSegmentImage} {pair : DirectoryPublication.Bindings}
    {range : MarkedWalRange} {history : List WAL.Write} {base table : PackedTable} {earlier first : Nat}
    (recovery : WalSegmentRecovery image pair range history base earlier table)
    (selected : pair.walRange = some range) (starts : first ≤ range.watermark) (bounded : range.through ≤ history.length)
    (baseClock : base.committed.toNat = range.watermark) (ordered : WAL.OrdinalsFrom 1 history)
    {bytes tail : ByteArray} (readExact : bytes = WAL.encode (history.drop first) ++ tail) :
    ∃ marker length, pair.walBoundary = some marker ∧ WAL.Boundary.decode marker = .ok length ∧
      WAL.Boundary.recoverRetainedMarked base first length bytes =
        .ok (WAL.encode ((history.take range.through).drop first), table) := by
  obtain ⟨marker, length, _, visible, decoded, markerCount, _, _, full⟩ := recovery.marked
  have coverage := (DirectoryPublication.Bindings.walRange_accounting selected).2.1
  have firstThrough := Nat.le_trans starts coverage
  have firstWithin := Nat.le_trans firstThrough bounded
  let removed := history.take first
  have removedLength : removed.length = first := by simp [removed, Nat.min_eq_left firstWithin]
  have removedWithin : removed.length ≤ base.committed.toNat := by rwa [removedLength, baseClock]
  have markerCovers : (WAL.encode removed).size ≤ length.toNat := by
    rw [WAL.encode_size, removedLength, markerCount, Nat.mul_comm WAL.frameSize]
    exact Nat.mul_le_mul_right _ firstThrough
  obtain ⟨_, fullReplay⟩ := SnapshotWalReplay.fromEmpty history ordered
  have split : removed ++ history.drop first = history := List.take_append_drop ..
  have splitReplay := split.symm ▸ fullReplay
  obtain ⟨_, retiredReplay, _⟩ := splitReplay.split
  have whole : WAL.encode removed ++ bytes = WAL.encode history ++ tail := by
    rw [readExact, ← ByteArray.append_assoc, ← WAL.encode_append, split]
  have oldSelection := selectFullWalPrefix bounded markerCount ByteArray.empty
  rw [ByteArray.append_empty] at oldSelection
  have newSelection := selectFullWalPrefix bounded markerCount tail
  have fullWithTail : WAL.Boundary.recoverMarked base length (WAL.encode history ++ tail) =
      .ok (WAL.encode (history.take range.through), table) := by
    unfold WAL.Boundary.recoverMarked at full ⊢
    rw [newSelection]
    rwa [oldSelection] at full
  have comparison := WAL.Boundary.recoverRetainedMarked_eq_recoverMarked base length bytes
    (WAL.decodeOrdinals_encode removed retiredReplay.ordinals) (by simp) removedWithin markerCovers
  rw [removedLength, whole, fullWithTail] at comparison
  cases found : WAL.Boundary.recoverRetainedMarked base first length bytes with
  | error cause => rw [found] at comparison; contradiction
  | ok output =>
    obtain ⟨physical, reopened⟩ := output
    rw [found] at comparison
    have restored := Except.ok.inj comparison
    have sameTable : table = reopened := congrArg Prod.snd restored
    have prefixOfSelected : (history.take range.through).take first = removed := by
      simp [removed, List.take_take, Nat.min_eq_left firstThrough]
    have semanticBytes : WAL.encode (history.take range.through) =
        WAL.encode removed ++ WAL.encode ((history.take range.through).drop first) := by
      rw [← WAL.encode_append, ← prefixOfSelected, List.take_append_drop]
    have sameBytes := (ByteArray.append_right_inj _).mp ((congrArg Prod.fst restored).symm.trans semanticBytes)
    exact ⟨marker, length, visible, decoded, by rw [sameTable, ← sameBytes]; exact found⟩

end Alvoki.Storage
