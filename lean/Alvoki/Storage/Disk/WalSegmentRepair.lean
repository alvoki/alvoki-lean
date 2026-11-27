import Alvoki.Storage.Disk.WAL.WalSegmentReplay
import Alvoki.Storage.Disk.Proofs.WAL.WalSegmentPathIdentity
import Alvoki.Storage.Disk.WAL.WalSegmentReadPlan

namespace Alvoki.Storage

open WAL (Write frameSize)

private theorem chain_start_le {history : List Write} {start : Nat} {segments : List WalSegment}
    (chain : WalSegment.Chain history start segments) : start ≤ history.length := by
  induction chain with
  | endOfHistory => exact Nat.le_refl _
  | cons step _ _ _ rest => exact Nat.le_trans step rest

private theorem chain_empty_end {history : List Write} {start : Nat}
    (chain : WalSegment.Chain history start []) : start = history.length := by
  cases chain
  rfl

private theorem chain_head_start {history : List Write} {start : Nat} {segment : WalSegment}
    {segments : List WalSegment} (chain : WalSegment.Chain history start (segment :: segments)) :
    start = segment.first := by
  cases chain
  rfl

private theorem encoded_take_size (history : List Write) {first last : Nat}
    (within : last ≤ history.length) :
    (WAL.encode ((history.drop first).take (last - first))).size = (last - first) * frameSize := by
  have count : last - first ≤ (history.drop first).length := by
    simp only [List.length_drop]
    exact Nat.sub_le_sub_right within first
  rw [WAL.encode_size, List.length_take, Nat.min_eq_left count, Nat.mul_comm]

private theorem WalSegment.Chain.readSpans {history : List Write} {start through : Nat}
    {sealed : List WalSegment} {active : WalSegment} {tail : ByteArray}
    (chain : Chain history start (sealed ++ [active])) (throughWithin : through ≤ history.length) :
    WalSegmentSpans through
      (sealed.map (fun segment => (segment.first, segment.bytes)) ++ [(active.first, active.bytes ++ tail)]) := by
  induction sealed generalizing start with
  | nil =>
    cases chain with
    | cons bounds _ bytes rest =>
      have ends := chain_empty_end rest
      have size := encoded_take_size history (first := active.first) (Nat.le_of_eq ends)
      refine .active ?_
      rw [ByteArray.size_append, bytes, size]
      exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (ends.symm ▸ throughWithin) _)) (Nat.le_add_right _ _)
  | cons segment rest ih =>
    cases chain with
    | cons bounds emptyLast bytes remaining =>
      have firstLt : segment.first < segment.last := Nat.lt_of_le_of_ne bounds (fun same => by
        have impossible := emptyLast same
        simp at impossible)
      have size := encoded_take_size history (first := segment.first) (chain_start_le remaining)
      have good := ih remaining
      cases rest with
      | nil =>
        have next := chain_head_start remaining
        exact .sealed (next ▸ firstLt) (by rw [bytes, size, next]) good
      | cons next rest =>
        have address := chain_head_start remaining
        exact .sealed (address ▸ firstLt) (by rw [bytes, size, address]) good

/-- Exact locked-read descriptors satisfy both the first-offset guard and
the per-file length check. Arbitrary trailing active bytes are admitted. -/
theorem WalSegment.Chain.checkReadSpans {history : List Write} {start through : Nat}
    {sealed : List WalSegment} {active : WalSegment} {tail : ByteArray}
    (chain : Chain history start (sealed ++ [active])) (startsBefore : start ≤ through)
    (throughWithin : through ≤ history.length) :
    checkWalSegmentSpans through
      (sealed.map (fun segment => (segment.first, segment.bytes)) ++ [(active.first, active.bytes ++ tail)]) = true := by
  refine (checkWalSegmentSpans_iff ..).mpr ⟨?_, chain.readSpans throughWithin⟩
  cases sealed with
  | nil =>
    have covers : active.first ≤ through := chain_head_start chain ▸ startsBefore
    exact ⟨_, _, rfl, covers⟩
  | cons head rest =>
    have covers : head.first ≤ through := chain_head_start chain ▸ startsBefore
    exact ⟨_, _, rfl, covers⟩

/-- The original boundary file is the only possible replacement target.
Every prior descriptor is carried through intact, and every newer address
is listed separately for removal. -/
structure WalSegmentRepairPlan where
  kept : List WalSegment
  boundary : WalSegment
  newer : List WalSegment

def WalSegmentRepairPlan.replacement (plan : WalSegmentRepairPlan) (through : Nat) : WalSegment :=
  { plan.boundary with
    last := through
    bytes := plan.boundary.bytes.extract 0 ((through - plan.boundary.first) * frameSize) }

/-- Locate the keeper at the marker. When the next segment starts exactly
at the marker, that segment supplies the empty final payload. -/
def planWalSegmentRepair (through : Nat) : List WalSegment → Option WalSegmentRepairPlan
  | [] => none
  | segment :: later =>
    if through < segment.first then none
    else if later ≠ [] ∧ segment.last ≤ through then
      (planWalSegmentRepair through later).map (fun plan => { plan with kept := segment :: plan.kept })
    else if through ≤ segment.last then some ⟨[], segment, later⟩ else none

theorem planWalSegmentRepair_beforeStart {through : Nat} {segment : WalSegment} {later : List WalSegment}
    (earlier : through < segment.first) : planWalSegmentRepair through (segment :: later) = none := by
  simp [planWalSegmentRepair, earlier]

private theorem encode_take_bytes (events : List Write) {frames : Nat} (within : frames ≤ events.length) :
    (WAL.encode events).extract 0 (frames * frameSize) = WAL.encode (events.take frames) := by
  have split := congrArg WAL.encode (List.take_append_drop frames events)
  rw [WAL.encode_append] at split
  rw [← split]
  apply ByteArray.extract_append_eq_left
  simp [WAL.encode_size, List.length_take, Nat.min_eq_left within, Nat.mul_comm]

/-- A plan certifies the physical cut and its per-file reconstruction. -/
structure WalSegmentRepairPlan.Exact (plan : WalSegmentRepairPlan) (through first : Nat)
    (history : List Write) (segments : List WalSegment) : Prop where
  split : segments = plan.kept ++ plan.boundary :: plan.newer
  covers : plan.boundary.first ≤ through ∧ through ≤ plan.boundary.last
  available : (through - plan.boundary.first) * frameSize ≤ plan.boundary.bytes.size
  keptThrough : ∀ segment ∈ plan.kept, segment.last ≤ through
  newerAfter : ∀ segment ∈ plan.newer, through < segment.first
  selectedBytes : WalSegment.concatenate (plan.kept ++ [plan.replacement through]) =
    WAL.encode ((history.drop first).take (through - first))

private theorem chain_all_starts {history : List Write} {start : Nat} {segments : List WalSegment}
    (chain : WalSegment.Chain history start segments) {segment : WalSegment} (member : segment ∈ segments) :
    start ≤ segment.first := by
  induction chain with
  | endOfHistory => simp at member
  | cons ordered _ _ _ ih =>
    rcases List.mem_cons.mp member with rfl | next
    · exact Nat.le_refl _
    · exact Nat.le_trans ordered (ih next)

theorem WalSegment.Chain.plansRepair {history : List Write} {first through : Nat} {segments : List WalSegment}
    (chain : Chain history first segments) (present : segments ≠ []) (starts : first ≤ through)
    (within : through ≤ history.length) :
    ∃ plan, planWalSegmentRepair through segments = some plan ∧ plan.Exact through first history segments := by
  induction chain with
  | endOfHistory => contradiction
  | @cons segment later bounds _ bytes rest ih =>
    by_cases next : later ≠ [] ∧ segment.last ≤ through
    · obtain ⟨plan, choice, exactPlan⟩ := ih next.1 next.2
      let extended := { plan with kept := segment :: plan.kept }
      refine ⟨extended, ?_, ?_⟩
      · simp [planWalSegmentRepair, Nat.not_lt.mpr starts, next, choice, extended]
      · refine ⟨?_, exactPlan.covers, exactPlan.available, ?_, exactPlan.newerAfter, ?_⟩
        · simp [extended, exactPlan.split]
        · intro file member
          rcases List.mem_cons.mp member with rfl | older
          · exact next.2
          · exact exactPlan.keptThrough file older
        · change segment.bytes ++ WalSegment.concatenate (plan.kept ++ [plan.replacement through]) = _
          rw [bytes, exactPlan.selectedBytes, ← WAL.encode_append]
          have tailEq : history.drop segment.last = (history.drop segment.first).drop (segment.last - segment.first) := by
            rw [List.drop_drop, Nat.add_sub_of_le bounds]
          rw [tailEq, ← List.take_add, show segment.last - segment.first + (through - segment.last) =
            through - segment.first by omega]
    · have throughBound : through ≤ segment.last := by
        by_cases closed : later = []
        · subst later
          exact (chain_empty_end rest).symm ▸ within
        · exact Nat.le_of_lt (Nat.lt_of_not_ge (fun high => next ⟨closed, high⟩))
      let plan : WalSegmentRepairPlan := ⟨[], segment, later⟩
      refine ⟨plan, ?_, rfl, ⟨starts, throughBound⟩, ?_, by simp [plan], ?_, ?_⟩
      · simp [planWalSegmentRepair, Nat.not_lt.mpr starts, next, throughBound, plan]
      · change (through - segment.first) * frameSize ≤ segment.bytes.size
        rw [bytes, encoded_take_size history (chain_start_le rest)]
        exact Nat.mul_le_mul_right _ (Nat.sub_le_sub_right throughBound _)
      · intro file member
        have laterExists : later ≠ [] := List.ne_nil_of_mem member
        have beforeLater : through < segment.last := Nat.lt_of_not_ge (fun reaches => next ⟨laterExists, reaches⟩)
        exact Nat.lt_of_lt_of_le beforeLater (chain_all_starts rest member)
      · change segment.bytes.extract 0 ((through - segment.first) * frameSize) ++ ByteArray.empty = _
        rw [ByteArray.append_empty, bytes]
        have count : through - segment.first ≤ ((history.drop segment.first).take (segment.last - segment.first)).length := by
          simp only [List.length_take, List.length_drop]
          exact Nat.le_min.mpr ⟨Nat.sub_le_sub_right throughBound _, Nat.sub_le_sub_right within _⟩
        rw [encode_take_bytes _ count, List.take_take, Nat.min_eq_left (Nat.sub_le_sub_right throughBound _)]

/-- Even when the physical boundary file contains an unselected tail, the
per-file replacement is exactly the marker's prefix of that file. -/
theorem WalSegmentRepairPlan.Exact.replacementFromRead {plan : WalSegmentRepairPlan} {through first : Nat}
    {history : List Write} {segments : List WalSegment} (exactPlan : plan.Exact through first history segments)
    (tail : ByteArray) : (plan.replacement through).bytes =
      (plan.boundary.bytes ++ tail).extract 0 ((through - plan.boundary.first) * frameSize) := by
  have tailStart := Nat.sub_eq_zero_of_le exactPlan.available
  simp [WalSegmentRepairPlan.replacement, ByteArray.extract_append, tailStart]

/-- Neither the replacement address nor any removal address aliases a kept
file. Addresses reconstruct their own canonical paths in the held directory. -/
theorem WalSegmentRepairPlan.Exact.keptPathsUntouched {plan : WalSegmentRepairPlan} {through first : Nat}
    {history : List Write} {segments : List WalSegment} (exactPlan : plan.Exact through first history segments)
    (chain : WalSegment.Chain history first segments) (directory : DiskDirectory)
    {file : WalSegment} (kept : file ∈ plan.kept) :
    directory.file (.walSegment plan.boundary.first) ≠ directory.file (.walSegment file.first) ∧
    ∀ later ∈ plan.newer, directory.file (.walSegment later.first) ≠ directory.file (.walSegment file.first) := by
  have ordered := exactPlan.split ▸ chain.startsStrict
  have ascending := (List.pairwise_append.mp ordered).2.2 file kept
  refine ⟨fun equal => Nat.ne_of_lt (ascending _ (List.mem_cons_self ..))
    (directory.walSegment_path_injective equal).symm, ?_⟩
  intro later chosen equal
  exact Nat.ne_of_lt (ascending _ (List.mem_cons_of_mem _ chosen)) (directory.walSegment_path_injective equal).symm

/-- Covered files that were outside the selected read prefix are also
outside the replacement and removal addresses. -/
theorem WalSegmentRepairPlan.Exact.earlierPathUntouched {plan : WalSegmentRepairPlan} {through first : Nat}
    {history : List Write} {segments : List WalSegment} (exactPlan : plan.Exact through first history segments)
    (chain : WalSegment.Chain history first segments) (directory : DiskDirectory)
    {offset : Nat} (earlier : offset < first) :
    directory.file (.walSegment plan.boundary.first) ≠ directory.file (.walSegment offset) ∧
    ∀ later ∈ plan.newer, directory.file (.walSegment later.first) ≠ directory.file (.walSegment offset) := by
  have laterPath (file : WalSegment) (within : file ∈ plan.boundary :: plan.newer) :
      directory.file (.walSegment file.first) ≠ directory.file (.walSegment offset) := by
    intro equal
    have member : file ∈ segments := exactPlan.split.symm ▸ List.mem_append_right _ within
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le earlier (chain_all_starts chain member))
      (directory.walSegment_path_injective equal).symm
  exact ⟨laterPath _ (List.mem_cons_self ..), fun file mem => laterPath file (List.mem_cons_of_mem _ mem)⟩

/-- Destructive repair at an absolute marker must bound every pair that
can still be selected. A live pair alone supplies only one such bound. -/
def WalSegmentImage.AllMarkersAtMost (image : WalSegmentImage) (through : Nat) : Prop :=
  ∀ pair, image.Selects pair → ∃ range, pair.walRange = some range ∧ range.through ≤ through

/-- A real directory barrier settles its current pair. Its decoded marker
then bounds every remaining recovery choice. -/
theorem WalSegmentImage.markersAtMost_afterSync (image : WalSegmentImage) {range : MarkedWalRange}
    (visible : image.directory.active.walRange = some range) :
    ({ image with directory := image.directory.syncDirectory } : WalSegmentImage).AllMarkersAtMost range.through := by
  intro pair chosen
  have current : pair = image.directory.active := by
    simpa [WalSegmentImage.Selects, DirectoryPublication.Image.syncDirectory, List.mem_cons] using chosen
  subst pair
  exact ⟨range, visible, Nat.le_refl _⟩

/-- The replacement retains enough frames at its own address for every
selectable marker. Every address scheduled for removal begins strictly beyond
all those markers. This bound still permits different checkpoint watermarks. -/
theorem WalSegmentRepairPlan.Exact.safeForEveryMarker {plan : WalSegmentRepairPlan} {through first : Nat}
    {history : List Write} {segments : List WalSegment} (exactPlan : plan.Exact through first history segments)
    {image : WalSegmentImage} (bound : image.AllMarkersAtMost through)
    {pair : DirectoryPublication.Bindings} (chosen : image.Selects pair) :
    ∃ range, pair.walRange = some range ∧
      (range.through - plan.boundary.first) * frameSize ≤ (plan.replacement through).bytes.size ∧
      ∀ removed ∈ plan.newer, range.through < removed.first := by
  obtain ⟨range, decoded, enough⟩ := bound pair chosen
  have size : (plan.replacement through).bytes.size = (through - plan.boundary.first) * frameSize := by
    simp [WalSegmentRepairPlan.replacement, ByteArray.size_extract, Nat.min_eq_left exactPlan.available]
  refine ⟨range, decoded, ?_, fun removed later => Nat.lt_of_le_of_lt enough (exactPlan.newerAfter removed later)⟩
  rw [size]
  exact Nat.mul_le_mul_right _ (Nat.sub_le_sub_right enough _)

/-- The retained replacement can take the active role after all newer
names are gone. Before that point an inventory can still choose a newer
address, so this is a property of the final descriptor list. -/
theorem WalSegmentRepairPlan.Exact.activeAfterPruning {plan : WalSegmentRepairPlan} {through first : Nat}
    {history : List Write} {segments : List WalSegment} (exactPlan : plan.Exact through first history segments)
    (chain : WalSegment.Chain history first segments) :
    ((plan.kept ++ [plan.replacement through]).map (·.first)).max? = some plan.boundary.first := by
  have ordered := exactPlan.split ▸ chain.startsStrict
  have lower := (List.pairwise_append.mp ordered).2.2
  apply List.max?_eq_some_iff.mpr
  refine ⟨List.mem_map.mpr ⟨plan.replacement through, List.mem_append_right _ (by simp), rfl⟩, ?_⟩
  intro _ member
  obtain ⟨file, included, rfl⟩ := List.mem_map.mp member
  rcases List.mem_append.mp included with earlier | boundary
  · exact Nat.le_of_lt (lower _ earlier _ (List.mem_cons_self ..))
  · rw [List.mem_singleton.mp boundary]
    exact Nat.le_refl _

theorem WalSegmentRepairPlan.Exact.bytesAtMarker {plan : WalSegmentRepairPlan} {through first : Nat}
    {history : List Write} {segments : List WalSegment} (exactPlan : plan.Exact through first history segments) :
    WalSegment.concatenate (plan.kept ++ [plan.replacement through]) = WAL.encode ((history.take through).drop first) := by
  rw [List.drop_take]
  exact exactPlan.selectedBytes

private theorem zipReadPayloads (sealed : List WalSegment) (active : WalSegment) (tail : ByteArray) :
    ((sealed ++ [active]).map (·.first)).zip (sealed.map (·.bytes) ++ [active.bytes ++ tail]) =
      sealed.map (fun segment => (segment.first, segment.bytes)) ++ [(active.first, active.bytes ++ tail)] := by
  induction sealed with
  | nil => rfl
  | cons segment rest ih => simp only [List.cons_append, List.map_cons, List.zip_cons_cons, ih]

/-- The actual selected addresses and payload reports yield a checked repair
plan. Only the active payload may include an arbitrary unselected tail.
Applying the plan additionally requires `AllMarkersAtMost` at the effect point. -/
theorem LockedWalSegmentInventory.plansRepairFromReads {directory : DiskDirectory}
    (inventory : LockedWalSegmentInventory directory) {offsets : List Nat}
    (scanned : inventory.offsets = .ok offsets) (unique : inventory.names.Nodup)
    {image : WalSegmentImage} {history : List Write}
    (layout : image.ReadLayout history) (valid : image.Valid history)
    (exactStarts : ∀ first, first ∈ offsets ↔ first ∈ image.segments.map (·.first))
    {pair : DirectoryPublication.Bindings} (chosen : image.Selects pair) {range : MarkedWalRange}
    (decoded : pair.walRange = some range) {tail : ByteArray}
    (closedReads : ∀ segment ∈ (image.readDescriptors range.watermark).dropLast,
      inventory.reports.readBin (directory.file (.walSegment segment.first)) = .ok segment.bytes)
    (activeRead : inventory.reports.readBin (directory.file (.walSegment image.active.first)) =
      .ok (image.active.bytes ++ tail)) :
    ∃ first addresses payloads plan,
      selectWalSegmentReads offsets range.watermark = some (first, addresses) ∧
      inventory.reports.readWalSegmentPayloads directory addresses = .ok payloads ∧
      checkWalSegmentSpans range.through (addresses.zip payloads) = true ∧
      planWalSegmentRepair range.through (image.readDescriptors range.watermark) = some plan ∧
      plan.Exact range.through first history (image.readDescriptors range.watermark) := by
  obtain ⟨first, beforeCheckpoint, bounded, selected, chain, _⟩ :=
    inventory.selectsReads scanned unique layout valid exactStarts chosen decoded
  have beforeMarker := Nat.le_trans beforeCheckpoint (DirectoryPublication.Bindings.walRange_accounting decoded).2.1
  obtain ⟨closed, split⟩ := image.readDescriptors_endsActive range.watermark
  have actualClosed : ∀ segment ∈ closed,
      inventory.reports.readBin (directory.file (.walSegment segment.first)) = .ok segment.bytes := by
    intro segment member
    exact closedReads segment (by simpa [split] using member)
  have reported := OpenPathReadReports.readWalSegmentPayloads_exact actualClosed activeRead
  have checked := (split ▸ chain).checkReadSpans (tail := tail) beforeMarker bounded
  have present : image.readDescriptors range.watermark ≠ [] := by simp [split]
  obtain ⟨plan, returned, witnessed⟩ := chain.plansRepair present beforeMarker bounded
  refine ⟨first, (closed ++ [image.active]).map (·.first), closed.map (·.bytes) ++ [image.active.bytes ++ tail], plan,
    ?_, reported, ?_, returned, witnessed⟩
  · simpa [split] using selected
  · rw [zipReadPayloads]
    exact checked

end Alvoki.Storage
