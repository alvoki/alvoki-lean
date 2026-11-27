import Alvoki.Storage.Disk.WAL.CollectionRange
import Alvoki.Storage.Disk.Proofs.WAL.WalWritePublicationModel

namespace Alvoki.Storage

open WAL (Write frameSize)

/-- Offsets count frames before an endpoint. A segment beginning at `first`
starts with absolute ordinal `first + 1` and ends at ordinal `last`. -/
structure WalSegment where
  first : Nat
  last : Nat
  bytes : ByteArray

/-- A contiguous list starts at an absolute frame offset and reaches the end
of the validated history. Each immutable payload is its exact history slice.
The active segment can be empty immediately after rotation. -/
inductive WalSegment.Chain (history : List Write) : Nat → List WalSegment → Prop where
  | endOfHistory : Chain history history.length []
  | cons {segment : WalSegment} {rest : List WalSegment} (ordered : segment.first ≤ segment.last)
      (nonempty : segment.first = segment.last → rest = [])
      (bytes : segment.bytes = WAL.encode ((history.drop segment.first).take (segment.last - segment.first)))
      (tail : Chain history segment.last rest) : Chain history segment.first (segment :: rest)

def WalSegment.concatenate : List WalSegment → ByteArray
  | [] => ByteArray.empty
  | segment :: rest => segment.bytes ++ concatenate rest

theorem WalSegment.Chain.concatenate_eq {history : List Write} {first : Nat} {segments : List WalSegment}
    (chain : Chain history first segments) : concatenate segments = WAL.encode (history.drop first) := by
  induction chain with
  | endOfHistory => simp [concatenate, WAL.encode]
  | @cons segment _ ordered _ bytes _ after =>
    have tail : history.drop segment.last = (history.drop segment.first).drop (segment.last - segment.first) := by
      rw [List.drop_drop, Nat.add_sub_of_le ordered]
    rw [concatenate, bytes, after, ← WAL.encode_append, tail, List.take_append_drop]

private theorem WalSegment.Chain.filter_eq_of_before {history : List Write} {first watermark : Nat}
    {segments : List WalSegment} (chain : Chain history first segments) (earlier : watermark < first) :
    segments.filter (fun segment => decide (watermark < segment.last)) = segments := by
  induction chain with
  | endOfHistory => rfl
  | @cons segment _ ordered _ _ _ ih =>
    have beforeLast := Nat.lt_of_lt_of_le earlier ordered
    simp [beforeLast, ih beforeLast]

/-- Keep the segment straddling the checkpoint watermark, if any, and all
later segments. Their concatenation starts at or before the watermark. -/
theorem WalSegment.Chain.afterWatermark {history : List Write} {first watermark : Nat} {segments : List WalSegment}
    (chain : Chain history first segments) (within : first ≤ watermark) :
    ∃ beginAt, beginAt ≤ watermark ∧
      Chain history beginAt (segments.filter (fun segment => decide (watermark < segment.last))) := by
  induction chain with
  | endOfHistory => exact ⟨_, within, .endOfHistory⟩
  | @cons segment _ ordered nonempty bytes tail ih =>
    by_cases needed : watermark < segment.last
    · exact ⟨segment.first, within, by simpa [needed, tail.filter_eq_of_before needed] using
        (Chain.cons ordered nonempty bytes tail)⟩
    · simpa [needed] using ih (Nat.le_of_not_gt needed)

theorem selectedCheckpointWatermark_present_iff {bytes : ByteArray} {watermark : Nat} :
    selectedCheckpointWatermark (some bytes) = some watermark ↔ ∃ manifest,
      Manifest.IntegrityCheckpoint.decode bytes = .ok manifest ∧ manifest.header.committed.toNat = watermark := by
  cases decoded : Manifest.IntegrityCheckpoint.decode bytes <;>
    simp [selectedCheckpointWatermark, decoded, Except.toOption]

theorem DirectoryPublication.Bindings.walRange_accounting {pair : DirectoryPublication.Bindings}
    {range : MarkedWalRange} (selected : pair.walRange = some range) :
    selectedCheckpointWatermark pair.manifest = some range.watermark ∧ range.watermark ≤ range.through ∧
    ∃ marker count, pair.walBoundary = some marker ∧ WAL.Boundary.decode marker = .ok count ∧
      count.toNat = range.through * frameSize := by
  unfold walRange at selected
  cases watermark : selectedCheckpointWatermark pair.manifest with
  | none => simp [watermark] at selected
  | some watermarkCount =>
    cases boundary : pair.walBoundary with
    | none => simp [watermark, boundary] at selected
    | some marker =>
      cases decoded : WAL.Boundary.decode marker with
      | error => simp [watermark, boundary, decoded, Except.toOption] at selected
      | ok count =>
        simp only [watermark, boundary, decoded, Except.toOption, Bind.bind, Option.bind] at selected
        split at selected
        · rename_i checked
          have same := Option.some.inj selected
          subst range
          have alignment := Nat.mod_add_div count.toNat frameSize
          refine ⟨rfl, checked.2, marker, count, rfl, decoded, ?_⟩
          simpa [checked.1, Nat.mul_comm] using alignment.symm
        · contradiction

/-- `sealed` records guaranteed available names, in offset order, and may
include covered segments left by an interrupted unlink. The active segment
is retained separately for the entire collection stretch. -/
structure WalSegmentImage where
  directory : DirectoryPublication.Image
  sealed : List WalSegment
  active : WalSegment

def WalSegmentImage.Selects (image : WalSegmentImage) (pair : DirectoryPublication.Bindings) : Prop :=
  pair ∈ image.directory.active :: image.directory.crashImages

def WalSegmentImage.afterWatermark (image : WalSegmentImage) (watermark : Nat) : List WalSegment :=
  (image.sealed ++ [image.active]).filter (fun segment => decide (watermark < segment.last))

/-- A removable segment must be wholly before the active segment and
covered by every live or crash-selectable checkpoint/marker pair. -/
structure WalSegmentImage.Eligible (image : WalSegmentImage) (segment : WalSegment) : Prop where
  sealedBeforeActive : segment.first < segment.last ∧ segment.last ≤ image.active.first
  covered : ∀ pair, image.Selects pair → ∃ range, pair.walRange = some range ∧ segment.last ≤ range.watermark

theorem WalSegmentImage.Eligible.notActive {image : WalSegmentImage} {segment : WalSegment}
    (eligible : image.Eligible segment) : segment.first ≠ image.active.first :=
  Nat.ne_of_lt (Nat.lt_of_lt_of_le eligible.sealedBeforeActive.1 eligible.sealedBeforeActive.2)

/-- Test a sealed descriptor against all directory pairs. An undecodable
manifest or a missing or invalid WAL marker fails the corresponding test. -/
def WalSegmentImage.canRemove (image : WalSegmentImage) (segment : WalSegment) : Bool :=
  decide (segment.first < segment.last ∧ segment.last ≤ image.active.first) &&
    (image.directory.active :: image.directory.crashImages).all (fun pair =>
      (pair.walRange.map fun range => decide (segment.last ≤ range.watermark)).getD false)

theorem WalSegmentImage.canRemove_iff {image : WalSegmentImage} {segment : WalSegment} :
    image.canRemove segment = true ↔ image.Eligible segment := by
  constructor
  · intro test
    obtain ⟨bounds, pairs⟩ := Bool.and_eq_true_iff.mp test
    refine ⟨of_decide_eq_true bounds, ?_⟩
    intro pair chosen
    have covered := List.all_eq_true.mp pairs pair chosen
    cases parsed : pair.walRange with
    | none => simp [parsed] at covered
    | some range => exact ⟨range, rfl, by simpa [parsed] using covered⟩
  · intro allowed
    exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true allowed.sealedBeforeActive,
      List.all_eq_true.mpr fun pair chosen => by
        obtain ⟨range, parsed, covered⟩ := allowed.covered pair chosen
        simp [parsed, covered]⟩

/-- Every selected pair has a gap-free suffix of exact retained bytes. Old
covered names outside that suffix may already have gaps. -/
def WalSegmentImage.Valid (image : WalSegmentImage) (history : List Write) : Prop :=
  ∀ pair, image.Selects pair → ∃ range first,
    pair.walRange = some range ∧ first ≤ range.watermark ∧ range.through ≤ history.length ∧
      WalSegment.Chain history first (image.afterWatermark range.watermark)

theorem WalSegmentImage.Valid.of_chain {image : WalSegmentImage} {history : List Write} {first : Nat}
    (chain : WalSegment.Chain history first (image.sealed ++ [image.active]))
    (accounting : ∀ pair, image.Selects pair → ∃ range,
      pair.walRange = some range ∧ first ≤ range.watermark ∧ range.through ≤ history.length) :
    image.Valid history := by
  intro pair chosen
  obtain ⟨range, decoded, within, committed⟩ := accounting pair chosen
  obtain ⟨beginAt, atOrBefore, exactChain⟩ := chain.afterWatermark within
  exact ⟨range, beginAt, decoded, atOrBefore, committed, exactChain⟩

/-- A cut can drop any subset of eligible names. Names outside the subset
keep their exact immutable metadata and bytes. A lost durability guarantee
also covers an interrupted unlink whose covered file remains on disk. -/
inductive WalSegmentDeletion (eligible : WalSegment → Prop) : List WalSegment → List WalSegment → Prop where
  | empty : WalSegmentDeletion eligible [] []
  | keep (rest : WalSegmentDeletion eligible before after) :
      WalSegmentDeletion eligible (segment :: before) (segment :: after)
  | remove (allowed : eligible segment) (rest : WalSegmentDeletion eligible before after) :
      WalSegmentDeletion eligible (segment :: before) after

private theorem WalSegmentDeletion.filter_eq {eligible : WalSegment → Prop} {before after : List WalSegment}
    (deleted : WalSegmentDeletion eligible before after) (keep : WalSegment → Bool)
    (unneeded : ∀ segment, eligible segment → keep segment = false) : after.filter keep = before.filter keep := by
  induction deleted with
  | empty => rfl
  | keep _ ih => simp only [List.filter_cons, ih]
  | remove allowed _ ih => simpa [unneeded _ allowed] using ih

theorem WalSegmentDeletion.keepsSelected {before : WalSegmentImage} {after : List WalSegment}
    (deleted : WalSegmentDeletion before.Eligible before.sealed after)
    {pair : DirectoryPublication.Bindings} (chosen : before.Selects pair) {range : MarkedWalRange}
    (decoded : pair.walRange = some range) :
    ({before with sealed := after} : WalSegmentImage).afterWatermark range.watermark =
      before.afterWatermark range.watermark := by
  have keeps := deleted.filter_eq (fun segment => decide (range.watermark < segment.last)) (by
    intro segment allowed
    obtain ⟨candidate, parsed, covered⟩ := allowed.covered pair chosen
    have same := Option.some.inj (parsed.symm.trans decoded)
    subst candidate
    exact decide_eq_false (Nat.not_lt_of_ge covered))
  simp [WalSegmentImage.afterWatermark, List.filter_append, keeps]

/-- Collection leaves the checkpoint and marker untouched. A directory sync
can settle their current pair, and a crash can keep one of the prior pairs.
Eligible deletion may be retried after either event. WAL writers and
independent readers holding WAL file names stay excluded for this stretch. -/
inductive WalSegmentCollectionRetry (initial : WalSegmentImage) : WalSegmentImage → Prop where
  | start : WalSegmentCollectionRetry initial initial
  | unlink (prior : WalSegmentCollectionRetry initial before)
      (deleted : WalSegmentDeletion before.Eligible before.sealed after) :
      WalSegmentCollectionRetry initial {before with sealed := after}
  | settle (prior : WalSegmentCollectionRetry initial before) :
      WalSegmentCollectionRetry initial {before with directory := before.directory.syncDirectory}
  | crash (prior : WalSegmentCollectionRetry initial before) (survives : pair ∈ before.directory.crashImages) :
      WalSegmentCollectionRetry initial {before with directory := .settled pair}

theorem WalSegmentCollectionRetry.keepsActive {initial after : WalSegmentImage}
    (retry : WalSegmentCollectionRetry initial after) : after.active = initial.active := by
  induction retry with
  | start => rfl
  | unlink _ _ prior | settle _ prior | crash _ _ prior => exact prior

/-- The exact ordered tail is identical for every pair that remains
selectable, even when a crash rules out some earlier pairs. -/
theorem WalSegmentCollectionRetry.preservesSelected {initial after : WalSegmentImage}
    (retry : WalSegmentCollectionRetry initial after) {pair : DirectoryPublication.Bindings}
    (chosen : after.Selects pair) : initial.Selects pair ∧ ∀ range, pair.walRange = some range →
      after.afterWatermark range.watermark = initial.afterWatermark range.watermark := by
  induction retry with
  | start => exact ⟨chosen, fun _ _ => rfl⟩
  | unlink _ deleted prior =>
    obtain ⟨original, keeps⟩ := prior chosen
    exact ⟨original, fun range decoded => (deleted.keepsSelected chosen decoded).trans (keeps range decoded)⟩
  | settle _ prior =>
    have visible := (by simpa [WalSegmentImage.Selects, DirectoryPublication.Image.syncDirectory, List.mem_cons] using
      chosen : pair = _)
    exact prior (List.mem_cons.mpr (.inl visible))
  | crash _ survives prior =>
    have same := (by simpa [WalSegmentImage.Selects, DirectoryPublication.Image.settled, List.mem_cons] using
      chosen : pair = _)
    exact prior (List.mem_cons.mpr (.inr (same.symm ▸ survives)))

theorem WalSegmentCollectionRetry.valid {initial after : WalSegmentImage} {history : List Write}
    (retry : WalSegmentCollectionRetry initial after) (valid : initial.Valid history) : after.Valid history := by
  intro pair chosen
  obtain ⟨original, keeps⟩ := retry.preservesSelected chosen
  obtain ⟨range, first, decoded, begins, through, chain⟩ := valid pair original
  exact ⟨range, first, decoded, begins, through, (keeps range decoded).symm ▸ chain⟩

/-- A selected pair feeds offset-aware marked recovery the exact encoded
history after a retained segment start at or before its watermark. The
absolute marker still bounds that same history. -/
theorem WalSegmentCollectionRetry.retainedBytes {initial after : WalSegmentImage} {history : List Write}
    (retry : WalSegmentCollectionRetry initial after) (valid : initial.Valid history)
    {pair : DirectoryPublication.Bindings} (chosen : after.Selects pair) :
    ∃ range first, pair.walRange = some range ∧ first ≤ range.watermark ∧
      range.watermark ≤ range.through ∧ range.through ≤ history.length ∧
      WalSegment.concatenate (after.afterWatermark range.watermark) = WAL.encode (history.drop first) := by
  obtain ⟨range, first, decoded, begins, through, chain⟩ := retry.valid valid pair chosen
  exact ⟨range, first, decoded, begins, (DirectoryPublication.Bindings.walRange_accounting decoded).2.1,
    through, chain.concatenate_eq⟩

end Alvoki.Storage
