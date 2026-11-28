import Alvoki.Experiments.SSTable.Recursive.FilteredReader

namespace ImmutableSSTable.Recursive

open Unified (Ref Data Checksum decodePacket findRef openData)

abbrev ReadM (world : Type) := EStateM String world

variable {world : Type} {frame : world → Prop}

/-- Only successful primitive results must agree with the exact immutable
image. Both outcomes must preserve the caller's protected state. -/
def ReadPost (frame : world → Prop) (action : ReadM world α) (value : α → Prop) : Prop :=
  ∀ start, frame start → match action start with
    | .ok result after => frame after ∧ value result
    | .error _ after => frame after

def ImageReads (frame : world → Prop) (source : Source (ReadM world))
    (image : ByteArray) : Prop :=
  ReadPost frame source.size (· = image.size) ∧
  ∀ offset count, ReadPost frame (source.readAt offset count)
    (· = image.extract offset (offset + count))

def exactSource (image : ByteArray) : Source (ReadM Unit) :=
  ⟨pure image.size, fun offset count => pure (image.extract offset (offset + count))⟩

private def Sim (frame : world → Prop) (action : ReadM world α)
    (reference : ReadM Unit β) (rel : α → β → Prop) : Prop :=
  ReadPost frame action fun a => ∃ b, reference () = .ok b () ∧ rel a b

private theorem Sim.bind
    {action : ReadM world α} {reference : ReadM Unit β}
    {next : α → ReadM world γ} {referenceNext : β → ReadM Unit δ}
    (first : Sim frame action reference rel)
    (rest : ∀ a b, rel a b → Sim frame (next a) (referenceNext b) out) :
    Sim frame (action >>= next) (reference >>= referenceNext) out := by
  intro start initial
  have step := first start initial
  change match EStateM.bind action next start with
    | .ok result after => frame after ∧
        ∃ b, EStateM.bind reference referenceNext () = .ok b () ∧ out result b
    | .error _ after => frame after
  cases ran : action start with
  | error e after => simpa [EStateM.bind, ran] using step
  | ok a middle =>
    rw [ran] at step
    obtain ⟨kept, b, expected, related⟩ := step
    have continuation := rest a b related middle kept
    simpa [EStateM.bind, ran, expected] using continuation

private theorem Sim.pure {rel : α → β → Prop} (h : rel a b) :
    Sim frame (pure a : ReadM world α) (pure b : ReadM Unit β) rel :=
  fun _ initial => ⟨initial, _, rfl, h⟩

private theorem Sim.error {rel : α → β → Prop} (error : String) (reference : ReadM Unit β) :
    Sim frame (throw error : ReadM world α) reference rel :=
  fun _ initial => initial

private theorem Sim.decode (result : Except String α) :
    Sim frame (liftDecode result : ReadM world α) (liftDecode result : ReadM Unit α) Eq := by
  cases result
  · exact Sim.error _ _
  · exact Sim.pure rfl

private theorem size_sim (h : ImageReads frame source image) :
    Sim frame source.size (exactSource image).size Eq := by
  intro start initial
  have step := h.1 start initial
  cases observed : source.size start with
  | error _ _ => simpa [observed] using step
  | ok result reached =>
    rw [observed] at step
    exact ⟨step.1, _, rfl, step.2⟩

private theorem read_sim (h : ImageReads frame source image) (offset count : Nat) :
    Sim frame (source.readAt offset count) ((exactSource image).readAt offset count) Eq := by
  intro start initial
  have step := h.2 offset count start initial
  cases observed : source.readAt offset count start with
  | error _ _ => simpa [observed] using step
  | ok result reached =>
    rw [observed] at step
    exact ⟨step.1, _, rfl, step.2⟩

private theorem exact_sim (h : ImageReads frame source image) (offset count : Nat) :
    Sim frame (readExact source offset count) (readExact (exactSource image) offset count) Eq := by
  unfold readExact
  apply Sim.bind (read_sim h offset count)
  intro actual expected hEq
  subst expected
  split
  · exact Sim.pure rfl
  · apply Sim.bind (rel := fun _ _ => False) (Sim.error _ _)
    intro _ _ impossible
    exact impossible.elim

private theorem index_sim (h : ImageReads frame source image)
    (crc : Checksum) (id : UInt64) (height : Nat) (ref : Ref) (limit : Nat) :
    Sim frame (readIndexPacket source crc id height ref limit)
      (readIndexPacket (exactSource image) crc id height ref limit) Eq := by
  unfold readIndexPacket
  apply Sim.bind (Sim.decode _)
  intro _ _ _
  apply Sim.bind (rel := Eq)
  · unfold readIndexBytes
    split
    · exact exact_sim h _ _
    · apply Sim.bind (exact_sim h _ _)
      intro actual expected same
      subst expected
      apply Sim.bind (exact_sim h _ _)
      intro actual expected same
      subst expected
      exact Sim.pure rfl
  · intro actual expected same
    subst expected
    exact Sim.decode _

private theorem descend_sim (h : ImageReads frame source image)
    (crc : Checksum) (id : UInt64) (before : Ref → Bool) (ref : Ref) (parent height : Nat) :
    Sim frame (descend source crc id before ref parent height)
      (descend (exactSource image) crc id before ref parent height) Eq := by
  induction height generalizing ref parent with
  | zero => exact Sim.pure rfl
  | succ depth ih =>
    unfold descend
    apply Sim.bind (index_sim h _ _ _ _ _)
    intro body expected same
    subst expected
    apply Sim.bind (Sim.decode _)
    intro children expected same
    subst expected
    split
    · apply ih
    · exact Sim.error _ _

/-- A caller can use the recursive read from any reached world preserving
its frame. The reference traverses the same checked packets. -/
theorem descend_framed (h : ImageReads frame source image)
    (crc : Checksum) (id : UInt64) (before : Ref → Bool) (ref : Ref) (parent height : Nat) :
    ReadPost frame (descend source crc id before ref parent height) fun selection =>
      descend (exactSource image) crc id before ref parent height () = .ok selection () := by
  intro start initial
  have sim := descend_sim h crc id before ref parent height start initial
  cases ran : descend source crc id before ref parent height start with
  | error _ _ => simpa [ran] using sim
  | ok selection reached =>
    rw [ran] at sim
    obtain ⟨kept, result, healthy, rfl⟩ := sim
    exact ⟨kept, healthy⟩


private theorem Sim.reject (error : String)
    (next : Unit → ReadM world α) (reference : ReadM Unit β) :
    Sim frame ((throw error : ReadM world Unit) >>= next) reference rel :=
  fun _ initial => initial

private theorem footer_sim (h : ImageReads frame source image) (crc : Checksum) :
    Sim frame (readFooter source crc) (readFooter (exactSource image) crc) Eq := by
  unfold readFooter
  apply Sim.bind (size_sim h)
  intro actual expected same
  subst expected
  split
  · apply Sim.bind (exact_sim h _ _)
    intro actual expected same
    subst expected
    apply Sim.bind (Sim.decode _)
    intro actual expected same
    subst expected
    apply Sim.bind (Sim.decode _)
    intro actual expected same
    subst expected
    exact Sim.pure rfl
  · exact Sim.reject _ _ _

private structure SameHandle (a : Handle (ReadM world)) (b : Handle (ReadM Unit))
    (source : Source (ReadM world)) (image : ByteArray) : Prop where
  source_eq : a.source = source
  reference_eq : b.source = exactSource image
  layout : a.layout = b.layout
  crc : a.crc = b.crc
  rootOffset : a.rootOffset = b.rootOffset
  height : a.height = b.height
  root : a.root = b.root
  filtered : a.filtered = b.filtered

private theorem open_sim (h : ImageReads frame source image) (crc : Checksum) (id : UInt64) :
    Sim frame (openChecked source crc id) (openChecked (exactSource image) crc id)
      (fun a b => SameHandle a b source image) := by
  unfold openChecked
  apply Sim.bind (footer_sim h crc)
  intro actual expected same
  subst expected
  obtain ⟨footer, endAt⟩ := actual
  dsimp only
  split
  · split
    · split
      · exact Sim.pure ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact Sim.reject _ _ _
    · split
      · apply Sim.bind (index_sim h _ _ _ _ _)
        intro actual expected same
        subst expected
        apply Sim.bind (Sim.decode _)
        intro actual expected same
        subst expected
        exact Sim.pure ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact Sim.reject _ _ _
  · exact Sim.reject _ _ _

private theorem packet_sim (h : ImageReads frame source image)
    (crc : Checksum) (id kind : UInt64) (offset size parent : Nat) :
    Sim frame (Unified.readPacket source crc id kind offset size parent)
      (Unified.readPacket (exactSource image) crc id kind offset size parent) Eq := by
  unfold Unified.readPacket
  split
  · apply Sim.bind (read_sim h _ _)
    intro actual expected same
    subst expected
    split
    · exact Sim.decode _
    · exact Sim.reject _ _ _
  · exact Sim.reject _ _ _

private theorem data_sim (h : ImageReads frame source image)
    (same : SameHandle actual expected source image) (ref : Ref) (parent : Nat) :
    Sim frame (actual.readData ref parent) (expected.readData ref parent) Eq := by
  obtain ⟨src, reference, layout, crc, _, _, _, _⟩ := same
  unfold Handle.readData
  rw [src, reference, layout, crc]
  apply Sim.bind (packet_sim h _ _ _ _ _ _)
  intro actualRaw expectedRaw equal
  subst expectedRaw
  apply Sim.bind (Sim.decode _)
  intro actualData expectedData equal
  subst expectedData
  apply Sim.bind (Sim.decode _)
  intro actualRow expectedRow equal
  subst expectedRow
  split
  · exact Sim.pure rfl
  · exact Sim.reject _ _ _

private theorem select_sim (h : ImageReads frame source image)
    (same : SameHandle actual expected source image) (rootChild : Ref) (before : Ref → Bool) :
    Sim frame (actual.select before rootChild) (expected.select before rootChild) Eq := by
  have ⟨src, reference, layout, crc, root, height, _, _⟩ := same
  unfold Handle.select
  rw [src, reference, layout, crc, root, height]
  apply Sim.bind (descend_sim h _ _ _ _ _ _)
  intro actualRef expectedRef equal
  subst expectedRef
  apply Sim.bind (data_sim h same _ _)
  intro a b equal
  subst b
  exact Sim.pure rfl

private theorem seek_sim (data : Data) (key : ByteArray) (lo hi : Nat) :
    Sim frame
      (seekBetween (fun i => liftDecode (data.readRow i)) key lo hi : ReadM world Nat)
      (seekBetween (fun i => liftDecode (data.readRow i)) key lo hi : ReadM Unit Nat) Eq := by
  rw [seekBetween, seekBetween]
  split
  · apply Sim.bind (Sim.decode _)
    intro row expected same
    subst expected
    split <;> apply seek_sim
  · exact Sim.pure rfl
termination_by hi - lo
decreasing_by all_goals omega

private theorem locate_sim (h : ImageReads frame source image)
    (same : SameHandle actual expected source image) (key : ByteArray) :
    Sim frame (actual.locate key) (expected.locate key) Eq := by
  unfold Handle.locate
  rw [same.root]
  dsimp only
  split
  · apply Sim.bind (select_sim h same _ _)
    intro a b equal
    subst b
    obtain ⟨ref, data⟩ := a
    dsimp only
    apply Sim.bind (seek_sim _ _ _ _)
    intro a b equal
    subst b
    split
    · exact Sim.pure rfl
    · exact Sim.reject _ _ _
  · exact Sim.pure rfl

private theorem lookup_sim (h : ImageReads frame source image)
    (same : SameHandle actual expected source image) (key : ByteArray) :
    Sim frame (actual.lookup key) (expected.lookup key) Eq := by
  unfold Handle.lookup
  apply Sim.bind (locate_sim h same key)
  intro a b equal
  subst b
  split
  · apply Sim.bind (Sim.decode _)
    intro a b equal
    subst b
    exact Sim.pure rfl
  · exact Sim.pure rfl

private theorem filter_read_sim (h : ImageReads frame source image) (crc : Checksum)
    (tableId : UInt64) (ref : Ref) :
    Sim frame (readFilter source crc tableId ref) (readFilter (exactSource image) crc tableId ref) Eq := by
  unfold readFilter
  dsimp only
  split
  · exact packet_sim h _ _ _ _ _ _
  · exact Sim.reject _ _ _

private theorem filter_check_sim (h : ImageReads frame source image)
    (same : SameHandle actual expected source image) (ref : Ref) (key : ByteArray) :
    Sim frame (actual.checkFilter ref key) (expected.checkFilter ref key) Eq := by
  unfold Handle.checkFilter
  rw [same.source_eq, same.reference_eq, same.layout, same.crc]
  split
  · apply Sim.bind (filter_read_sim h _ _ _)
    intro mask baseline eq
    subst baseline
    exact Sim.pure rfl
  · exact Sim.pure rfl

private theorem data_lookup_sim (h : ImageReads frame source image)
    (same : SameHandle actual expected source image) (ref : Ref) (parent : Nat) (key : ByteArray) :
    Sim frame (actual.lookupInData ref parent key) (expected.lookupInData ref parent key) Eq := by
  unfold Handle.lookupInData
  apply Sim.bind (data_sim h same _ _)
  intro data reference equal
  subst reference
  apply Sim.bind (seek_sim _ _ _ _)
  intro index reference equal
  subst reference
  split
  · apply Sim.bind (Sim.decode _)
    intro row reference equal
    subst reference
    exact Sim.pure rfl
  · exact Sim.reject _ _ _

private theorem filtered_lookup_sim (h : ImageReads frame source image)
    (same : SameHandle actual expected source image) (key : ByteArray) :
    Sim frame (actual.filteredLookup key) (expected.filteredLookup key) Eq := by
  unfold Handle.filteredLookup
  rw [same.filtered, same.root, same.source_eq, same.reference_eq, same.crc, same.layout,
    same.rootOffset, same.height]
  split
  · exact lookup_sim h same key
  · dsimp only
    split
    · apply Sim.bind (descend_sim h _ _ _ _ _ _)
      intro region reference equal
      subst reference
      obtain ⟨ref, parent⟩ := region
      dsimp only
      apply Sim.bind (filter_check_sim h same _ _)
      intro bit reference equal
      subst reference
      split
      · exact data_lookup_sim h same _ _ _
      · exact Sim.pure rfl
    · exact Sim.pure rfl

private theorem Sim.result {action : ReadM world α} {reference : ReadM Unit α}
    (simulation : Sim frame action reference Eq) :
    ReadPost frame action (fun value => reference () = .ok value ()) := by
  intro start initial
  have run := simulation start initial
  cases observed : action start with
  | ok actual reached =>
    rw [observed] at run
    obtain ⟨kept, _, agrees, rfl⟩ := run
    exact ⟨kept, agrees⟩
  | error _ _ => simpa [observed] using run

/-- Checked open and lookup share the exact reader used with the native
source. If they return a value, it agrees with the healthy lookup on the
producer's byte image. A reported error establishes the same frame. -/
theorem checkedLookup_framed (h : ImageReads frame source image)
    (crc : Checksum) (id : UInt64) (key : ByteArray) :
    ReadPost frame (openChecked source crc id >>= (·.lookup key)) (fun value =>
      (openChecked (exactSource image) crc id >>= (·.lookup key)) () = .ok value ()) :=
  (Sim.bind (open_sim h crc id) (fun _ _ same => lookup_sim h same key)).result

theorem checkedFilteredLookup_framed (h : ImageReads frame source image)
    (crc : Checksum) (id : UInt64) (key : ByteArray) :
    ReadPost frame (openChecked source crc id >>= (·.filteredLookup key)) (fun value =>
      (openChecked (exactSource image) crc id >>= (·.filteredLookup key)) () = .ok value ()) :=
  (Sim.bind (open_sim h crc id) (fun _ _ same => filtered_lookup_sim h same key)).result

end ImmutableSSTable.Recursive
