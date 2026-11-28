import Alvoki.Experiments.SSTable.Recursive.BlockIterator

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

private def SameHandle (a : Handle (ReadM world)) (b : Handle (ReadM Unit))
    (source : Source (ReadM world)) (image : ByteArray) : Prop :=
  a.source = source ∧ b.source = exactSource image ∧ a.layout = b.layout ∧ a.crc = b.crc ∧
    a.rootOffset = b.rootOffset ∧ a.height = b.height ∧ a.root = b.root ∧ a.rowCount = b.rowCount

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

private theorem data_packet_sim (h : ImageReads frame source image)
    (crc : Checksum) (id : UInt64) (ref : Ref) (parent : Nat) :
    Sim frame (Unified.readPacket source crc id dataKind ref.offset ref.size parent)
      (Unified.readPacket (exactSource image) crc id dataKind ref.offset ref.size parent) Eq := by
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
  apply Sim.bind (data_packet_sim h _ _ _ _)
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
  rw [same.2.2.2.2.2.2.1]
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

namespace BlockIterator

private theorem position_sim (h : ImageReads frame source image)
    (same : SameHandle actual expected source image) (before : Ref → Bool)
    (ref : Ref) (parent : Nat) (path : List Frame) (height : Nat) :
    Sim frame (descend actual before ref parent path height)
      (descend expected before ref parent path height) Eq := by
  induction height generalizing ref parent path with
  | zero =>
    unfold descend
    apply Sim.bind (data_sim h same _ _)
    rintro a _ rfl
    exact Sim.pure rfl
  | succ depth ih =>
    have ⟨src, refSource, layout, crc, _, _, _, _⟩ := same
    unfold descend
    rw [src, refSource, layout, crc]
    apply Sim.bind (index_sim h _ _ _ _ _)
    rintro raw _ rfl
    apply Sim.bind (Sim.decode _)
    rintro children _ rfl
    split
    · exact ih _ _ _
    · exact Sim.error _ _

private theorem root_sim (h : ImageReads frame source image)
    (same : SameHandle actual expected source image) (before : Ref → Bool) (child : Ref) :
    Sim frame (fromRoot actual before child) (fromRoot expected before child) Eq := by
  have ⟨_, _, _, _, root, height, _, _⟩ := same
  unfold fromRoot
  rw [root, height]
  exact position_sim h same _ _ _ _ _

private theorem boundary_sim (h : ImageReads frame source image)
    (same : SameHandle actual expected source image) (index : Nat) (path : List Frame) :
    Sim frame (atBoundary actual index path) (atBoundary expected index path) Eq := by
  induction path with
  | nil =>
    have ⟨_, _, _, _, _, _, root, _⟩ := same
    unfold atBoundary
    rw [root]
    dsimp only
    split
    · exact root_sim h same _ _
    · exact Sim.error _ _
  | cons _ _ ih =>
    unfold atBoundary
    split
    · dsimp only
      split
      · exact position_sim h same _ _ _ _ _
      · exact Sim.error _ _
    · exact ih

end BlockIterator

/-- Both cursors use identically checked packets from the same immutable image.
Only the real descriptor's source can perform effects or return I/O errors. -/
def BlockCursor.SameImage (actual : BlockCursor (ReadM world)) (expected : BlockCursor (ReadM Unit))
    (source : Source (ReadM world)) (image : ByteArray) : Prop :=
  SameHandle actual.handle expected.handle source image ∧
    actual.index = expected.index ∧ actual.position = expected.position

private theorem BlockCursor.prepare_sim (h : ImageReads frame source image)
    (same : BlockCursor.SameImage actual expected source image) :
    Sim frame actual.prepare expected.prepare Eq := by
  obtain ⟨handleEq, indexEq, positionEq⟩ := same
  unfold BlockCursor.prepare
  rw [positionEq, indexEq]
  split
  · exact BlockIterator.boundary_sim h handleEq _ _
  · split
    · exact Sim.pure rfl
    · exact BlockIterator.boundary_sim h handleEq _ _

private def SameItem (source : Source (ReadM world)) (image : ByteArray) :
    Option (Entry × BlockCursor (ReadM world)) → Option (Entry × BlockCursor (ReadM Unit)) → Prop
  | none, none => True
  | some (next, actual), some (expected, reference) =>
      next = expected ∧ actual.SameImage reference source image
  | _, _ => False

private theorem BlockCursor.pull_sim (h : ImageReads frame source image)
    (same : BlockCursor.SameImage actual expected source image) :
    Sim frame actual.pull expected.pull (SameItem source image) := by
  have ⟨handleEq, indexEq, _⟩ := same
  unfold BlockCursor.pull
  -- Keep the cursors inside the prepare actions unchanged.
  have guard : (actual.handle.rowCount ≤ actual.index) =
      (expected.handle.rowCount ≤ expected.index) := by rw [handleEq.2.2.2.2.2.2.2, indexEq]
  by_cases done : actual.handle.rowCount ≤ actual.index
  · have doneRef : expected.handle.rowCount ≤ expected.index := guard ▸ done
    simp only [done, doneRef, ↓reduceIte]
    exact Sim.pure trivial
  · have doneRef : ¬ expected.handle.rowCount ≤ expected.index := guard ▸ done
    simp only [done, doneRef, ↓reduceIte]
    apply Sim.bind (BlockCursor.prepare_sim h same)
    rintro position _ rfl
    rw [indexEq]
    apply Sim.bind (Sim.decode _)
    rintro row _ rfl
    exact Sim.pure ⟨rfl, handleEq, rfl, rfl⟩

private theorem seekCursor_sim (h : ImageReads frame source image)
    (same : SameHandle actual expected source image) (key : ByteArray) :
    Sim frame (actual.seekCursor key) (expected.seekCursor key)
      (fun a b => a.SameImage b source image) := by
  have ⟨_, _, _, _, _, _, root, count⟩ := same
  unfold Handle.seekCursor
  rw [root]
  dsimp only
  split
  · apply Sim.bind (BlockIterator.root_sim h same _ _)
    rintro position _ rfl
    apply Sim.bind (seek_sim _ _ _ _)
    rintro index _ rfl
    split
    · exact Sim.pure ⟨same, rfl, rfl⟩
    · exact Sim.reject _ _ _
  · exact Sim.pure ⟨same, count, rfl⟩

/-- A framed checked open yields a cold cursor refining the exact image. -/
theorem checkedCursor_framed (h : ImageReads frame source image)
    (exact : Image layout crc image rows) (index : Nat) :
    ReadPost frame (openChecked source crc layout.tableId >>= fun held => pure (held.cursorAt index))
      (fun actual => ∃ expected, actual.SameImage expected source image ∧ expected.Observes image rows) := by
  have simulation := Sim.bind (open_sim h crc layout.tableId) fun a b same =>
    Sim.pure (frame := frame) (rel := fun x y => BlockCursor.SameImage x y source image)
      (a := a.cursorAt index) (b := b.cursorAt index) ⟨same, rfl, rfl⟩
  intro start within
  have run := simulation start within
  cases ran : (openChecked source crc layout.tableId >>= fun held => pure (held.cursorAt index)) start with
  | error _ _ => simpa [ran] using run
  | ok actual reached =>
    rw [ran] at run
    obtain ⟨kept, _, agrees, same⟩ := run
    obtain ⟨expected, opened, observes⟩ := exact.open_observes (Source.memory_serves (m := ReadM Unit) image)
    change ((openChecked (exactSource image) crc layout.tableId >>= fun held =>
      pure (held.cursorAt index)) ()) = _ at agrees
    change openChecked (exactSource image) crc layout.tableId = pure expected at opened
    rw [opened, pure_bind] at agrees
    cases agrees
    exact ⟨kept, _, same, Handle.cursorAt_observes observes index⟩

/-- A framed seek retains the same checked packets as the exact reader. -/
theorem seekCursor_framed (h : ImageReads frame source image)
    (exact : Image layout crc image rows) (key : ByteArray) :
    ReadPost frame (openChecked source crc layout.tableId >>= (·.seekCursor key))
      (fun actual => ∃ expected, actual.SameImage expected source image ∧ expected.Observes image rows ∧
        LowerBound (fun i => (rowAt rows i).key) rows.length key actual.index) := by
  have simulation := Sim.bind (open_sim h crc layout.tableId) fun _ _ same =>
    seekCursor_sim h same key
  intro start within
  have run := simulation start within
  cases ran : (openChecked source crc layout.tableId >>= (·.seekCursor key)) start with
  | error _ _ => simpa [ran] using run
  | ok actual reached =>
    rw [ran] at run
    obtain ⟨kept, _, agrees, same⟩ := run
    obtain ⟨reference, opened, observes⟩ := exact.open_observes (Source.memory_serves (m := ReadM Unit) image)
    obtain ⟨index, lower⟩ := Unified.exists_lowerBound exact.ordered key
    obtain ⟨expected, sought, atIndex, cursorOk⟩ := observes.seekCursor lower
    change ((openChecked (exactSource image) crc layout.tableId >>= (·.seekCursor key)) ()) = _ at agrees
    change openChecked (exactSource image) crc layout.tableId = pure reference at opened
    rw [opened, pure_bind, sought] at agrees
    cases agrees
    exact ⟨kept, _, same, cursorOk, by simpa [same.2.1, atIndex] using lower⟩

/-- With the native source framed, each successful result refines the exact
suffix, and the last world of a failed read still preserves the frame. -/
theorem BlockCursor.pull_framed (h : ImageReads frame source image)
    (same : BlockCursor.SameImage actual expected source image)
    (observed : expected.Observes image rows) :
    ReadPost frame actual.pull (fun result =>
      match result with
      | none => rows.drop actual.index = []
      | some (row, next) => ∃ reference, next.SameImage reference source image ∧
          reference.Observes image rows ∧ next.index = actual.index + 1 ∧
          rows.drop actual.index = row :: rows.drop next.index) := by
  intro start within
  have run := BlockCursor.pull_sim h same start within
  cases ran : actual.pull start with
  | error _ _ => simpa [ran] using run
  | ok result reached =>
    rw [ran] at run
    obtain ⟨kept, item, agrees, related⟩ := run
    refine ⟨kept, ?_⟩
    rw [same.2.1]
    have step := observed.pull
    cases suffix : rows.drop expected.index with
    | nil =>
      rw [suffix] at step
      rw [step] at agrees
      cases agrees
      cases result <;> simp_all [SameItem]
    | cons row tail =>
      rw [suffix] at step
      obtain ⟨next, advance, cursorOk, offset, rest⟩ := step
      rw [advance] at agrees
      cases agrees
      cases result with
      | none => exact related.elim
      | some item =>
        obtain ⟨a, nextActual⟩ := item
        obtain ⟨rfl, nextSame⟩ := related
        exact ⟨next, nextSame, cursorOk, nextSame.2.1.trans offset,
          by simp [nextSame.2.1, rest]⟩

/-- Returning an error from any boundary read leaves the cursor unadvanced and
passes the same error and reached world to the consumer. -/
theorem BlockCursor.pull_prepare_error {cursor : BlockCursor (ReadM world)}
    (notDone : cursor.index < cursor.handle.rowCount)
    (failed : cursor.prepare start = .error error reached) :
    cursor.pull start = .error error reached := by
  simp [BlockCursor.pull, Nat.not_le_of_gt notDone, Bind.bind, EStateM.bind, failed]

theorem BlockCursor.pull_row_error {cursor : BlockCursor (ReadM world)}
    {position : BlockIterator.Position}
    (notDone : cursor.index < cursor.handle.rowCount)
    (prepared : cursor.prepare start = .ok position middle)
    (failed : position.read (m := ReadM world) cursor.index middle = .error error reached) :
    cursor.pull start = .error error reached := by
  simp [BlockCursor.pull, Nat.not_le_of_gt notDone, Bind.bind, EStateM.bind, prepared, failed]

end ImmutableSSTable.Recursive
