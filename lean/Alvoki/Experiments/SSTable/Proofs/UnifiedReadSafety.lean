import Alvoki.Experiments.SSTable.Proofs.UnifiedOpen

namespace ImmutableSSTable.Unified

private abbrev Reference := EStateM String Unit
private abbrev Native := EIO String

abbrev ReadWorld := Void IO.RealWorld

/-- A returned error preserves the same caller frame as a successful read. -/
def ReadPost (P : ReadWorld → Prop) (q : α → Prop) (a : Native α) : Prop :=
  ∀ w, P w → match a w with
    | .error _ t => P t
    | .ok x t => P t ∧ q x

private def Sim {P : ReadWorld → Prop} (a : Native α) (b : Reference β)
    (rel : α → β → Prop) : Prop :=
  ReadPost P (fun x => ∃ y, b () = .ok y () ∧ rel x y) a

variable {P : ReadWorld → Prop}

private theorem Sim.bind {a : Native α} {b : Reference β}
    {f : α → Native γ} {g : β → Reference δ}
    (step : Sim (P := P) a b rel) (next : ∀ x y, rel x y → Sim (P := P) (f x) (g y) out) :
    Sim (P := P) (a >>= f) (b >>= g) out := by
  intro s valid
  have first := step s valid
  cases h : a s with
  | error e t => simpa [Bind.bind, instMonadEIO._aux_13, EST.bind, h] using (by simpa only [h] using first : P t)
  | ok x t =>
    rw [h] at first
    obtain ⟨held, y, returned, related⟩ := first
    have rest := next x y related t held
    cases more : f x t with
    | error e u => simpa [Bind.bind, instMonadEIO._aux_13, EST.bind, h, more] using (by simpa only [more] using rest : P u)
    | ok z u =>
      rw [more] at rest
      obtain ⟨frame, v, done, outcome⟩ := rest
      simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, h, more, EStateM.bind, returned]
      exact ⟨frame, v, done, outcome⟩

private theorem Sim.pure {rel : α → β → Prop} (h : rel x y) :
    Sim (P := P) (pure x : Native α) (pure y : Reference β) rel :=
  fun _ frame => ⟨frame, y, rfl, h⟩

private theorem Sim.throw : Sim (P := P) (throw e : Native α) b rel := fun _ frame => frame

private theorem Sim.decode (decoded : Except String α) :
    Sim (P := P) (liftDecode decoded : Native α) (liftDecode decoded : Reference α) Eq := by
  cases decoded with
  | ok value => exact Sim.pure rfl
  | error e => exact Sim.throw

/-- Reference values for every successful read, independent of whether a
particular call reports a fault. -/
structure ReadSafety (source : Source (Native)) (image : ByteArray) : Prop where
  size : ∀ s n t, source.size s = .ok n t → n = image.size
  read : ∀ offset count s bytes t, source.readAt offset count s = .ok bytes t →
    bytes = image.extract offset (offset + count)

def ReadSafety.reference (image : ByteArray) : Source (Reference) :=
  ⟨pure image.size, fun offset count => pure (image.extract offset (offset + count))⟩

structure ScopedRead (P : ReadWorld → Prop) (source : Source Native) (image : ByteArray) : Prop where
  size : ReadPost P (· = image.size) source.size
  read : ∀ offset count, ReadPost P (· = image.extract offset (offset + count)) (source.readAt offset count)

private theorem exact_sim {a : Native α} (h : ReadPost P (· = v) a) :
    Sim (P := P) a (pure v) Eq := by
  intro s valid
  have step := h s valid
  cases ran : a s with
  | error e t => simpa only [ran] using step
  | ok x t =>
    rw [ran] at step
    exact ⟨step.1, v, rfl, step.2⟩

private theorem packet_sim (h : ScopedRead P source image) :
    Sim (P := P) (readPacket source crc tableId kind offset size endAt)
      (readPacket (ReadSafety.reference image) crc tableId kind offset size endAt) Eq := by
  unfold readPacket
  split
  · apply Sim.bind
    · exact exact_sim (h.read _ _)
    · intro x y equal
      subst y
      split
      · apply Sim.decode
      · exact Sim.throw
  · exact Sim.throw

private theorem footer_sim (h : ScopedRead P source image) :
    Sim (P := P) (readFooter source crc) (readFooter (ReadSafety.reference image) crc) Eq := by
  unfold readFooter
  apply Sim.bind
  · exact exact_sim h.size
  · intro size expected equal
    subst expected
    dsimp only
    split
    · apply Sim.bind
      · exact exact_sim (h.read _ _)
      · intro bytes expected equal
        subst expected
        split
        · apply Sim.bind (Sim.decode _)
          intro body expected equal
          subst expected
          apply Sim.bind (Sim.decode _)
          intro footer expected equal
          subst expected
          exact Sim.pure rfl
        · first | exact Sim.throw | exact Sim.bind (rel := fun _ _ => False) Sim.throw (fun _ _ h => False.elim h)
    · first | exact Sim.throw | exact Sim.bind (rel := fun _ _ => False) Sim.throw (fun _ _ h => False.elim h)

private def SameHandle (a : Handle (Native)) (b : Handle (Reference))
    (source : Source (Native)) (image : ByteArray) : Prop :=
  a.rowCount = b.rowCount ∧ a.layout = b.layout ∧ a.root = b.root ∧ a.crc = b.crc ∧
    a.source = source ∧ b.source = ReadSafety.reference image

private theorem open_sim (h : ScopedRead P source image) :
    Sim (P := P) (openChecked source crc tableId) (openChecked (ReadSafety.reference image) crc tableId)
      (fun a b => SameHandle a b source image) := by
  unfold openChecked
  apply Sim.bind (footer_sim h)
  intro info expected equal
  subst expected
  obtain ⟨footer, endAt⟩ := info
  dsimp only
  split
  · split
    · split
      · exact Sim.pure ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact Sim.bind (rel := fun _ _ => False) Sim.throw (fun _ _ impossible => False.elim impossible)
    · split
      · apply Sim.bind (packet_sim h)
        intro bytes expected equal
        subst expected
        apply Sim.bind (Sim.decode _)
        intro root expected equal
        subst expected
        apply Sim.bind (Sim.decode _)
        intro _ _ _
        exact Sim.pure ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact Sim.bind (rel := fun _ _ => False) Sim.throw (fun _ _ impossible => False.elim impossible)
  · exact Sim.bind (rel := fun _ _ => False) Sim.throw (fun _ _ impossible => False.elim impossible)

/-- The metadata checks for an immutable table preserve the read footprint,
including when an extent read or a metadata check reports an error. -/
theorem checkedOpen_frame (safe : ScopedRead P source image) :
    ReadPost P (fun _ => True) (openChecked source crc tableId) := by
  intro w held
  have frame := open_sim (crc := crc) (tableId := tableId) safe w held
  cases ran : openChecked source crc tableId w with
  | error e t => simpa only [ran] using frame
  | ok handle t =>
    rw [ran] at frame
    exact ⟨frame.1, trivial⟩

/-- Total reads needed only for healthy recovery. The poststates of two
different bounded reads may differ, even when both read the same inode. -/
structure AvailableRead (P : ReadWorld → Prop) (source : Source Native) (bytes : ByteArray) : Prop where
  size : ∀ w, P w → ∃ t, source.size w = .ok bytes.size t ∧ P t
  read : ∀ offset count, count ≤ maxRowSize → offset + count ≤ bytes.size →
    ∀ w, P w → ∃ t, source.readAt offset count w = .ok (bytes.extract offset (offset + count)) t ∧ P t

/-- A valid image needs a size read, a footer read and, for a nonempty
table, one bounded root packet read. All use the actual reached world. -/
theorem Image.checkedOpen_healthy {source : Source Native} (built : Image crc layout rows image)
    (available : AvailableRead P source image) (w) (held : P w) :
    ∃ h t, openChecked source crc layout.tableId w = .ok h t ∧ P t := by
  obtain ⟨footer, groups, rfl, count, _, valid, footerAt, footerWithin, _, root⟩ := built.exists_layout
  obtain ⟨s, size, held⟩ := available.size w held
  have endEq := Nat.sub_add_cancel footerWithin
  obtain ⟨u, fread, held⟩ := available.read _ _ (by decide : footerBodySize + checksumSize ≤ maxRowSize)
    (Nat.le_of_eq endEq) s held
  rw [endEq, footerAt] at fread
  have flength : (encodePacket crc 0 4 0 (encodeFooterBody footer)).size =
      footerBodySize + checksumSize := by rw [encodePacket_size, encodeFooterBody_size]
  have readsFooter : readFooter source crc w =
      .ok (footer, image.size - (footerBodySize + checksumSize)) u := by
    simp [readFooter, Bind.bind, instMonadEIO._aux_13, EST.bind, size,
      footerWithin, built.extent, fread, flength,
      decodePacket_encodePacket, decodeFooterBody_encodeFooterBody footer valid, liftDecode,
      Pure.pure, instMonadEIO._aux_5, EST.pure]
  cases rows with
  | nil =>
    have zero : footer.count = 0 := count
    simp only [List.isEmpty_nil, ite_true] at root
    have noData : image.size - (footerBodySize + checksumSize) = 0 := by rw [root.2, Nat.sub_self]
    simp only [openChecked, Bind.bind, instMonadEIO._aux_13, EST.bind, readsFooter, zero,
      noData, eq_self, ite_true, Pure.pure, instMonadEIO._aux_5]
    exact ⟨_, u, rfl, held⟩
  | cons row rest =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false] at root
    obtain ⟨refs, children, rootEnd, packet⟩ := root
    obtain ⟨t, rread, held⟩ := available.read _ _ packet.bounded packet.extent u held
    rw [packet.slice] at rread
    have enough : checksumSize ≤ footer.rootSize := by rw [packet.size_eq]; omega
    have length : (encodePacket crc footer.layout.tableId 3 footer.rootOffset
        (encodeIndex (groups.map LeafGroup.ref))).size = footer.rootSize := by rw [encodePacket_size, packet.size_eq]
    have readsRoot : readPacket source crc footer.layout.tableId 3 footer.rootOffset footer.rootSize
        (image.size - (footerBodySize + checksumSize)) u = .ok (encodeIndex (groups.map LeafGroup.ref)) t := by
      simp [readPacket, Bind.bind, instMonadEIO._aux_13, EST.bind,
        enough, packet.bounded, Nat.le_of_eq rootEnd, rread, length, decodePacket_encodePacket, liftDecode]
      rfl
    have children' : checkChildren (groups.map LeafGroup.ref) 0 (rest.length + 1) footer.rootOffset = .ok () := by
      simpa using children
    simp [openChecked, Bind.bind, instMonadEIO._aux_13, EST.bind, readsFooter, count, rootEnd,
      readsRoot, decodeIndex_encodeIndex _ refs, liftDecode, children', Pure.pure, instMonadEIO._aux_5,
      EST.pure]
    exact ⟨_, t, ⟨rfl, rfl⟩, held⟩

private theorem seek_sim (data : Data) (key : ByteArray) (lo hi : Nat) :
    Sim (P := P) (seekBetween (fun i => liftDecode (data.readRow i)) key lo hi : Native Nat)
      (seekBetween (fun i => liftDecode (data.readRow i)) key lo hi : Reference Nat) Eq := by
  rw [seekBetween, seekBetween]
  split
  · rename_i range
    apply Sim.bind (Sim.decode _)
    intro row expected same
    subst expected
    split <;> apply seek_sim
  · exact Sim.pure rfl
termination_by hi - lo
decreasing_by all_goals omega

private theorem locate_sim {a : Handle (Native)} {b : Handle (Reference)}
    (same : SameHandle a b source image) (h : ScopedRead P source image) (key : ByteArray) :
    Sim (P := P) (a.locate key) (b.locate key) Eq := by
  obtain ⟨_, layout, root, crc, left, right⟩ := same
  unfold Handle.locate
  rw [root]
  dsimp only
  split
  · rename_i parent _
    unfold Handle.readLeaf
    rw [left, right, crc, layout]
    apply Sim.bind
    · apply Sim.bind (packet_sim h)
      intro raw expected equal
      subst expected
      apply Sim.bind (Sim.decode _)
      intro refs expected equal
      subst expected
      apply Sim.bind (Sim.decode _)
      intro _ _ _
      split
      · exact Sim.pure rfl
      · exact Sim.bind (rel := fun _ _ => False) Sim.throw (fun _ _ impossible => False.elim impossible)
    · intro refs expected equal
      subst expected
      split
      · rename_i ref _
        unfold Handle.readData
        rw [left, right, crc, layout]
        apply Sim.bind
        · apply Sim.bind (packet_sim h)
          intro raw expected equal
          subst expected
          apply Sim.bind (Sim.decode _)
          intro data expected equal
          subst expected
          apply Sim.bind (Sim.decode _)
          intro row expected equal
          subst expected
          split
          · exact Sim.pure rfl
          · exact Sim.bind (rel := fun _ _ => False) Sim.throw (fun _ _ impossible => False.elim impossible)
        · intro data expected equal
          subst expected
          apply Sim.bind (seek_sim data key 0 ref.count)
          intro index expected equal
          subst expected
          split
          · exact Sim.pure rfl
          · exact Sim.bind (rel := fun _ _ => False) Sim.throw (fun _ _ impossible => False.elim impossible)
      · exact Sim.throw
  · exact Sim.pure rfl

private theorem lookup_sim {a : Handle (Native)} {b : Handle (Reference)}
    (same : SameHandle a b source image) (h : ScopedRead P source image) (key : ByteArray) :
    Sim (P := P) (a.lookup key) (b.lookup key) Eq := by
  unfold Handle.lookup
  apply Sim.bind (locate_sim same h key)
  intro found expected equal
  subst expected
  rcases found with _ | ⟨ref, data, index⟩
  · exact Sim.pure rfl
  · apply Sim.bind (Sim.decode _)
    intro row expected equal
    subst expected
    exact Sim.pure rfl

private theorem ReadSafety.unscoped (h : ReadSafety source image) : ScopedRead (fun _ => True) source image where
  size s _ := by cases ran : source.size s with
                 | error => trivial
                 | ok n t => exact ⟨trivial, h.size _ _ _ ran⟩
  read o n s _ := by cases ran : source.readAt o n s with
                     | error => trivial
                     | ok bytes t => exact ⟨trivial, h.read _ _ _ _ _ ran⟩

/-- Any successful lookup on the checked image equals the result computed
by the healthy reference schedule. The actual source may fail on other calls. -/
theorem checkedLookup_success (safety : ReadSafety source image)
    (ran : (do
      let table ← openChecked source crc tableId
      table.lookup key) start = .ok value after) :
    (do
      let table ← openChecked (ReadSafety.reference image) crc tableId
      table.lookup key) () = .ok value () := by
  have sim := Sim.bind (open_sim (crc := crc) (tableId := tableId) safety.unscoped)
    (fun _ _ same => lookup_sim same safety.unscoped key)
  have result := sim start trivial
  rw [ran] at result
  obtain ⟨_, expected, done, rfl⟩ := result
  exact done

theorem Image.checkedLookup_sound (built : Image crc layout rows image)
    (safety : ReadSafety source image)
    (ran : (do
      let table ← openChecked source crc layout.tableId
      table.lookup key) start = .ok value after) :
    value = Contents.lookup rows key := by
  have referenceRan := checkedLookup_success safety ran
  have served : (ReadSafety.reference image).Serves image := ⟨rfl, fun _ _ _ _ => rfl⟩
  obtain ⟨table, opened, observed⟩ := built.open_observed served
  have looked := table.lookup_observed observed built.ordered key
  rw [show (do
    let table ← openChecked (ReadSafety.reference image) crc layout.tableId
    table.lookup key : Reference (Option ByteArray)) = pure (Contents.lookup rows key) by simp [opened, looked]] at referenceRan
  exact (EStateM.Result.ok.inj referenceRan).1.symm

/-- Transfer checked open plus typed lookup, including the caller's decode. -/
theorem checkedTypedLookup_scoped (safety : ScopedRead P source image)
    (keys : Codec κ) (values : Codec ν) (key : κ) :
    ReadPost P (fun value => (do
      let handle ← openChecked (ReadSafety.reference image) crc tableId
      (TypedTable.mk handle.table keys values).lookup key) () = .ok value ()) (do
      let handle ← openChecked source crc tableId
      (TypedTable.mk handle.table keys values).lookup key) := by
  have step : ∀ a b, SameHandle a b source image →
      Sim (P := P) ((TypedTable.mk a.table keys values).lookup key)
        ((TypedTable.mk b.table keys values).lookup key) Eq := by
    intro a b same
    unfold TypedTable.lookup
    apply Sim.bind (lookup_sim same safety (keys.encode key))
    intro result expected equal
    subst expected
    cases result with
    | none => exact Sim.pure rfl
    | some bytes =>
      apply Sim.bind (Sim.decode (values.decode bytes))
      intro value expected equal
      subst expected
      exact Sim.pure rfl
  intro s valid
  have sim := Sim.bind (open_sim (crc := crc) (tableId := tableId) safety) step s valid
  split <;> rename_i ran <;> rw [ran] at sim
  · exact sim
  · obtain ⟨frame, y, done, rfl⟩ := sim
    exact ⟨frame, done⟩

theorem checkedTypedLookup_success (safety : ReadSafety source image)
    (keys : Codec κ) (values : Codec ν) (key : κ)
    (ran : (do
      let handle ← openChecked source crc tableId
      (TypedTable.mk handle.table keys values).lookup key) start = .ok value after) :
    (do
      let handle ← openChecked (ReadSafety.reference image) crc tableId
      (TypedTable.mk handle.table keys values).lookup key) () = .ok value () := by
  have post := checkedTypedLookup_scoped (crc := crc) (tableId := tableId) safety.unscoped keys values key start trivial
  rw [ran] at post
  exact post.2

private theorem leaf_sim (same : SameHandle a b source image)
    (h : ScopedRead P source image) (parent : Ref) :
    Sim (P := P) (a.readLeaf parent) (b.readLeaf parent) Eq := by
  obtain ⟨_, layout, _, crc, left, right⟩ := same
  unfold Handle.readLeaf
  rw [left, right, crc, layout]
  apply Sim.bind (packet_sim h)
  intro raw expected equal
  subst expected
  apply Sim.bind (Sim.decode _)
  intro refs expected equal
  subst expected
  apply Sim.bind (Sim.decode _)
  intro _ _ _
  split
  · exact Sim.pure rfl
  · exact Sim.bind (rel := fun _ _ => False) Sim.throw (fun _ _ impossible => False.elim impossible)

private theorem data_sim (same : SameHandle a b source image)
    (h : ScopedRead P source image) (ref : Ref) :
    Sim (P := P) (a.readData ref) (b.readData ref) Eq := by
  obtain ⟨_, layout, _, crc, left, right⟩ := same
  unfold Handle.readData
  rw [left, right, crc, layout]
  apply Sim.bind (packet_sim h)
  intro raw expected equal
  subst expected
  apply Sim.bind (Sim.decode _)
  intro data expected equal
  subst expected
  apply Sim.bind (Sim.decode _)
  intro row expected equal
  subst expected
  split
  · exact Sim.pure rfl
  · exact Sim.bind (rel := fun _ _ => False) Sim.throw (fun _ _ impossible => False.elim impossible)

private theorem next_sim (same : SameHandle a b source image)
    (h : ScopedRead P source image) (index : Nat) :
    Sim (P := P) (a.next index) (b.next index) Eq := by
  unfold Handle.next
  rw [same.1, same.2.2.1]
  split
  · exact Sim.pure rfl
  · dsimp only
    split
    · apply Sim.bind (leaf_sim same h _)
      intro refs expected equal
      subst expected
      split
      · apply Sim.bind (data_sim same h _)
        intro data expected equal
        subst expected
        apply Sim.bind (Sim.decode _)
        intro row expected equal
        subst expected
        exact Sim.pure rfl
      · exact Sim.throw
    · exact Sim.throw

/-- The table returned by the actual checked open has a fallible indexed
cursor. A successful call returns the exact row or logical EOF. All returned
outcomes preserve the caller's chosen frame, including a failed packet
read or decode. The caller may strengthen the frame during later use. -/
theorem Image.checkedOpenTable_next_scoped
    (built : Image crc layout rows image) (opening : ScopedRead P source image) :
    ReadPost P (fun table : Table Native =>
      ∀ Q, ScopedRead Q source image →
        ∀ index, ReadPost Q (· = Contents.next rows index) (table.next index))
      (openTableChecked source crc layout.tableId) := by
  have served : (ReadSafety.reference image).Serves image := ⟨rfl, fun _ _ _ _ => rfl⟩
  obtain ⟨reference, opened, observed⟩ := built.open_observed served
  intro start frame
  have handoff := open_sim (crc := crc) (tableId := layout.tableId) opening start frame
  cases ran : openChecked source crc layout.tableId start with
  | error error reached =>
    simpa [openTableChecked, Bind.bind, instMonadEIO._aux_13, EST.bind, ran] using handoff
  | ok handle reached =>
    rw [ran] at handoff
    obtain ⟨kept, other, openedOther, same⟩ := handoff
    rw [opened] at openedOther
    cases openedOther
    simp only [openTableChecked, Bind.bind, instMonadEIO._aux_13, EST.bind, ran]
    refine ⟨kept, ?_⟩
    intro Q reads index before valid
    have cursor := next_sim same reads index before valid
    simp only [Handle.table]
    rw [reference.next_observed observed] at cursor
    cases pulled : handle.next index before with
    | error error after => simpa only [pulled] using cursor
    | ok result after =>
      rw [pulled] at cursor
      obtain ⟨held, value, exactResult, rfl⟩ := cursor
      exact ⟨held, (EStateM.Result.ok.inj exactResult).1.symm⟩

end ImmutableSSTable.Unified
