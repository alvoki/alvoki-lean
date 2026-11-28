import Alvoki.Experiments.SSTable.Proofs.UnifiedOpen

namespace ImmutableSSTable.Unified.ReaderRelation
private abbrev Native := EIO String
private abbrev Reference := EStateM String Unit

structure Rules where
  Rel : {α β : Type} → Native α → Reference β → (α → β → Prop) → Prop
  bind : ∀ {α β γ δ : Type} {a : Native α} {b : Reference β} {f : α → Native γ} {g : β → Reference δ}
    {rel out}, Rel a b rel → (∀ x y, rel x y → Rel (f x) (g y) out) → Rel (a >>= f) (b >>= g) out
  pure : ∀ {α β : Type} {rel : α → β → Prop} {x y}, rel x y → Rel (pure x) (pure y) rel
  throw : ∀ {α β : Type} {rel : α → β → Prop} {e : String}, Rel (throw e) (throw e) rel

variable (R : Rules)

private theorem decode (decoded : Except String α) :
    R.Rel (liftDecode decoded) (liftDecode decoded) Eq := by
  cases decoded with
  | ok x => exact R.pure rfl
  | error e => exact R.throw

structure SourceSteps (source : Source Native) (model : Source Reference) : Prop where
  size : R.Rel source.size model.size Eq
  read : ∀ offset count, R.Rel (source.readAt offset count) (model.readAt offset count) Eq

private theorem packet_sim (h : SourceSteps R source model) :
    R.Rel (readPacket source crc tableId kind offset size endAt)
      (readPacket (model) crc tableId kind offset size endAt) Eq := by
  unfold readPacket
  split
  · apply R.bind
    · exact h.read _ _
    · intro x y equal
      subst y
      split
      · apply decode R
      · exact R.throw
  · exact R.throw

private theorem footer_sim (h : SourceSteps R source model) :
    R.Rel (readFooter source crc) (readFooter (model) crc) Eq := by
  unfold readFooter
  apply R.bind
  · exact h.size
  · intro size expected equal
    subst expected
    dsimp only
    split
    · apply R.bind
      · exact h.read _ _
      · intro bytes expected equal
        subst expected
        split
        · apply R.bind (decode R _)
          intro body expected equal
          subst expected
          apply R.bind (decode R _)
          intro footer expected equal
          subst expected
          exact R.pure rfl
        · first | exact R.throw | exact R.bind (rel := fun _ _ => False) R.throw (fun _ _ h => False.elim h)
    · first | exact R.throw | exact R.bind (rel := fun _ _ => False) R.throw (fun _ _ h => False.elim h)

def SameHandle (a : Handle (Native)) (b : Handle (Reference))
    (source : Source (Native)) (model : Source Reference) : Prop :=
  a.rowCount = b.rowCount ∧ a.layout = b.layout ∧ a.root = b.root ∧ a.crc = b.crc ∧
    a.source = source ∧ b.source = model

theorem open_sim (h : SourceSteps R source model) :
    R.Rel (openChecked source crc tableId) (openChecked (model) crc tableId)
      (fun a b => SameHandle a b source model) := by
  unfold openChecked
  apply R.bind (footer_sim R h)
  intro info expected equal
  subst expected
  obtain ⟨footer, endAt⟩ := info
  dsimp only
  split
  · split
    · split
      · exact R.pure ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact R.bind (rel := fun _ _ => False) R.throw (fun _ _ impossible => False.elim impossible)
    · split
      · apply R.bind (packet_sim R h)
        intro bytes expected equal
        subst expected
        apply R.bind (decode R _)
        intro root expected equal
        subst expected
        apply R.bind (decode R _)
        intro _ _ _
        exact R.pure ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact R.bind (rel := fun _ _ => False) R.throw (fun _ _ impossible => False.elim impossible)
  · exact R.bind (rel := fun _ _ => False) R.throw (fun _ _ impossible => False.elim impossible)

private theorem seek_sim (data : Data) (key : ByteArray) (lo hi : Nat) :
    R.Rel (seekBetween (fun i => liftDecode (data.readRow i)) key lo hi : Native Nat)
      (seekBetween (fun i => liftDecode (data.readRow i)) key lo hi : Reference Nat) Eq := by
  rw [seekBetween, seekBetween]
  split
  · rename_i range
    apply R.bind (decode R _)
    intro row expected same
    subst expected
    split <;> apply seek_sim
  · exact R.pure rfl
termination_by hi - lo
decreasing_by all_goals omega

private theorem leaf_sim {a : Handle Native} {b : Handle Reference}
    (same : SameHandle a b source model)
    (h : SourceSteps R source model) (parent : Ref) :
    R.Rel (a.readLeaf parent) (b.readLeaf parent) Eq := by
  obtain ⟨_, layout, _, crc, left, right⟩ := same
  unfold Handle.readLeaf
  rw [left, right, crc, layout]
  apply R.bind (packet_sim R h)
  intro raw expected equal
  subst expected
  apply R.bind (decode R _)
  intro refs expected equal
  subst expected
  apply R.bind (decode R _)
  intro _ _ _
  split
  · exact R.pure rfl
  · exact R.bind (rel := fun _ _ => False) R.throw (fun _ _ impossible => False.elim impossible)

private theorem data_sim {a : Handle Native} {b : Handle Reference}
    (same : SameHandle a b source model)
    (h : SourceSteps R source model) (ref : Ref) :
    R.Rel (a.readData ref) (b.readData ref) Eq := by
  obtain ⟨_, layout, _, crc, left, right⟩ := same
  unfold Handle.readData
  rw [left, right, crc, layout]
  apply R.bind (packet_sim R h)
  intro raw expected equal
  subst expected
  apply R.bind (decode R _)
  intro data expected equal
  subst expected
  apply R.bind (decode R _)
  intro row expected equal
  subst expected
  split
  · exact R.pure rfl
  · exact R.bind (rel := fun _ _ => False) R.throw (fun _ _ impossible => False.elim impossible)

theorem next_sim {a : Handle Native} {b : Handle Reference}
    (same : SameHandle a b source model)
    (h : SourceSteps R source model) (index : Nat) :
    R.Rel (a.next index) (b.next index) Eq := by
  unfold Handle.next
  rw [same.1, same.2.2.1]
  split
  · exact R.pure rfl
  · dsimp only
    split
    · apply R.bind (leaf_sim R same h _)
      intro refs expected equal
      subst expected
      split
      · apply R.bind (data_sim R same h _)
        intro data expected equal
        subst expected
        apply R.bind (decode R _)
        intro row expected equal
        subst expected
        exact R.pure rfl
      · exact R.throw
    · exact R.throw

private theorem locate_sim {a : Handle (Native)} {b : Handle (Reference)}
    (same : SameHandle a b source model) (h : SourceSteps R source model) (key : ByteArray) :
    R.Rel (a.locate key) (b.locate key) Eq := by
  unfold Handle.locate
  rw [same.2.2.1]
  dsimp only
  split
  · rename_i parent _
    apply R.bind (leaf_sim R same h parent)
    intro refs expected equal
    subst expected
    split
    · rename_i ref _
      apply R.bind (data_sim R same h ref)
      intro data expected equal
      subst expected
      apply R.bind (seek_sim R data key 0 ref.count)
      intro index expected equal
      subst expected
      split
      · exact R.pure rfl
      · exact R.bind (rel := fun _ _ => False) R.throw (fun _ _ impossible => False.elim impossible)
    · exact R.throw
  · exact R.pure rfl

theorem lookup_sim {a : Handle (Native)} {b : Handle (Reference)}
    (same : SameHandle a b source model) (h : SourceSteps R source model) (key : ByteArray) :
    R.Rel (a.lookup key) (b.lookup key) Eq := by
  unfold Handle.lookup
  apply R.bind (locate_sim R same h key)
  intro found expected equal
  subst expected
  rcases found with _ | ⟨ref, data, index⟩
  · exact R.pure rfl
  · apply R.bind (decode R _)
    intro row expected equal
    subst expected
    exact R.pure rfl

theorem typedLookup (safety : SourceSteps R source model) (keys : Codec κ) (values : Codec ν) (key : κ) :
    R.Rel (do let h ← openChecked source crc tableId; (TypedTable.mk h.table keys values).lookup key)
      (do let h ← openChecked model crc tableId; (TypedTable.mk h.table keys values).lookup key) Eq := by
  have step : ∀ a b, SameHandle a b source model →
      R.Rel ((TypedTable.mk a.table keys values).lookup key)
        ((TypedTable.mk b.table keys values).lookup key) Eq := by
    intro a b same
    unfold TypedTable.lookup
    apply R.bind (lookup_sim R same safety (keys.encode key))
    intro result expected equal
    subst expected
    cases result with
    | none => exact R.pure rfl
    | some bytes =>
      apply R.bind (decode R (values.decode bytes))
      intro value expected equal
      subst expected
      exact R.pure rfl
  exact R.bind (open_sim R safety) step

end ImmutableSSTable.Unified.ReaderRelation
