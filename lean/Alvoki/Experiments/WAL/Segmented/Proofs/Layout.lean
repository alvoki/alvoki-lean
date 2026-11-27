import Alvoki.Experiments.WAL.Segmented.Protocol

namespace WalRecoverySlice.Segmented

/-- Logical batches assigned to this zero-based segment by fixed batch capacity. -/
def segmentHistory (capacity id : Nat) (history : List Bytes) : List Bytes :=
  (history.drop (id * capacity)).take capacity

def segmentWindow (capacity first count : Nat) (history : List Bytes) : List Bytes :=
  match count with
  | 0 => []
  | n + 1 => segmentHistory capacity first history ++ segmentWindow capacity (first + 1) n history

theorem segmentHistory_full {capacity id : Nat} {history : List Bytes}
    (sealed : (id + 1) * capacity ≤ history.length) :
    (segmentHistory capacity id history).length = capacity := by
  simp only [segmentHistory, List.length_take, List.length_drop]
  rw [Nat.add_mul, Nat.one_mul] at sealed
  omega

theorem segmentHistory_active_length {capacity active : Nat} {history : List Bytes}
    (limit : history.length ≤ (active + 1) * capacity) :
    (segmentHistory capacity active history).length = history.length - active * capacity := by
  simp only [segmentHistory, List.length_take, List.length_drop]
  rw [Nat.add_mul, Nat.one_mul] at limit
  omega

theorem segmentWindow_eq (capacity first count : Nat) (history : List Bytes) :
    segmentWindow capacity first count history =
      (history.drop (first * capacity)).take (count * capacity) := by
  induction count generalizing first with
  | zero => simp [segmentWindow]
  | succ n ih =>
    rw [segmentWindow, ih, segmentHistory]
    conv => rhs; rw [Nat.succ_mul, Nat.add_comm, List.take_add]
    simp [List.drop_drop, Nat.add_mul]

theorem selectedHistory_eq (c : Control) (history : List Bytes)
    (upper : history.length ≤ (c.active + 1) * c.capacity) :
    ((segmentWindow c.capacity c.firstNeeded (c.active - c.firstNeeded) history ++
      segmentHistory c.capacity c.active history).drop (c.discarded - c.firstNeeded * c.capacity)) =
        history.drop c.discarded := by
  let f := c.firstNeeded
  have atActive : f ≤ c.active := Nat.min_le_left ..
  have retained : f * c.capacity ≤ c.discarded :=
    Nat.le_trans (Nat.mul_le_mul_right c.capacity (Nat.min_le_right ..)) (Nat.div_mul_le_self ..)
  have join : f * c.capacity + (c.active - f) * c.capacity = c.active * c.capacity := by
    rw [← Nat.add_mul]; congr 1; omega
  have extent : history.length - f * c.capacity ≤ (c.active - f) * c.capacity + c.capacity := by
    rw [Nat.add_mul, Nat.one_mul] at upper
    omega
  change ((segmentWindow c.capacity f (c.active - f) history ++ segmentHistory c.capacity c.active history).drop _) = _
  rw [segmentWindow_eq, segmentHistory, ← join, ← List.drop_drop, ← List.take_add]
  rw [List.take_of_length_le (by simpa only [List.length_drop] using extent), List.drop_drop]
  congr 1
  change f * c.capacity + (c.discarded - f * c.capacity) = _
  omega

theorem segmentHistory_before_append {capacity id : Nat} {history : List Bytes} (batch : Bytes)
    (sealed : (id + 1) * capacity ≤ history.length) :
    segmentHistory capacity id (history ++ [batch]) = segmentHistory capacity id history := by
  rw [Nat.add_mul, Nat.one_mul] at sealed
  simp only [segmentHistory, List.drop_append_of_le_length (by omega : id * capacity ≤ history.length)]
  exact List.take_append_of_le_length (by simp only [List.length_drop]; omega)

theorem segmentHistory_append {capacity active : Nat} {history : List Bytes} (batch : Bytes)
    (start : active * capacity ≤ history.length) (room : history.length < (active + 1) * capacity) :
    segmentHistory capacity active (history ++ [batch]) = segmentHistory capacity active history ++ [batch] := by
  rw [Nat.add_mul, Nat.one_mul] at room
  simp only [segmentHistory, List.drop_append_of_le_length start]
  rw [List.take_of_length_le (by simp only [List.length_append, List.length_cons, List.length_nil, List.length_drop]; omega)]
  rw [List.take_of_length_le (by simp only [List.length_drop]; omega)]

theorem segmentHistory_next_empty {capacity active : Nat} {history : List Bytes}
    (limit : history.length ≤ (active + 1) * capacity) :
    segmentHistory capacity (active + 1) history = [] := by
  simp [segmentHistory, List.drop_eq_nil_iff.mpr limit]

/-- The error and interruption carry a reached state too. Choosing an
impossible failure postcondition specializes the same rule to healthy walks. -/
def readOutcome {σ α : Type} (inv failure : σ → Prop) (expected : α)
    (outcome : EStateM.Result Unit σ (Except String α)) : Prop :=
  match outcome with
  | .ok (.ok value) state => inv state ∧ value = expected
  | .ok (.error _) state | .error _ state => failure state

/-- Concatenate exactly the selected segment range using the executable reader.
The invariant is threaded through changing per-segment cursors and heap states.
A failed or interrupted child immediately ends this read at that child's heap. -/
theorem readSealed_spec {σ : Type} (ops : Ops (ExceptT String (EStateM Unit σ))) (policy : Policy)
    (capacity first count : Nat) (history : List Bytes) (acc : Array Bytes) (start : σ)
    (inv failure : σ → Prop) (initial : inv start)
    (full : (first + count) * capacity ≤ history.length)
    (leaf : ∀ id, first ≤ id → id < first + count → ∀ s, inv s →
      readOutcome inv failure (segmentHistory capacity id history) ((ops.openSegment policy id).run s)) :
    readOutcome inv failure (acc ++ (segmentWindow capacity first count history).toArray)
      ((readSealed ops policy capacity first count acc).run start) := by
  induction count generalizing first acc start with
  | zero => simpa [segmentWindow, readSealed, readOutcome, Pure.pure, ExceptT.pure, EStateM.pure] using initial
  | succ n ih =>
    have step := leaf first (by omega) (by omega) start initial
    have enough : (first + 1) * capacity ≤ history.length :=
      Nat.le_trans (Nat.mul_le_mul_right capacity (by omega)) full
    have width := segmentHistory_full (history := history) enough
    simp only [readSealed, Bind.bind, ExceptT.run, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, EStateM.bind]
    cases got : (ops.openSegment policy first) start with
    | error _ s => simpa [ExceptT.run, got, readOutcome] using step
    | ok ret s =>
      cases ret with
      | error e => simpa [ExceptT.run, got, readOutcome, Pure.pure, EStateM.pure] using step
      | ok batches =>
        change readOutcome inv failure _ ((ops.openSegment policy first) start) at step
        rw [got] at step
        obtain ⟨kept, rfl⟩ := step
        simp only [width, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        have res := ih (first + 1) (acc ++ (segmentHistory capacity first history).toArray) s kept
          (by simpa [Nat.add_assoc, Nat.add_comm 1] using full)
          (by intro id low high state entry; exact leaf id (by omega) (by omega) state entry)
        simpa [segmentWindow, Array.append_assoc, ExceptT.run] using res


private theorem readOutcome_bind {σ α β : Type} {inv post failure : σ → Prop} {b : σ}
    {a : α} {target : β} {act : ExceptT String (EStateM Unit σ) α} {k : α → ExceptT String (EStateM Unit σ) β}
    (src : readOutcome inv failure a (act.run b))
    (tail : ∀ s, inv s → readOutcome post failure target ((k a).run s)) :
    readOutcome post failure target ((act >>= k).run b) := by
  simp only [Bind.bind, ExceptT.run, ExceptT.bind, ExceptT.mk, EStateM.bind]
  change readOutcome inv failure a (act b) at src
  cases h : act b with
  | error _ s => rw [h] at src; exact src
  | ok v s =>
    rw [h] at src
    cases v with
    | error => exact src
    | ok value =>
      obtain ⟨keep, rfl⟩ := src
      exact tail s keep

/-- Recover the precise absolute base and retained history from the control and
its selected child files. Primitive errors use a separate postcondition; a
healthy caller can instantiate it with False. -/
theorem reopen_spec {σ : Type} (ops : Ops (ExceptT String (EStateM Unit σ)))
    (c : Control) (history : List Bytes) (start : σ) (seen layout opened installed failure : σ → Prop)
    (capacity : 0 < c.capacity ∧ c.capacity ≤ 255)
    (lower : c.active * c.capacity ≤ history.length)
    (upper : history.length ≤ (c.active + 1) * c.capacity) (release : c.discarded ≤ history.length)
    (readControl : readOutcome seen failure c (ops.readControl.run start))
    (stabilize : ∀ s, seen s → readOutcome layout failure () (ops.syncRoot.run s))
    (sealedRead : ∀ id, c.firstNeeded ≤ id → id < c.active → ∀ s, layout s →
      readOutcome layout failure (segmentHistory c.capacity id history) ((ops.openSegment c.policy id).run s))
    (activeRead : ∀ s, layout s →
      readOutcome opened failure (segmentHistory c.capacity c.active history) ((ops.openSegment c.policy c.active).run s))
    (cleanup : ∀ s, opened s → readOutcome installed failure () ((collect ops c).run s)) :
    readOutcome installed failure
      ⟨c, history.length - c.active * c.capacity, ⟨c.discarded, history.drop c.discarded⟩⟩
      ((reopen ops).run start) := by
  unfold reopen reopenWith
  apply readOutcome_bind readControl
  intro s valid
  have nonzero : c.capacity ≠ 0 := by omega
  simp only [nonzero, decide_false, Bool.false_or,
    Nat.not_lt_of_ge capacity.2, ↓reduceIte, Nat.not_lt_of_ge (Nat.le_trans release upper)]
  apply readOutcome_bind (stabilize s valid)
  intro next stable
  have first : c.firstNeeded ≤ c.active := Nat.min_le_left ..
  have span : c.firstNeeded + (c.active - c.firstNeeded) = c.active := by omega
  apply readOutcome_bind (readSealed_spec ops c.policy c.capacity c.firstNeeded (c.active - c.firstNeeded)
    history #[] next layout failure stable (by rwa [span])
    (by intro id low hi; exact sealedRead id low (by omega)))
  intro afterSealed validSealed
  apply readOutcome_bind (activeRead afterSealed validSealed)
  intro afterActive validActive
  have n := segmentHistory_active_length (active := c.active) upper
  have size : history.length - c.active * c.capacity ≤ c.capacity := by
    rw [Nat.add_mul, Nat.one_mul] at upper; omega
  have endBound : ¬ c.discarded > c.active * c.capacity + (history.length - c.active * c.capacity) := by omega
  simp only [n, Nat.not_lt_of_ge size, endBound, ↓reduceIte, Array.toList_append,
    List.nil_append, selectedHistory_eq c history upper]
  apply readOutcome_bind (cleanup afterActive validActive)
  intro finish ok
  exact ⟨ok, rfl⟩

end WalRecoverySlice.Segmented
