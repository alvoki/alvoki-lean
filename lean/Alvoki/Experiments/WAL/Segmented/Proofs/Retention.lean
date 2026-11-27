import Alvoki.Experiments.WAL.Segmented.Contract

namespace WalRecoverySlice.Segmented.Contract

/-- The absolute position was released, or still contains the acknowledged batch. -/
def View.Keeps (v : View) (pos : Nat) (batch : Batch) : Prop :=
  pos ≤ v.base ∨ ∃ i, pos = v.base + i + 1 ∧ v.batches[i]? = some batch

def State.known : State → View
  | .online v | .offline v _ => v

theorem View.append_keeps (v : View) (batch : Batch) :
    (v.append batch).Keeps (v.tail + 1) batch := by
  right
  refine ⟨v.batches.length, rfl, ?_⟩
  simp [View.append]

private theorem apply_keeps {r : Request} (applied : r.apply v = some w)
    (kept : v.Keeps pos batch) : w.Keeps pos batch := by
  cases r with
  | append p =>
    simp [Request.apply] at applied
    subst w
    rcases kept with gone | ⟨i, atPos, present⟩
    · exact Or.inl gone
    · right
      refine ⟨i, atPos, ?_⟩
      have hi : i < v.batches.length := by
        by_cases hi : i < v.batches.length
        · exact hi
        · simp [List.getElem?_eq_none (Nat.le_of_not_gt hi)] at present
      simpa [View.append, List.getElem?_append_left hi] using present
  | discardThrough k =>
    simp only [Request.apply] at applied
    split at applied <;> simp_all only [Option.some.injEq, reduceCtorEq]
    subst w
    by_cases gone : pos ≤ max k v.base
    · exact Or.inl gone
    · rcases kept with old | ⟨i, atPos, present⟩
      · omega
      · right
        refine ⟨i - (k - v.base), ?_, ?_⟩
        · simp only [View.discardThrough]
          omega
        · simp only [View.discardThrough, List.getElem?_drop]
          have eq : k - v.base + (i - (k - v.base)) = i := by omega
          simpa [eq] using present

theorem Step.keeps (step : Step s e t) (kept : s.known.Keeps pos batch) :
    t.known.Keeps pos batch := by
  cases step with
  | ack applied => exact apply_keeps applied kept
  | @opened observed v pending possible =>
    rcases possible with rfl | applied
    · exact kept
    · cases pending with
      | none => contradiction
      | some r => exact apply_keeps (r := r) applied kept
  | _ => exact kept

private theorem Allows.last_step (allowed : Allows (events ++ [event]) s) :
    ∃ prior, Allows events prior ∧ Step prior event s := by
  generalize historyEq : events ++ [event] = history at allowed
  cases allowed with
  | fresh => simp at historyEq
  | next before step =>
    have parts := List.append_inj' historyEq rfl
    obtain ⟨rfl, tailEq⟩ := parts
    simp only [List.singleton_inj] at tailEq
    subst_vars
    exact ⟨_, before, step⟩

private theorem Allows.after_event {P : State → Prop} (earlier suffix : List Event) (event : Event)
    (starts : ∀ prior next, Allows earlier prior → Step prior event next → P next)
    (preserved : ∀ {s e t}, Step s e t → P s → P t)
    (allowed : Allows (earlier ++ [event] ++ suffix) last) : P last := by
  obtain ⟨rev, rfl⟩ : ∃ rev, suffix = List.reverse rev := ⟨suffix.reverse, by simp⟩
  induction rev generalizing last with
  | nil =>
    simp only [List.reverse_nil, List.append_nil] at allowed
    obtain ⟨_, before, step⟩ := allowed.last_step
    exact starts _ _ before step
  | cons e rest ih =>
    simp only [List.reverse_cons] at allowed
    rw [← List.append_assoc] at allowed
    obtain ⟨_, before, step⟩ := allowed.last_step
    exact preserved step (ih before)

/-- In every legal execution containing an append acknowledgement, the batch
remains at its original absolute position until that position is released. -/
theorem acknowledged_retained (earlier suffix : List Event) (batch : Batch) {last : State}
    (allowed : Allows (earlier ++ [.ack (.append batch)] ++ suffix) last) :
    ∃ prior, Allows earlier (.online prior) ∧ last.known.Keeps (prior.tail + 1) batch := by
  apply Allows.after_event earlier suffix _ _ _ allowed
  · intro _ _ before step
    cases step with
    | ack applied =>
      simp only [Request.apply, Option.some.injEq] at applied
      subst_vars
      exact ⟨_, before, View.append_keeps _ _⟩
  · rintro _ _ _ step ⟨prior, valid, kept⟩
    exact ⟨prior, valid, step.keeps kept⟩

private theorem apply_base {r : Request} (applied : r.apply v = some w) : v.base ≤ w.base := by
  cases r with
  | append => simp [Request.apply] at applied; subst w; exact Nat.le_refl _
  | discardThrough k =>
    simp only [Request.apply] at applied
    split at applied <;> simp_all only [Option.some.injEq, reduceCtorEq]
    subst w
    exact Nat.le_max_right ..

theorem Step.base_mono (step : Step s e t) : s.known.base ≤ t.known.base := by
  cases step with
  | ack applied => exact apply_base applied
  | @opened observed v pending possible =>
    rcases possible with rfl | applied
    · exact Nat.le_refl _
    · cases pending with
      | none => contradiction
      | some r => exact apply_base (r := r) applied
  | _ => exact Nat.le_refl _

/-- Acknowledged release is irreversible, including across any later series
of unsuccessful opens, lost responses and restarts. -/
theorem acknowledged_discard_persists (earlier suffix : List Event) (k : Nat) {last : State}
    (allowed : Allows (earlier ++ [.ack (.discardThrough k)] ++ suffix) last) :
    k ≤ last.known.base := by
  apply Allows.after_event earlier suffix _ _ _ allowed
  · intro _ _ _ step
    cases step with
    | ack applied =>
      simp only [Request.apply] at applied
      split at applied <;> simp_all only [Option.some.injEq, reduceCtorEq]
      subst_vars
      exact Nat.le_max_left ..
  · intro _ _ _ step kept
    exact Nat.le_trans kept step.base_mono

end WalRecoverySlice.Segmented.Contract
