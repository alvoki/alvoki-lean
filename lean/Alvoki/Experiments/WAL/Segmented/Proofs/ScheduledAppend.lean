import Alvoki.Experiments.WAL.Segmented.Proofs.Model
import Alvoki.Experiments.WAL.Proofs.ScheduledExecution

namespace WalRecoverySlice.Segmented.Model

/-- The exact append callback retains the submitted batch as the sole
    uncertainty. Ordinary scheduled writes may ACK. The first torn data write
    aborts, so neither a data barrier nor a marker publication follows it. -/
theorem Effects.appendRun_refines (effects : Effects) (clock id : Nat) (policy : Policy)
    (image : Persistence.Image) (history : List Bytes) (p : Bytes)
    (entry : Persistence.Ready policy image history) (clean : image.powerLoss = image)
    (bounded : ∀ b ∈ history, b.length ≤ 32) (fits : history.length < 255) (size : p.length ≤ 32) :
    let r := (effects.appendRun clock id policy (Persistence.historyCursor history) p).run image
    Persistence.Dirty policy history (some p) (Persistence.reached r) ∧
    (policy = .logOnly → (Persistence.reached r).MarkersSettled) ∧
    ∀ c, Persistence.acknowledged r = some c →
      c = Persistence.historyCursor (history ++ [p]) ∧
      Persistence.Ready policy (Persistence.reached r) (history ++ [p]) ∧
      (Persistence.reached r).powerLoss = Persistence.reached r := by
  unfold Effects.appendRun
  cases residue : effects.tornAppend clock id policy (Persistence.historyCursor history) p with
  | none =>
    dsimp only
    rw [Persistence.appendBatch_withWritebacks _ _ _ _ _ _ clean]
    let e := Persistence.appendEffects (effects.appendSegment clock id) (effects.appendWritebacks clock id)
    refine ⟨Persistence.appendBatch_dirty policy e _ _ _ entry clean bounded fits size, ?_, ?_⟩
    · rintro rfl
      exact Persistence.appendBatch_logOnly_markers _ _ _ _ entry clean bounded fits size
    · intro c got
      let run := appendBatch (Persistence.ops e) policy (Persistence.historyCursor history) p
      have settled := Persistence.appendBatch_ack_clean policy e _ _ _ entry clean bounded fits size got
      change (Persistence.reached (run.run image)).powerLoss = Persistence.reached (run.run image) at settled
      change Persistence.acknowledged (run.run image) = some c at got
      change _ ∧ Persistence.Ready policy (Persistence.reached (run.run image)) _ ∧ _
      cases h : run.run image with
      | error => simp [h, Persistence.acknowledged] at got
      | ok value after =>
        cases value with
        | error => simp [h, Persistence.acknowledged] at got
        | ok cursor =>
          simp [h, Persistence.acknowledged] at got
          subst c
          obtain ⟨canonical, ready⟩ := Persistence.ready_after_ack entry p e h bounded fits size
          exact ⟨canonical, ready, by simpa only [h] using settled⟩
  | some admitted =>
    dsimp only
    rw [Persistence.tornAppend_withWritebacks _ _ _ _ _ _ clean]
    obtain ⟨dirty, markers⟩ := Persistence.tornAppend_dirty policy admitted.val image history p
      entry clean bounded fits size admitted.property.1 admitted.property.2
    refine ⟨dirty, fun _ => markers, ?_⟩
    have total := Persistence.encoded_history_size history 1 bounded
    rw [Persistence.tornAppend_stops _ _ _ _ _ size (by simp [Persistence.historyCursor])
      (by simp [Persistence.historyCursor]; omega) (by simp only [Persistence.historyCursor, frame_length]; omega)]
    cases admitted.val.abort <;> simp [Persistence.Abort.result, Persistence.acknowledged]

end WalRecoverySlice.Segmented.Model
