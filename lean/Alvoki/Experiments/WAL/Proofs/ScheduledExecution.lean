import Alvoki.Experiments.WAL.Proofs.Execution
import Alvoki.Experiments.WAL.Proofs.AppendWriteback
import Alvoki.Experiments.WAL.Proofs.ReopenWriteback

namespace WalRecoverySlice.Persistence

/-- Both observed acknowledgements and unresolved attempts use the exact
result of the append with scheduled pre-callback writebacks. -/
theorem Run.appendWithWritebacks {policy events image cursor cached} (p : Bytes)
    (prior : Run policy events (.online image cursor cached)) (effects : Effects) (schedule : WritebackSchedule) :
    let result := (appendBatch (scheduledOps (ops effects) schedule) policy cursor p).run image
    (∀ next after, result = .ok (.ok next) after →
      Run policy (events ++ [.ack p]) (.online after next (cached ++ [p]))) ∧
    Run policy (events ++ [.uncertain p]) (.offline (reached result)) := by
  dsimp only
  rw [appendBatch_withWritebacks effects schedule policy cursor p image prior.onlineImageClean]
  exact ⟨fun _ _ returned => .ack prior (appendEffects effects schedule) returned,
    .uncertain prior (appendEffects effects schedule)⟩

private theorem Run.settleOffline {policy events image} (prior : Run policy events (.offline image))
    (files : List WalFile) : Run policy events (.offline (settleFiles files image)) := by
  induction files generalizing image with
  | nil => exact prior
  | cons file rest ih =>
    exact ih (.writeback prior (file.writeback image))

theorem tornAppend_withWritebacks (cut : TornAppend) (schedule : WritebackSchedule)
    (policy : Policy) (cursor : Cursor) (p : Bytes) (image : Image) (clean : image.powerLoss = image) :
    (appendBatch (scheduledOps cut.ops schedule) policy cursor p).run image =
      (appendBatch cut.ops policy cursor p).run image := by
  unfold appendBatch
  dsimp only
  split <;> first | rfl | skip
  split <;> first | rfl | skip
  obtain ⟨live, durable, abort⟩ := cut
  have settled := settleFiles_clean schedule.appendData image clean
  cases abort <;> simp [scheduledOps, TornAppend.ops, withWritebacks, settled, Bind.bind,
    ExceptT.run, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, EStateM.bind, Abort.result]

/-- Scheduled writes before the interrupted append are inert on the
settled entry. Later callbacks, including their schedules, stay unreached. -/
theorem Run.tornAppendWithWritebacks {policy events image cursor cached p}
    (prior : Run policy events (.online image cursor cached)) (cut : TornAppend) (schedule : WritebackSchedule)
    (sized : p.length ≤ 32) (fits : cursor.nextSeq ≤ 255)
    (extent : cut.SameExtent p) (detected : policy = .logOnly → cut.Detected cursor.nextSeq) :
    Run policy (events ++ [.uncertain p])
      (.offline (reached ((appendBatch (scheduledOps cut.ops schedule) policy cursor p).run image))) := by
  rw [tornAppend_withWritebacks cut schedule policy cursor p image prior.onlineImageClean]
  exact .tornAppend prior cut sized fits extent detected

private theorem Result.reached_writeback (files : List WalFile) (result : Result α) :
    reached (Result.writeback files result) = settleFiles files (reached result) := by
  cases result <;> rfl

/-- A recovery with independent pre-callback writebacks has the same
client transition as its actual return. A caller that loses the response
can instead keep the exact reached image offline. -/
theorem Run.reopenWithWritebacks {policy events image} (prior : Run policy events (.offline image))
    (effects : Effects) (schedule : WritebackSchedule) :
    let result := (reopen (scheduledOps (ops effects) schedule) policy).run image
    (match result with
      | .ok (.ok decoded) after => Run policy (events ++ [.opened decoded.batches])
          (.online after decoded.cursor decoded.batches)
      | .ok (.error _) after => Run policy (events ++ [.openFailed]) (.offline after)
      | .error _ after => Run policy (events ++ [.stop]) (.offline after)) ∧
    Run policy (events ++ [.stop]) (.offline (reached result)) := by
  dsimp only
  obtain ⟨first, last, normalized⟩ := reopen_writeback_normalizes effects schedule policy image
  rw [normalized, Result.reached_writeback]
  have start := prior.settleOffline first
  have abandoned := start.abandonOpen effects
  refine ⟨?_, abandoned.settleOffline last⟩
  cases returned : (reopen (ops effects) policy).run (settleFiles first image) with
  | error _ after =>
    rw [returned] at abandoned
    exact abandoned.settleOffline last
  | ok result after =>
    cases result with
    | error diagnostic =>
      exact (start.failed effects returned).settleOffline last
    | ok decoded =>
      have opened := start.opened effects returned
      have clean := settleFiles_clean last after opened.onlineImageClean
      simpa only [Result.writeback, clean] using opened

theorem appendPrimitive_refines (effects : Effects) (schedule : WritebackSchedule) (policy : Policy)
    (image : Image) (history : List Bytes) (p : Bytes)
    (cut : Option {c : TornAppend // c.SameExtent p ∧ (policy = .logOnly → c.Detected (historyCursor history).nextSeq)})
    (entry : Ready policy image history) (clean : image.powerLoss = image)
    (bounded : ∀ b ∈ history, b.length ≤ 32) (fits : history.length < 255) (size : p.length ≤ 32) :
    let r := (appendBatch (scheduledOps (appendPrimitives effects (cut.map Subtype.val)) schedule) policy (historyCursor history) p).run image
    Dirty policy history (some p) (reached r) ∧
    (policy = .logOnly → (reached r).MarkersSettled) ∧
    ∀ c, acknowledged r = some c →
      c = historyCursor (history ++ [p]) ∧
      Ready policy (reached r) (history ++ [p]) ∧
      (reached r).powerLoss = reached r := by
  cases cut with
  | none =>
    dsimp only [Option.map, appendPrimitives]
    rw [appendBatch_withWritebacks _ _ _ _ _ _ clean]
    let e := appendEffects effects schedule
    refine ⟨appendBatch_dirty policy e _ _ _ entry clean bounded fits size, ?_, ?_⟩
    · rintro rfl
      exact appendBatch_logOnly_markers _ _ _ _ entry clean bounded fits size
    · intro c got
      let run := appendBatch (ops e) policy (historyCursor history) p
      have settled := appendBatch_ack_clean policy e _ _ _ entry clean bounded fits size got
      change (reached (run.run image)).powerLoss = reached (run.run image) at settled
      change acknowledged (run.run image) = some c at got
      change _ ∧ Ready policy (reached (run.run image)) _ ∧ _
      cases h : run.run image with
      | error => simp [h, acknowledged] at got
      | ok value after =>
        cases value with
        | error => simp [h, acknowledged] at got
        | ok cursor =>
          simp [h, acknowledged] at got
          subst c
          obtain ⟨canonical, ready⟩ := ready_after_ack entry p e h bounded fits size
          exact ⟨canonical, ready, by simpa only [h] using settled⟩
  | some admitted =>
    dsimp only [Option.map, appendPrimitives]
    rw [tornAppend_withWritebacks _ _ _ _ _ _ clean]
    obtain ⟨dirty, markers⟩ := tornAppend_dirty policy admitted.val image history p
      entry clean bounded fits size admitted.property.1 admitted.property.2
    refine ⟨dirty, fun _ => markers, ?_⟩
    have total := encoded_history_size history 1 bounded
    rw [tornAppend_stops _ _ _ _ _ size (by simp [historyCursor])
      (by simp [historyCursor]; omega) (by simp only [historyCursor, frame_length]; omega)]
    cases admitted.val.abort <;> simp [Abort.result, acknowledged]


end WalRecoverySlice.Persistence
