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

private theorem tornAppend_withWritebacks (cut : TornAppend) (schedule : WritebackSchedule)
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

end WalRecoverySlice.Persistence
