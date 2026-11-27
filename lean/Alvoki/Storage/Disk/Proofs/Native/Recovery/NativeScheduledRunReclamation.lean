import Alvoki.Storage.Disk.Proofs.Native.Execution.NativeExecutionTrace

namespace Alvoki.Storage.DiskSession

open CheckpointPublication

private theorem NativeExecutionStep.completedObsoleteRunCollection
    (step : NativeExecutionStep before (.collectedObsoleteRuns held) after) :
    ∃ (next : NativeReadPosition before.history before.submissions)
      (seen : NativeObsoleteRunCollection before.ready.state),
      after = ⟨before.history, before.submissions, next⟩ ∧ seen.reports.held = held ∧
        NativeObsoleteRunCollectionStep before.ready seen next := by
  cases step with
  | collectObsoleteRuns _ seen next returned => exact ⟨next, seen, rfl, rfl, returned⟩

/-- Once a completed collector with the specified holds occurs, its first
occurrence reclaims this older unheld name. The prefix premise checks age
at the scheduled pass's own reached writer. The returned collector proof
carries its exact run map, protected bytes, custody and client replay into
the same ready position that starts the rest of the trace. -/
theorem NativeExecutionTrace.reclaimsAtFirstCompletedObsoleteRunCollection
    (trace : NativeExecutionTrace start events last) {held : List UInt64} {generation : UInt64}
    (index : Nat) (scheduled : .collectedObsoleteRuns held ∈ events) (unheld : generation ∉ held)
    (older : ∀ {priorEvents before after}, NativeExecutionTrace start priorEvents before →
      NativeExecutionStep before (.collectedObsoleteRuns held) after →
      List.IsPrefix (priorEvents ++ [.collectedObsoleteRuns held]) events →
      generation < before.ready.state.writer.installed.generation) :
    ∃ (priorEvents laterEvents : List NativeExecutionEvent) (before : NativeExecutionPosition)
      (next : NativeReadPosition before.history before.submissions)
      (seen : NativeObsoleteRunCollection before.ready.state),
      events = priorEvents ++ .collectedObsoleteRuns held :: laterEvents ∧
      .collectedObsoleteRuns held ∉ priorEvents ∧ NativeExecutionTrace start priorEvents before ∧
      seen.reports.held = held ∧ NativeObsoleteRunCollectionStep before.ready seen next ∧
      seen.atBarrier.syncDirectory.DurablyAbsent (generation, index) ∧
      next.state.writer.published.durable generation index = none ∧
      NativeExecutionTrace ⟨before.history, before.submissions, next⟩ laterEvents last := by
  induction trace with
  | empty => simp at scheduled
  | @step earlier before event after prior step ih =>
    by_cases earlierPass : .collectedObsoleteRuns held ∈ earlier
    · obtain ⟨priorEvents, laterEvents, atCollection, next, seen, ordered, first, ran, holds, returned, absent,
        durable, later⟩ := ih earlierPass
          (fun ran finished within => older ran finished (List.prefix_append_of_prefix within))
      refine ⟨priorEvents, laterEvents ++ [event], atCollection, next, seen, ?_, first, ran, holds, returned, absent,
        durable, .step later step⟩
      simp only [ordered, List.append_assoc, List.cons_append]
    · have current : event = .collectedObsoleteRuns held := by
        exact (List.mem_singleton.mp ((List.mem_append.mp scheduled).resolve_left earlierPass)).symm
      subst event
      have eligible := older prior step List.prefix_rfl
      obtain ⟨next, seen, rfl, holds, returned⟩ := step.completedObsoleteRunCollection
      have absent := returned.obsolete generation index eligible (holds.symm ▸ unheld)
      have durable : next.state.writer.published.durable generation index = none := by
        rw [returned.durable, RunUnlinkImage.guaranteed, absent.1, returned.settled]
        simp [absent.1]
      exact ⟨earlier, [], before, next, seen, rfl, earlierPass, prior, holds, returned, absent, durable, .empty⟩

end Alvoki.Storage.DiskSession
