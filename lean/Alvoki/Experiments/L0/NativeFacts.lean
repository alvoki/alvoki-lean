import Alvoki.Experiments.WAL.Segmented.Proofs.Execution

namespace ExperimentalL0.NativeBridge
open WalRecoverySlice.Segmented

private theorem wal_step_unique (left : Contract.Step start event a)
    (right : Contract.Step start event b) : a = b := by
  cases left <;> cases right <;> simp_all

private theorem wal_trace_empty (trace : Contract.Allows events state)
    (empty : events = []) : state = .online {base := 0, batches := []} := by
  cases trace with
  | fresh => rfl
  | next => simp at empty

private theorem wal_trace_snoc (trace : Contract.Allows observed state)
    (last : observed = events ++ [event]) :
    ∃ prior, Contract.Allows events prior ∧ Contract.Step prior event state := by
  cases trace with
  | fresh => simp at last
  | next previous step =>
    obtain ⟨rfl, rfl⟩ := List.append_singleton_inj.mp last
    exact ⟨_, previous, step⟩

private theorem wal_trace_unique (left : Contract.Allows events a)
    (right : Contract.Allows events b) : a = b := by
  induction left generalizing b with
  | fresh => exact (wal_trace_empty right rfl).symm
  | next _ step ih =>
    obtain ⟨_, earlier, following⟩ := wal_trace_snoc right rfl
    exact wal_step_unique step (ih earlier ▸ following)

theorem wal_append
    (prior : Run events (.online before state))
    (issued : (requestCall effects before (.append batch)).run state = .ok (.ok next) after) :
    next.view = before.view.append batch := by
  have trace := (Run.ack prior effects (.append batch) issued).refinesOnline
  obtain ⟨_, earlier, step⟩ := wal_trace_snoc trace rfl
  have same := wal_trace_unique earlier prior.refinesOnline
  cases same
  cases step with
  | ack applied =>
    simp only [Contract.Request.apply] at applied
    split at applied
    · exact (Option.some.inj applied).symm
    · contradiction

end ExperimentalL0.NativeBridge
