import Alvoki.Experiments.L0.Trace
import Alvoki.Experiments.L0.RecoveryChoices
import Alvoki.Experiments.L0.CodecProofs
import Alvoki.Experiments.Manifest.Proofs
import Alvoki.Experiments.DurableBlob.Proofs
import Alvoki.Experiments.SSTable.Proofs.Reader
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
  | ack applied => exact (Option.some.inj applied).symm

theorem manifest_trace {initial : ByteArray}
    (run : DurableBlob.Run initial events online image)
    (empty : initial = L0Manifest.encode .empty)
    (submitted : ∀ event ∈ events,
      event.Submitted (fun bytes => ∃ v, L0Manifest.Version.Valid v ∧ L0Manifest.encode v = bytes)) :
    ∃ observed next, DurableBlob.Allows L0Manifest.Version.empty observed next ∧
      observed.map (DurableBlob.Event.map L0Manifest.encode) = events := by
  subst initial
  obtain ⟨state, allowed, _⟩ := run.refines
  obtain ⟨observed, next, typed, related, _, _⟩ := L0Manifest.trace_refines allowed submitted
  exact ⟨observed, next, typed, related⟩

private theorem manifest_last_publish (trace : DurableBlob.Allows initial events state)
    (last : events.getLast? = some (.published version)) : state = .ready version := by
  cases trace with
  | initial => simp at last
  | next previous step =>
    simp at last
    subst_vars
    cases step
    rfl

theorem manifest_publish
    (run : DurableBlob.Run (L0Manifest.encode .empty)
      (events ++ [.published (L0Manifest.encode proposal)]) true image)
    (submitted : ∀ event ∈ events ++ [.published (L0Manifest.encode proposal)],
      event.Submitted (fun bytes => ∃ v, L0Manifest.Version.Valid v ∧ L0Manifest.encode v = bytes))
    (valid : proposal.Valid) :
    L0Manifest.decode image.active = some proposal := by
  obtain ⟨observed, next, typed, related, final, _⟩ :=
    L0Manifest.trace_refines run.refinesReady submitted
  have last := congrArg List.getLast? related
  simp [List.getLast?_map] at last
  cases hit : observed.getLast? with
  | none => simp [hit] at last
  | some event =>
    cases event <;> simp [hit, DurableBlob.Event.map] at last
    rename_i published
    have ready := manifest_last_publish typed hit
    subst next
    simp [DurableBlob.State.map] at final
    rw [← final, last, L0Manifest.decode_encode valid]

end ExperimentalL0.NativeBridge
