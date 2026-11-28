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

/-- Reading the cached view of a reached WAL session is a public scan of
the exact installed state. No independent scan-content premise is needed. -/
theorem wal_scan (prior : Run events (.online session state)) :
    Contract.Allows (events ++ [.scan session.view]) (.online session.view) :=
  (Run.scan prior).refinesOnline

/-- A successful WAL reopen contributes the public recovery step for the
session that was actually returned, including after a prior failed open. -/
theorem wal_open (prior : Run events (.offline state))
    (issued : (reopen (Model.ops effects)).run state = .ok (.ok session) after) :
    ∃ previous, Contract.Allows events previous ∧
      Contract.Step previous (.opened session.view) (.online session.view) :=
  wal_trace_snoc (Run.opened prior effects issued).refinesOnline rfl

/-- Read the returned session's cached view, separately from the public
trace used to identify the selected image. -/
inductive WalScanReceipt (selected : Contract.View) : Contract.View → Prop where
  | issued (prior : Run events (.online session state))
      (projection : Contract.Allows events (.online selected)) :
      WalScanReceipt selected session.view

theorem WalScanReceipt.effect (receipt : WalScanReceipt selected result) :
    result = selected := by
  cases receipt with
  | issued prior projection =>
    obtain ⟨_, before, observed⟩ := wal_trace_snoc (wal_scan prior) rfl
    have same := wal_trace_unique before projection
    cases same
    cases observed
    rfl

/-- The observed reopen is the successful result of the reached WAL
schedule. Its selected view is indexed by the same public trace. -/
inductive WalOpenReceipt (selected : Contract.View) : Contract.View → Prop where
  | issued (prior : Run events (.offline state))
      (returned : (reopen (Model.ops effects)).run state = .ok (.ok session) after)
      (projection : Contract.Allows (events ++ [.opened session.view]) (.online selected)) :
      WalOpenReceipt selected session.view

theorem WalOpenReceipt.effect (receipt : WalOpenReceipt selected result) :
    result = selected := by
  cases receipt with
  | issued prior returned projection =>
    obtain ⟨_, trace, step⟩ := wal_open prior returned
    exact Contract.State.online.inj (wal_trace_unique (trace.next step) projection)

end ExperimentalL0.NativeBridge
