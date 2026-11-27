import Alvoki.Experiments.Manifest.Proofs
import Alvoki.Experiments.DurableBlob.Proofs
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

private theorem manifest_last_open (trace : DurableBlob.Allows initial events state)
    (last : events.getLast? = some (.opened version)) : state = .ready version := by
  cases trace with
  | initial => simp at last
  | next previous step =>
    simp at last
    subst_vars
    cases step
    rfl

/-- Decode the bytes returned by the actual successful blob reopen and
identify the same version in the typed manifest trace and settled image. -/
theorem manifest_open
    (run : DurableBlob.Run (L0Manifest.encode .empty) (events ++ [.opened bytes]) true image)
    (submitted : ∀ event ∈ events ++ [.opened bytes],
      event.Submitted (fun payload => ∃ v, L0Manifest.Version.Valid v ∧ L0Manifest.encode v = payload)) :
    ∃ observed version, DurableBlob.Allows L0Manifest.Version.empty observed (.ready version) ∧
      observed.getLast? = some (.opened version) ∧
      L0Manifest.decode bytes = some version ∧ L0Manifest.decode image.active = some version := by
  obtain ⟨observed, next, typed, related, final, values⟩ :=
    L0Manifest.trace_refines run.refinesReady submitted
  have last := congrArg List.getLast? related
  simp [List.getLast?_map] at last
  cases hit : observed.getLast? with
  | none => simp [hit] at last
  | some event =>
    cases event <;> simp [hit, DurableBlob.Event.map] at last
    rename_i opened
    have ready := manifest_last_open typed hit
    subst next
    have decoded : L0Manifest.decode (L0Manifest.encode opened) = some opened :=
      values (.opened opened) (List.mem_of_getLast? hit)
    refine ⟨observed, opened, typed, ?_, ?_, ?_⟩
    · exact hit
    · rw [← last, decoded]
    · simp [DurableBlob.State.map] at final
      rw [← final, decoded]

/-- The adapter decoded the returned bytes, and the selected manifest was
read from the active bytes of the same modeled successful reopen. -/
inductive ManifestOpenReceipt (selected actual : L0Manifest.Version) : Prop where
  | issued
      (run : DurableBlob.Run (L0Manifest.encode .empty) (events ++ [.opened bytes]) true image)
      (submitted : ∀ event ∈ events ++ [.opened bytes],
        event.Submitted (fun payload => ∃ v, v.Valid ∧ L0Manifest.encode v = payload))
      (decoded : L0Manifest.decode bytes = some actual)
      (projection : L0Manifest.decode image.active = some selected) :
      ManifestOpenReceipt selected actual

theorem ManifestOpenReceipt.effect (receipt : ManifestOpenReceipt selected actual) :
    actual = selected := by
  cases receipt with
  | issued run submitted decoded projection =>
    obtain ⟨_, _, _, _, issued, active⟩ := manifest_open run submitted
    exact Option.some.inj (decoded.symm.trans (issued.trans (active.symm.trans projection)))

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
