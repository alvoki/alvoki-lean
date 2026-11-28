import Alvoki.Experiments.L0.Refinement

namespace ExperimentalL0.RecoveryChoices
open WalRecoverySlice.Segmented

def walChoices : Contract.State → Contract.View → Prop
  | .online view, chosen => chosen = view
  | .offline known pending, chosen =>
      chosen = known ∨ pending.bind (fun request => request.apply known) = some chosen

def manifestChoices : DurableBlob.State L0Manifest.Version → L0Manifest.Version → Prop
  | .ready version, chosen => chosen = version
  | .offline known pending, chosen => DurableBlob.Permitted known pending chosen

private def walRecoveryEvent : Contract.Event → Prop
  | .stop | .openFailed | .opened _ => True
  | _ => False

private def manifestRecoveryEvent : DurableBlob.Event L0Manifest.Version → Prop
  | .stop | .openFailed | .opened _ => True
  | _ => False

private theorem wal_narrows (step : Contract.Step before event after)
    (recovery : walRecoveryEvent event) (allowed : walChoices after chosen) :
    walChoices before chosen := by
  cases step with
  | ack _ | uncertain | scan => contradiction
  | stop => exact allowed.elim (fun h => h) (by simp)
  | stopAgain | openFailed => exact allowed
  | opened permitted =>
    change chosen = _ at allowed
    cases allowed
    exact permitted

private theorem manifest_narrows (step : DurableBlob.Step before event after)
    (recovery : manifestRecoveryEvent event) (allowed : manifestChoices after chosen) :
    manifestChoices before chosen := by
  cases step with
  | published | uncertain => contradiction
  | stop => exact allowed.elim (fun h => h) (by simp)
  | stopAgain | openFailed => exact allowed
  | opened permitted =>
    change chosen = _ at allowed
    cases allowed
    exact permitted

/-- Between mutations, component recovery events can interleave. This also
covers closing a component that opened successfully during a failed LSM
recovery attempt and reopening it on the next attempt. -/
inductive Retry (walStart : Contract.State) (manifestStart : DurableBlob.State L0Manifest.Version) :
    Contract.State → DurableBlob.State L0Manifest.Version → Prop where
  | initial : Retry walStart manifestStart walStart manifestStart
  | wal : Retry walStart manifestStart wal manifest →
      Contract.Step wal event after → walRecoveryEvent event →
      Retry walStart manifestStart after manifest
  | manifest : Retry walStart manifestStart wal manifest →
      DurableBlob.Step manifest event after → manifestRecoveryEvent event →
      Retry walStart manifestStart wal after

/-- A fixed pair can represent all earlier steps of any recovery attempt
that can still select it. Each successful component open narrows its own
choice to a singleton; a later failure elsewhere cannot undo that choice. -/
theorem Retry.narrows (retry : Retry walStart manifestStart walEnd manifestEnd)
    (wal : walChoices walEnd view) (manifest : manifestChoices manifestEnd version) :
    walChoices walStart view ∧ manifestChoices manifestStart version := by
  induction retry with
  | initial => exact ⟨wal, manifest⟩
  | wal _ step event ih => exact ih (wal_narrows step event wal) manifest
  | manifest _ step event ih => exact ih wal (manifest_narrows step event manifest)

theorem Retry.opened (retry : Retry walStart manifestStart (.online view) (.ready version)) :
    walChoices walStart view ∧ manifestChoices manifestStart version :=
  retry.narrows rfl rfl

/-- An uncertain append can change only the WAL choice. The manifest comes
from the ready state that existed at the time of the append. -/
theorem Retry.afterAppend
    (retry : Retry (.offline old (some (.append batch))) (.ready version)
      (.online view) (.ready observed)) :
    (view = old ∨ view = old.append batch) ∧ observed = version := by
  have chosen := retry.opened
  by_cases room : old.tail < Contract.maxPosition
  · simpa [walChoices, manifestChoices, Contract.Request.apply, room, eq_comm (a := old.append batch)]
      using chosen
  · have unchanged : view = old ∧ observed = version := by
      simpa [walChoices, manifestChoices, Contract.Request.apply, room] using chosen
    exact ⟨.inl unchanged.1, unchanged.2⟩

/-- An uncertain flush can change only the manifest choice. The WAL has
already settled every write used to build the new table. -/
theorem Retry.afterPublish
    (retry : Retry (.online view) (.offline old (some proposal))
      (.online observed) (.ready version)) :
    observed = view ∧ (version = old ∨ version = proposal) := by
  simpa [walChoices, manifestChoices, DurableBlob.Permitted, eq_comm (a := proposal)]
    using retry.opened

/-- If a stopped LSM preserves every admitted selection, all partial
component recovery states still admit only durable LSM images. The table
catalog is framed throughout these read-only attempts. -/
theorem Retry.preservesDurability
    (retry : Retry walStart manifestStart walEnd manifestEnd)
    (historyFor : Contract.View → Rows)
    (before : ∀ view version, walChoices walStart view → manifestChoices manifestStart version →
      Nonempty (Durable ⟨view, version, tables⟩ (historyFor view)))
    (wal : walChoices walEnd view) (manifest : manifestChoices manifestEnd version) :
    Nonempty (Durable ⟨view, version, tables⟩ (historyFor view)) := by
  obtain ⟨w, m⟩ := retry.narrows wal manifest
  exact before view version w m

end ExperimentalL0.RecoveryChoices
