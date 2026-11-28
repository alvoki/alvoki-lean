import Alvoki.Experiments.L0.RecoveryChoices
import Alvoki.Experiments.WAL.Segmented.Proofs.NativeAppend

namespace ExperimentalL0.WalProducerHandoff

open WalRecoverySlice.Segmented

/-- The reached registration and the acquired child's lock are available
at the actual WAL reopen result. No selected view is supplied by L0. -/
theorem reopenAuthority (owned : Model.RootBinding directory lock) (root : Model.RootReports)
    (reports : Nat → Nat → WalRecoverySlice.SingleFile.OpenReports) (childError rootError : Option String)
    {start after : Model.State} (pending : Recoverable known request start.disk)
    (opened : (Model.publicOpenModel (.ok owned) root reports childError rootError).run (start, false) =
      .ok (.ok (.ready store session, ())) (after, true)) :
    after.activeEntry = some session.control.active ∧
      Model.AppendReady session (after, WalRecoverySlice.SingleFile.storedPhase store.activeChild) ∧
      ∃ (before : Model.State) (childAfter : WalRecoverySlice.SingleFile.OpenImage),
        WalRecoverySlice.SingleFile.openExistingModel (Native.segmentPath owned.root store.activeId)
          session.control.policy (reports before.step store.activeId)
          {image := before.disk.segment store.activeId} = .ok (.ok store.activeChild) childAfter ∧
        childAfter.held = true := by
  exact (Model.reopensWithAppendAuthority owned root reports childError rootError pending opened).2

/-- A failed reopen and two reached successful reopens provide the L0
retry selection for an uncertain append. -/
theorem retry (owned : Model.RootBinding directory lock) (failedAttempt first second : Model.RootReports)
    (reports : Nat → Nat → WalRecoverySlice.SingleFile.OpenReports)
    (childError rootError : Option String) {start failed returned final : Model.State}
    (pending : Recoverable original (some (.append batch)) start.disk)
    (failedOpen : match (Model.publicOpenModel (.ok owned) failedAttempt reports childError rootError).run (start, false) with
      | .ok (.error _) after | .error _ after => after.1 = failed
      | .ok (.ok _) _ => False)
    (opened : (Model.publicOpenModel (.ok owned) first reports childError rootError).run (failed, false) =
      .ok (.ok (.ready firstStore firstSession, ())) (returned, true))
    (reopened : (Model.publicOpenModel (.ok owned) second reports childError rootError).run (returned, false) =
      .ok (.ok (.ready secondStore secondSession, ())) (final, true)) :
    RecoveryChoices.Retry (.offline original (some (.append batch))) (.ready version)
      (.online secondSession.view) (.ready version) := by
  obtain ⟨selected, same⟩ := Model.publicAppendRecovery owned failedAttempt first second reports
    childError rootError pending failedOpen opened reopened
  rw [same]
  exact .wal (.wal .initial .openFailed trivial) (.opened selected) trivial

end ExperimentalL0.WalProducerHandoff
