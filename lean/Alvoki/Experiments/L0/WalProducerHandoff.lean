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

/-- The higher layer can hand a reported append's reached disk directly
to its recovery interpretation after closing the WAL. -/
theorem reportedWrite (root : System.FilePath) (held : Nat)
    (removal : Model.RootReports) (effects : Model.Effects)
    (create : WalRecoverySlice.SingleFile.CreateReports) (close : WalRecoverySlice.SingleFile.OpenReports)
    (unlockError : Option String) (session : WalRecoverySlice.Segmented.Session)
    (reports : ∀ policy cursor, WalRecoverySlice.SingleFile.AppendReports policy cursor batch)
    (before : Model.AppendCloseState) (rootHeld : before.rootHeld = true) (childHeld : before.childHeld = true)
    (ready : Model.AppendReady session (before.state, before.child))
    (registered : before.state.activeEntry = some session.control.active)
    (size : batch.length ≤ 32) (position : session.view.tail < Contract.maxPosition)
    (linux : System.Platform.isWindows = false)
    (returned :
      let action := fun (_ : Nat) (current : WalRecoverySlice.Segmented.Session) =>
        Model.nativeAppendModel root held removal effects create close current current.control.active
          (reports current.control.policy)
      (Native.appendPositionWith (Model.publicAppendActiveModel action)).run
        ((before.state, before.child), .ready held session) = .ok (.error err) (after, reachedPhase)) :
    ∃ released : Model.AppendCloseState,
      released.rootHeld = false ∧ released.childHeld = false ∧
      Recoverable session.view (some (.append batch)) released.state.disk ∧
      let closeResult :=
        (Model.publicAppendClose session.control.policy close unlockError).run
          (Model.appendCloseState before after reachedPhase (decide (session.activeCount = session.control.capacity)))
      match closeResult with
      | .ok () reached | .error _ reached => reached = released := by
  obtain ⟨disk, closed⟩ := Model.publicNativeAppend_reportedClose root held removal effects create close
    unlockError session reports before rootHeld childHeld ready registered size position linux returned
  let released : Model.AppendCloseState := ⟨{after.1 with activeEntry := none}, .closed, .closed, false, false⟩
  refine ⟨released, rfl, rfl, disk, ?_⟩
  dsimp only at closed ⊢
  rw [closed]
  by_cases childError : (after.1.activeEntry.isSome && close.unlockError) = true <;>
    cases unlockError <;> simp [childError, released]

end ExperimentalL0.WalProducerHandoff
