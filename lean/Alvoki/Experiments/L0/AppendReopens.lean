import Alvoki.Experiments.L0.AppendRecovery
import Alvoki.Experiments.L0.WalProducerHandoff

namespace ExperimentalL0.WalProducerHandoff
open WalRecoverySlice
open WalRecoverySlice.Segmented (Contract.View PermittedView Recoverable)
open WalRecoverySlice.Segmented

/-- The model primitive reports for one concrete call to public WAL open. -/
structure OpenAttempt (directory lock : Type) where
  owned : Model.RootBinding directory lock
  root : Model.RootReports
  reports : Nat → Nat → SingleFile.OpenReports
  childError : Option String
  unlockError : Option String

abbrev OpenAttempt.run (o : OpenAttempt directory lock) (s : Model.State) :=
  (Model.publicOpenModel (.ok o.owned) o.root o.reports o.childError o.unlockError).run (s, false)

def OpenAttempt.opened (o : OpenAttempt directory lock) (s t : Model.State)
    (store : Model.ReopenedStore directory lock) (wal : WalRecoverySlice.Segmented.Session) :=
  o.run s = .ok (.ok (.ready store wal, ())) (t, true)

/-- Each attempt actually returned an error on the state produced by its
predecessor. The root is released before the next acquisition. -/
inductive FailedOpens (dir lock : Type) (root : System.FilePath) : Nat → Model.State → Model.State → Prop where
  | nil : FailedOpens dir lock root 0 s s
  | next {o : OpenAttempt dir lock} : FailedOpens dir lock root n s t → o.owned.root = root →
      (match o.run t with
      | .error _ reached | .ok (.error _) reached => reached = (u, false)
      | .ok (.ok _) _ => False) →
      FailedOpens dir lock root (n + 1) s u

theorem FailedOpens.recoverable (steps : FailedOpens dir lock root n s t)
    (prior : Recoverable known pending s.disk) : Recoverable known pending t.disk := by
  induction steps with
  | nil => exact prior
  | @next _ s t u o _ _ failed ih =>
    have post := Model.publicOpenModel_refines (.ok o.owned) o.root o.reports o.childError o.unlockError t (ih prior)
    generalize ran : o.run t = res at failed
    change (match o.run t with | .ok (.ok (.ready _ _, ())) (_, _) => _ | .ok (.ok _) _ => _ | .ok (.error _) (_, _) => _ | .error _ (_, _) => _) at post
    rw [ran] at post
    cases res with
    | error _ p => obtain rfl := failed; exact post.2
    | ok reply p =>
      cases reply with
      | ok => contradiction
      | error => obtain rfl := failed; exact post.2.1

/-- Successful recovery returns both an installed WAL and the specific
registered single-file authority that the next public close/append uses. -/
structure Authority (o : OpenAttempt directory lock) (store : Model.ReopenedStore directory lock)
    (wal : WalRecoverySlice.Segmented.Session) (t : Model.State) : Prop where
  disk : WalRecoverySlice.Segmented.Installed wal t.disk
  registered : t.activeEntry = some wal.control.active
  ready : Model.AppendReady wal (t, SingleFile.storedPhase store.activeChild)
  acquired : ∃ (before : Model.State) (childAfter : SingleFile.OpenImage),
    SingleFile.openExistingModel (WalRecoverySlice.Segmented.Native.segmentPath o.owned.root store.activeId) wal.control.policy
      (o.reports before.step store.activeId) {image := before.disk.segment store.activeId} =
      .ok (.ok store.activeChild) childAfter ∧ childAfter.held = true

theorem reopenAfterWrite (o : OpenAttempt directory lock) (pending : Recoverable known request s.disk)
    (opened : o.opened s t store wal) :
    PermittedView known request wal.view ∧ Authority o store wal t := by
  have post := Model.publicOpenModel_refines (.ok o.owned) o.root o.reports o.childError o.unlockError s pending
  unfold OpenAttempt.opened OpenAttempt.run at opened
  rw [opened] at post
  obtain ⟨reg, ready, acquired⟩ := reopenAuthority o.owned o.root o.reports o.childError o.unlockError pending opened
  exact ⟨post.2.2.2.2.1, post.2.2.2.1, reg, ready, acquired⟩

def reopenedState (store : Model.ReopenedStore directory lock)
    (wal : WalRecoverySlice.Segmented.Session) (s : Model.State) : Model.AppendCloseState :=
  ⟨s, .ready store.activeId wal, SingleFile.storedPhase store.activeChild, true, true⟩

def closedState (s : Model.State) : Model.AppendCloseState :=
  ⟨{s with activeEntry := none}, .closed, .closed, false, false⟩

/-- Even a close reporting an unlock error takes the registered slot and
produces the state supplied to the next public open. -/
theorem closeReopened (auth : Authority o store wal s) (close : SingleFile.OpenReports) (unlock : Option String) :
    let action := (Model.publicAppendClose wal.control.policy close unlock).run (reopenedState store wal s)
    (match action with | .ok () reached | .error _ reached => reached = closedState s) ∧
      Recoverable wal.view none (closedState s).state.disk := by
  let live := reopenedState store wal s
  have custody : live.ChildCustody := Model.AppendReady.closeCustody auth.ready auth.registered rfl
  have released := Model.publicAppendClose_releases wal.control.policy close unlock live (by simp [live, reopenedState]) rfl custody
  dsimp only
  change (match (Model.publicAppendClose wal.control.policy close unlock).run live with
    | .ok () reached | .error _ reached => _) ∧ _
  rw [released]
  constructor
  · by_cases child : (live.state.activeEntry.isSome && close.unlockError) = true
    · simp only [child, ite_true]; rfl
    · rw [ite_eq_right child]; cases unlock <;> rfl
  · exact auth.disk.offline (.inl rfl)


/-- All the reported public operations between a released append and the
second published session. The middle close consumes the first returned slot. -/
structure Reopens (directory lock : Type) (root : System.FilePath) (start : Model.State) where
  failures : Nat
  retryState : Model.State
  retries : FailedOpens directory lock root failures start retryState
  first : OpenAttempt directory lock
  firstRoot : first.owned.root = root
  firstStore : Model.ReopenedStore directory lock
  firstWal : WalRecoverySlice.Segmented.Session
  returned : Model.State
  opened : first.opened retryState returned firstStore firstWal
  close : SingleFile.OpenReports
  unlock : Option String
  second : OpenAttempt directory lock
  secondRoot : second.owned.root = root
  finalStore : Model.ReopenedStore directory lock
  finalWal : WalRecoverySlice.Segmented.Session
  finalState : Model.State
  reopened : second.opened (closedState returned).state finalState finalStore finalWal

def Reopens.clientEvents (r : Reopens directory lock root start) (events : List Event) (change : Change) :=
  (((((events ++ [.writeUncertain change]) ++ [.stop]) ++ List.replicate r.failures .openFailed) ++
    [.reopened]) ++ [.stop]) ++ [.reopened]

structure ReopenedTwice (r : Reopens directory lock root start) (events : List Event)
    (change : Change) (image : Selected) : Prop where
  selected : PermittedView image.view (some (.append (encode change))) r.firstWal.view
  first : Authority r.first r.firstStore r.firstWal r.returned
  released : match (Model.publicAppendClose r.firstWal.control.policy r.close r.unlock).run
      (reopenedState r.firstStore r.firstWal r.returned) with
    | .ok () reached | .error _ reached => reached = closedState r.returned
  pinned : r.finalWal.view = r.firstWal.view
  second : Authority r.second r.finalStore r.finalWal r.finalState
  run : let chosen := {image with view := r.finalWal.view}
    Execution.Run (r.clientEvents events change) (some chosen.replaySession) chosen

theorem Reopens.refines (r : Reopens directory lock root start) (run : Execution.Run events (some session) image)
    (pending : Recoverable image.view (some (.append (encode change))) start.disk) :
    ReopenedTwice r events change image := by
  obtain ⟨permitted, first⟩ := reopenAfterWrite r.first (r.retries.recoverable pending) r.opened
  obtain ⟨released, pinned⟩ := closeReopened first r.close r.unlock
  obtain ⟨same, second⟩ := reopenAfterWrite r.second pinned r.reopened
  have sameView : r.finalWal.view = r.firstWal.view := same.elim id (by simp)
  have choice : r.finalWal.view = image.view ∨ r.finalWal.view = image.view.append (encode change) := by
    rw [sameView]
    rcases permitted with old | updated
    · exact .inl old
    · right
      by_cases room : image.view.tail < Contract.maxPosition <;> simp_all [Contract.Request.apply]
  exact ⟨permitted, first, released, sameView, second,
    ((run.uncertainAtView choice).stop.failedOpens r.failures).reopenSelected.stop.reopenSelected⟩

structure AppendCall (change : Change) where
  root : System.FilePath
  held : Nat
  removal : Model.RootReports
  effects : Model.Effects
  create : SingleFile.CreateReports
  close : SingleFile.OpenReports
  reports : ∀ policy cursor, SingleFile.AppendReports policy cursor (encode change)

abbrev AppendCall.run (call : AppendCall change) (wal : WalRecoverySlice.Segmented.Session)
    (before : Model.AppendCloseState) :=
  let action := fun (_ : Nat) (current : WalRecoverySlice.Segmented.Session) =>
    Model.nativeAppendModel call.root call.held call.removal call.effects call.create call.close
      current current.control.active (call.reports current.control.policy)
  (WalRecoverySlice.Segmented.Native.appendPositionWith (Model.publicAppendActiveModel action)).run
    ((before.state, before.child), .ready call.held wal)

def reachedClose (call : AppendCall change) (unlock : Option String) (wal : WalRecoverySlice.Segmented.Session)
    (before : Model.AppendCloseState) (after : Model.State × SingleFile.AppendPhase) (phase : WalRecoverySlice.Segmented.Native.Phase Nat) :=
  (Model.publicAppendClose wal.control.policy call.close unlock).run
    (Model.appendCloseState before after phase (decide (wal.activeCount = wal.control.capacity)))

def closeWorld (res : EStateM.Result String Model.AppendCloseState Unit) : Model.AppendCloseState :=
  match res with | .ok () reached | .error _ reached => reached

/-- A public append error is observed before close. Even if close reports an
error after performing release, retry starts on exactly that stopped disk. -/
theorem reportedWriteTwice (call : AppendCall change) (unlock : Option String)
    (wal : WalRecoverySlice.Segmented.Session) (before : Model.AppendCloseState)
    (rootHeld : before.rootHeld = true) (childHeld : before.childHeld = true)
    (ready : Model.AppendReady wal (before.state, before.child))
    (registered : before.state.activeEntry = some wal.control.active)
    (room : wal.view.tail < Contract.maxPosition) (linux : System.Platform.isWindows = false)
    (reported : call.run wal before = .ok (.error err) (after, phase))
    (r : Reopens directory lock call.root (closeWorld (reachedClose call unlock wal before after phase)).state)
    (run : Execution.Run events (some session) image) (bound : wal.view = image.view) :
    let released := closeWorld (reachedClose call unlock wal before after phase)
    released.rootHeld = false ∧ released.childHeld = false ∧
      Recoverable image.view (some (.append (encode change))) released.state.disk ∧
      ReopenedTwice r events change image := by
  obtain ⟨release, hr, hc, pending, ended⟩ := reportedWrite call.root call.held call.removal
    call.effects call.create call.close unlock wal call.reports before rootHeld childHeld ready registered
    (encode_size change) room linux reported
  dsimp only at ended
  have same : closeWorld (reachedClose call unlock wal before after phase) = release := by
    change (match reachedClose call unlock wal before after phase with
      | .ok () reached | .error _ reached => reached = release) at ended
    unfold closeWorld
    cases hn : reachedClose call unlock wal before after phase <;> simpa [hn] using ended
  rw [bound] at pending
  have selected := r.refines run (same.symm ▸ pending)
  exact ⟨same.symm ▸ hr, same.symm ▸ hc, same.symm ▸ pending, selected⟩

end ExperimentalL0.WalProducerHandoff
