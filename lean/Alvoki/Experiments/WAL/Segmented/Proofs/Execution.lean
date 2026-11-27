import Alvoki.Experiments.WAL.Segmented.Proofs.Append
import Alvoki.Experiments.WAL.Segmented.Proofs.Artifacts
import Alvoki.Experiments.WAL.Segmented.Proofs.Bootstrap
import Alvoki.Experiments.WAL.Segmented.Proofs.Discard
import Alvoki.Experiments.WAL.Segmented.Proofs.Reopen
import Alvoki.Experiments.WAL.Segmented.Proofs.Retention
import Alvoki.Experiments.WAL.Segmented.Proofs.Writeback

/-! Finite client executions of the shared segmented source schedules. -/

namespace WalRecoverySlice.Segmented

open WalRecoverySlice.Segmented.Contract (Event Request Allows)

def requestCall (effects : Model.Effects) (session : Session) : Request → Model.M Session
  | .append p => append (Model.ops effects) session p
  | .discardThrough k => discardThrough (Model.ops effects) session k

private theorem request_refines (effects : Model.Effects) (session : Session) (request : Request)
    (state : Model.State) (installed : Installed session state.disk) :
    Model.DiskPost
      (fun next disk => Installed next disk ∧ request.apply session.view = some next.view)
      (Recoverable session.view (some request)) ((requestCall effects session request).run state) := by
  cases request
  · exact append_refines _ _ _ _ installed
  · exact discard_refines _ _ _ _ installed

inductive Running where
  | online (session : Session) (state : Model.State)
  | offline (state : Model.State)

inductive Restart where
  | processExit
  | powerLoss

def Restart.after (mode : Restart) (state : Model.State) : Model.State :=
  match mode with
  | .processExit => state
  | .powerLoss => {state with disk := state.disk.powerLoss}

/-- A trace records client operations and observed replies. An append or
release can finish before its reply is lost. Background file writeback
between attempts changes only the offline disk. -/
inductive Run : List Event → Running → Prop where
  | created (effects : Model.Effects) (policy : Policy) (capacity : Nat)
      (positive : 0 < capacity) (fits : capacity ≤ 255)
      (got : (create (Model.ops effects) policy capacity).run {} = .ok (.ok session) state) :
      Run [] (.online session state)
  | ack (prior : Run events (.online session state)) (effects : Model.Effects) (request : Request)
      (got : (requestCall effects session request).run state = .ok (.ok next) after) :
      Run (events ++ [.ack request]) (.online next after)
  | uncertain (prior : Run events (.online session state)) (effects : Model.Effects) (request : Request) :
      Run (events ++ [.uncertain request])
        (.offline (Model.reached ((requestCall effects session request).run state)))
  | stopped (prior : Run events (.online session state)) (mode : Restart) :
      Run (events ++ [.stop]) (.offline (mode.after state))
  | stoppedAgain (prior : Run events (.offline state)) (mode : Restart) :
      Run (events ++ [.stop]) (.offline (mode.after state))
  | writeback (prior : Run events (.offline state)) (id : Nat) (file : Persistence.WalFile) :
      Run events (.offline { state with disk := state.disk.writeback id file })
  | artifact (prior : Run events (.offline state)) (id : Nat) (image : Model.DataImage) (live durable : Bool)
      (unselected : ∀ c, state.disk.liveControl = some c ∨ state.disk.durableControl = some c → ¬ c.selects id) :
      Run events (.offline { state with disk := state.disk.withArtifact id image live durable })
  | failed (prior : Run events (.offline state)) (effects : Model.Effects)
      (got : (reopen (Model.ops effects)).run state = .ok (.error error) after) :
      Run (events ++ [.openFailed]) (.offline after)
  | abandonOpen (prior : Run events (.offline state)) (effects : Model.Effects) :
      Run (events ++ [.stop]) (.offline (Model.reached ((reopen (Model.ops effects)).run state)))
  | opened (prior : Run events (.offline state)) (effects : Model.Effects)
      (got : (reopen (Model.ops effects)).run state = .ok (.ok session) after) :
      Run (events ++ [.opened session.view]) (.online session after)
  | scan (prior : Run events (.online session state)) :
      Run (events ++ [.scan session.view]) (.online session state)

private inductive Represents : Running → Contract.State → Prop where
  | online (installed : Installed session state.disk) :
      Represents (.online session state) (.online session.view)
  | offline (recoverable : Recoverable view request state.disk) :
      Represents (.offline state) (.offline view request)

private theorem restart_frames {known request} (state : Model.State) (mode : Restart)
    (allowed : Recoverable known request state.disk) : Recoverable known request (mode.after state).disk := by
  cases mode
  · exact allowed
  · exact allowed.powerLoss

private theorem sound {events running} (run : Run events running) :
    ∃ abstract, Allows events abstract ∧ Represents running abstract := by
  induction run with
  | created effects policy capacity positive fits got =>
    have step := Model.create_returns_ready effects policy positive fits
    rw [got] at step
    obtain ⟨rfl, live, durable, ready⟩ := step
    exact ⟨_, .fresh, .online ⟨[], rfl, ready, live, durable⟩⟩
  | ack prior effects request got ih =>
    obtain ⟨_, allowed, represented⟩ := ih
    cases represented with
    | online installed =>
      have step := request_refines effects _ request _ installed
      rw [got] at step
      exact ⟨_, .next allowed (.ack step.2), .online step.1⟩
  | @uncertain events session state prior effects request ih =>
    obtain ⟨_, allowed, represented⟩ := ih
    cases represented with
    | online installed =>
      have step := request_refines effects session request state installed
      refine ⟨_, .next allowed .uncertain, .offline ?_⟩
      cases got : (requestCall effects session request).run state with
      | error _ after =>
        rw [got] at step
        exact step
      | ok answer after =>
        rw [got] at step
        cases answer with
        | error _ => exact step
        | ok _ => exact step.1.offline (.inr step.2)
  | stopped prior mode ih =>
    obtain ⟨_, allowed, represented⟩ := ih
    cases represented with
    | online installed =>
      exact ⟨_, .next allowed .stop, .offline (restart_frames _ mode (installed.offline (.inl rfl)))⟩
  | stoppedAgain prior mode ih =>
    obtain ⟨_, allowed, represented⟩ := ih
    cases represented with
    | offline canOpen =>
      exact ⟨_, .next allowed .stopAgain, .offline (restart_frames _ mode canOpen)⟩
  | writeback prior id file ih =>
    obtain ⟨_, allowed, represented⟩ := ih
    cases represented with
    | offline canOpen =>
      exact ⟨_, allowed, .offline (canOpen.writeback id file)⟩
  | artifact prior id image live durable unselected ih =>
    obtain ⟨_, allowed, represented⟩ := ih
    cases represented with
    | offline canOpen =>
      exact ⟨_, allowed, .offline ((Recoverable.withUnselectedArtifact unselected image live durable).mpr canOpen)⟩
  | failed prior effects got ih =>
    obtain ⟨_, allowed, represented⟩ := ih
    cases represented with
    | offline canOpen =>
      have step := Model.reopen_refines effects _ canOpen
      rw [got] at step
      exact ⟨_, .next allowed .openFailed, .offline step⟩
  | @abandonOpen events state prior effects ih =>
    obtain ⟨_, allowed, represented⟩ := ih
    cases represented with
    | offline canOpen =>
      have step := Model.reopen_refines effects state canOpen
      refine ⟨_, .next allowed .stopAgain, .offline ?_⟩
      cases got : (reopen (Model.ops effects)).run state with
      | error _ after =>
        rw [got] at step
        exact step
      | ok answer after =>
        rw [got] at step
        cases answer with
        | error _ => exact step
        | ok _ => exact step.1.offline step.2
  | opened prior effects got ih =>
    obtain ⟨_, allowed, represented⟩ := ih
    cases represented with
    | offline canOpen =>
      have step := Model.reopen_refines effects _ canOpen
      rw [got] at step
      exact ⟨_, .next allowed (.opened step.2), .online step.1⟩
  | scan prior ih =>
    obtain ⟨_, allowed, represented⟩ := ih
    cases represented with
    | online installed =>
      exact ⟨_, .next allowed .scan, .online installed⟩

/-- Every admitted finite source execution implements the independent
client history and absolute release contract. -/
theorem Run.refines {events running} (run : Run events running) : ∃ abstract, Allows events abstract := by
  obtain ⟨abstract, valid, _⟩ := sound run
  exact ⟨abstract, valid⟩

theorem Run.refinesOnline {events session state} (run : Run events (.online session state)) :
    Allows events (.online session.view) := by
  obtain ⟨_, valid, represented⟩ := sound run
  cases represented
  exact valid

/-- A recovered online session keeps an acknowledged batch at its
original position, or has explicitly released that position. -/
theorem Run.acknowledged_retained {earlier suffix : List Event} {batch : Bytes} {session state}
    (run : Run (earlier ++ [.ack (.append batch)] ++ suffix) (.online session state)) :
    ∃ prior, Allows earlier (.online prior) ∧ session.view.Keeps (prior.tail + 1) batch :=
  Contract.acknowledged_retained earlier suffix batch run.refinesOnline

/-- Reopening an online session cannot roll back an acknowledged release. -/
theorem Run.acknowledged_discard_persists {earlier suffix : List Event} {k session state}
    (run : Run (earlier ++ [.ack (.discardThrough k)] ++ suffix) (.online session state)) :
    k ≤ session.view.base :=
  Contract.acknowledged_discard_persists earlier suffix k run.refinesOnline

/-- Once the primitive callbacks are healthy, every reachable, initialized
offline state can reopen its selected history. -/
theorem Run.healthy_open {events state} (run : Run events (.offline state)) :
    ∃ session after, (reopen (Model.ops Model.healthy)).run state = .ok (.ok session) after := by
  obtain ⟨_, _, represented⟩ := sound run
  cases represented with
  | offline canOpen => exact Model.reopen_healthy _ canOpen

end WalRecoverySlice.Segmented
