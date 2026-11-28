import Alvoki.Experiments.L0.ComponentContract
import Alvoki.Experiments.WAL.Segmented.Proofs.NativeReopen

namespace ExperimentalL0.WalRecovery

open WalRecoverySlice.Segmented WalRecoverySlice.Segmented.Model
open WalRecoverySlice.Segmented.Native (Phase scanWith)

abbrev PublicOpenResult (directory lock : Type) :=
  EStateM.Result Unit (State × Bool) (Except String (Phase (ReopenedStore directory lock) × Unit))

/-- Install the phase returned by public open and scan that phase directly.
Both branches retain the disk reached by the shared WAL open schedule. -/
def reopened (install : State → Phase (ReopenedStore directory lock) → σ) :
    PublicOpenResult directory lock → EStateM.Result String σ Contract.View
  | .ok (.ok (phase, ())) (after, _) =>
    match scanWith (m := Except String) phase with
    | .ok view => .ok view (install after phase)
    | .error error => .error error (install after phase)
  | .ok (.error error) (after, _) => .error error (install after .closed)
  | .error _ (after, _) => .error "segmented WAL open interrupted" (install after .closed)

/-- Connect the L0 callbacks to the two executable WAL schedules. The
incoming image denotes the already selected restart view. The WAL
producer supplies the phase, resource and disk guarantees for public open. -/
structure Interpretation (ops : Components (StorageM σ)) (selected : σ → Selected) where
  directory : Type
  lock : Type
  phase : σ → Phase (ReopenedStore directory lock)
  diskState : σ → State
  install : σ → State → Phase (ReopenedStore directory lock) → σ
  binding : σ → Except String (RootBinding directory lock)
  reports : σ → RootReports
  childReports : σ → Nat → Nat → WalRecoverySlice.SingleFile.OpenReports
  closeError : σ → Option String
  unlockError : σ → Option String
  openSchedule : ∀ s, ops.reopenWal s = reopened (install s)
    ((publicOpenModel (binding s) (reports s) (childReports s) (closeError s) (unlockError s)).run
      (diskState s, false))
  scanSchedule : ∀ s, ops.scan s = match scanWith (m := Except String) (phase s) with
    | .ok view => .ok view s
    | .error error => .error error s
  recoverable : ∀ s, Recoverable (selected s).view none (diskState s).disk
  readyView : ∀ s store session, phase s = .ready store session → session.view = (selected s).view
  installReached : ∀ s after installed,
    Recoverable (selected s).view none after.disk →
    (match installed with
      | .ready _ session => session.view = (selected s).view
      | .closed | .poisoned _ => True) →
    selected (install s after installed) = selected s ∧
      phase (install s after installed) = installed ∧ diskState (install s after installed) = after

variable {σ : Type} {ops : Components (StorageM σ)} {selected : σ → Selected}

def Interpretation.runOpen (i : Interpretation ops selected) (s : σ) :=
  (publicOpenModel (i.binding s) (i.reports s) (i.childReports s)
    (i.closeError s) (i.unlockError s)).run (i.diskState s, false)

private theorem selectedView {known observed : Contract.View}
    (allowed : PermittedView known none observed) : observed = known := by
  simpa [PermittedView] using allowed

theorem Interpretation.scanEffect (i : Interpretation ops selected) (s : σ) :
    match ops.scan s with
    | .ok view after => view = (selected s).view ∧ selected after = selected s
    | .error _ after => selected after = selected s := by
  rw [i.scanSchedule]
  cases held : i.phase s with
  | ready store session =>
    rw [WalRecoverySlice.Segmented.Native.scan_ready store session]
    exact ⟨i.readyView s store session held, rfl⟩
  | poisoned => rfl
  | closed => rfl

/-- Successful open preserves the returned ready child as well as its
view. Failure records the reached recoverable disk in a closed phase.
The detailed release result remains part of the component's producer. -/
theorem Interpretation.reopenReached (i : Interpretation ops selected) (s : σ) :
    match ops.reopenWal s with
    | .ok view after =>
        view = (selected s).view ∧ selected after = selected s ∧
        ∃ store session, i.phase after = .ready store session ∧
          store.activeId = session.control.active ∧
          Installed session (i.diskState after).disk ∧ session.view = view ∧
          i.runOpen s = .ok (.ok (.ready store session, ())) (i.diskState after, true)
    | .error _ after =>
        selected after = selected s ∧ i.phase after = .closed ∧
          Recoverable (selected s).view none (i.diskState after).disk := by
  have produced := publicOpenModel_refines (i.binding s) (i.reports s) (i.childReports s)
    (i.closeError s) (i.unlockError s) (i.diskState s) (i.recoverable s)
  rw [i.openSchedule]
  cases result : (publicOpenModel (i.binding s) (i.reports s) (i.childReports s)
      (i.closeError s) (i.unlockError s)).run (i.diskState s, false) with
  | error token reached =>
    rw [result] at produced
    obtain ⟨frame, phase, disk⟩ := i.installReached s reached.1 .closed produced.2 trivial
    exact ⟨frame, phase, disk.symm ▸ produced.2⟩
  | ok response reached =>
    rw [result] at produced
    cases response with
    | error error =>
      obtain ⟨frame, phase, disk⟩ := i.installReached s reached.1 .closed produced.2.1 trivial
      exact ⟨frame, phase, disk.symm ▸ produced.2.1⟩
    | ok value =>
      obtain ⟨phase, ⟨⟩⟩ := value
      cases phase with
      | poisoned => exact False.elim produced
      | closed => exact False.elim produced
      | ready store session =>
        obtain ⟨state, held⟩ := reached
        obtain ⟨_, rootHeld, active, installed, allowed, scanned⟩ := produced
        have view := selectedView allowed
        obtain ⟨frame, phase, disk⟩ :=
          i.installReached s state (.ready store session) (installed.offline allowed) view
        simp only [reopened, scanned]
        refine ⟨view, frame, store, session, phase, active, disk.symm ▸ installed, rfl, ?_⟩
        rw [Interpretation.runOpen, disk, result, rootHeld]

/-- A later scan of an immediately reopened state consumes the exact phase
installed by that open. This path does not require the general ready-view
invariant used after mutations. -/
theorem Interpretation.scanAfterReopen (i : Interpretation ops selected)
    (opened : ops.reopenWal s = .ok view after) :
    ops.scan after = .ok view after := by
  have reached := i.reopenReached s
  rw [opened] at reached
  obtain ⟨_, _, store, session, ready, _, _, cached, _⟩ := reached
  rw [i.scanSchedule, ready, WalRecoverySlice.Segmented.Native.scan_ready]
  exact congrArg (fun found => EStateM.Result.ok found after) cached

/-- On a returned error, keep the exact disk and the component's release
guarantee for the acquired child, including when cleanup reports an error. -/
theorem Interpretation.reportedFailure (i : Interpretation ops selected)
    (failed : i.runOpen s = .ok (.error error) (after, held)) :
    ops.reopenWal s = .error error (i.install s after .closed) ∧
      held = false ∧ Recoverable (selected s).view none after.disk ∧
      ∀ owned, i.binding s = .ok owned →
        ScopedFailureReleased owned.root (i.reports s) (i.childReports s) (i.closeError s)
          (i.diskState s) after error := by
  have produced := publicOpenModel_refines (i.binding s) (i.reports s) (i.childReports s)
    (i.closeError s) (i.unlockError s) (i.diskState s) (i.recoverable s)
  unfold Interpretation.runOpen at failed
  rw [failed] at produced
  exact ⟨by rw [i.openSchedule, failed]; rfl, produced⟩

theorem Interpretation.reopenHealthy (i : Interpretation ops selected) (s : σ)
    {owned : RootBinding i.directory i.lock}
    (binding : i.binding s = .ok owned)
    (rootOK : HealthyRoot (i.reports s)) (childrenOK : HealthyChildren (i.childReports s))
    (closeOK : i.closeError s = none) (unlockOK : i.unlockError s = none)
    (representable : ∀ c, (i.diskState s).disk.liveControl = some c →
      c.capacity ≤ 255 ∧ c.active ≤ ControlCodec.wordMax ∧ c.discarded ≤ ControlCodec.wordMax) :
    ∃ after, ops.reopenWal s = .ok (selected s).view after ∧
      ops.scan after = .ok (selected s).view after := by
  obtain ⟨session, child, reached, ran⟩ :=
    publicOpenModel_healthy owned (i.reports s) (i.childReports s) (i.diskState s)
      (i.recoverable s) rootOK childrenOK representable
  have opened : ops.reopenWal s = .ok session.view
      (i.install s reached (.ready ⟨owned, session.control.active, child⟩ session)) := by
    rw [i.openSchedule, binding, closeOK, unlockOK, ran]
    rfl
  have produced := i.reopenReached s
  rw [opened] at produced
  have scanned := i.scanAfterReopen opened
  rw [produced.1] at opened scanned
  exact ⟨_, opened, scanned⟩

theorem Interpretation.reopenEffect (i : Interpretation ops selected) (s : σ) :
    match ops.reopenWal s with
    | .ok view after => view = (selected s).view ∧ selected after = selected s
    | .error _ after => selected after = selected s := by
  have reached := i.reopenReached s
  cases ran : ops.reopenWal s with
  | ok result after =>
    rw [ran] at reached
    exact ⟨reached.1, reached.2.1⟩
  | error error after =>
    rw [ran] at reached
    exact reached.1

end ExperimentalL0.WalRecovery
