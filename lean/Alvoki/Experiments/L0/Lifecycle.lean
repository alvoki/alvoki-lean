import Alvoki.Experiments.L0.Basic

namespace ExperimentalL0.Lifecycle

/-- The wrapper holds one phase cell. An exposed session owns the WAL
in the same cell, and intermediate phases keep it private for cleanup. -/
inductive Phase (W : Type) where
  | offline
  | opening
  | recovering (handle : W)
  | updating (handle : W)
  | online (handle : W) (session : Session)

variable {W : Type}

def Phase.wal : Phase W → Option W
  | .recovering handle | .updating handle | .online handle _ => some handle
  | .offline | .opening => none

def Phase.session : Phase W → Option Session
  | .online _ session => some session
  | _ => none

/-- Reserve the only phase in which the recovery callback can open a WAL.
The returned constructor records the new handle before the callback scans it. -/
def Phase.attachWal : Phase W → Option (W → Phase W)
  | .opening => some .recovering
  | _ => none

/-- Hide the previous session for the entire duration of a mutation. -/
def Phase.beginUpdate : Phase W → Option (Phase W × Session)
  | .online handle session => some (.updating handle, session)
  | _ => none

/-- Publish only after recovery or the mutating operation completed. -/
def Phase.publish (phase : Phase W) (session : Session) : Option (Phase W) :=
  match phase with
  | .recovering handle | .updating handle => some (.online handle session)
  | _ => none

/-- Publish into the same handle custody. In particular a closed handle
cannot be brought online by either an operation or a recovery continuation. -/
theorem Phase.publish_owns_wal {before after : Phase W} {session : Session}
    (step : before.publish session = some after) :
    after.session = some session ∧ after.wal = before.wal ∧ before.session = none := by
  cases before <;> simp [publish] at step <;> subst after <;> exact ⟨rfl, rfl, rfl⟩

theorem Phase.beginUpdate_hides_session {before after : Phase W} {session : Session}
    (step : before.beginUpdate = some (after, session)) :
    before.session = some session ∧ after.session = none ∧ after.wal = before.wal := by
  cases before <;> simp [beginUpdate] at step
  obtain ⟨rfl, rfl⟩ := step
  exact ⟨rfl, rfl, rfl⟩

theorem Phase.attachWal_keeps_session_private {before : Phase W} {attach : W → Phase W}
    (step : before.attachWal = some attach) (handle : W) :
    before.wal = none ∧ (attach handle).wal = some handle ∧
      (attach handle).session = none := by
  cases before <;> simp [attachWal] at step
  subst attach
  exact ⟨rfl, rfl, rfl⟩

theorem Phase.online_owns_wal {phase : Phase W} {session : Session}
    (online : phase.session = some session) : ∃ handle, phase.wal = some handle := by
  cases phase <;> simp_all [Phase.session, Phase.wal]

/-- This is the value installed by cleanup before any fallible close callback. -/
theorem Phase.offline_closed (session : Session) :
    (Phase.offline : Phase W).wal = none ∧ (Phase.offline : Phase W).session = none ∧
      (Phase.offline : Phase W).attachWal = none ∧
      (Phase.offline : Phase W).beginUpdate = none ∧
      (Phase.offline : Phase W).publish session = none :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩


/-- The executable wrapper interprets the phase cell with an IO.Ref. -/
structure Cell (m : Type → Type) (W : Type) where
  read : m (Phase W)
  swap : Phase W → m (Phase W)

/-- Keep custody of the returned handle before scanning. A failed scan
therefore leaves the attached handle available to the scope cleanup. -/
def Cell.reopenWal [Monad m] [MonadExceptOf ε m] (cell : Cell m W)
    (invalid : ε) (openWal : m W) (scan : W → m α) : m α := do
  let some attach := (← cell.read).attachWal | throw invalid
  let handle ← openWal
  let _ ← cell.swap (attach handle)
  scan handle

def Cell.publish [Monad m] [MonadExceptOf ε m] (cell : Cell m W)
    (invalid : ε) (session : Session) : m Unit := do
  let some next := (← cell.read).publish session | throw invalid
  let _ ← cell.swap next

def Cell.close [Monad m] (cell : Cell m W) (closeWal : W → m Unit) : m Unit := do
  let previous ← cell.swap .offline
  if let some handle := previous.wal then closeWal handle

private def attempt [Monad m] [MonadExceptOf ε m] (action : m α) : m (Except ε α) :=
  MonadExceptOf.tryCatch (ε := ε) (action >>= fun value => pure (.ok value))
    (fun error => pure (.error error))

/-- Execute cleanup on either outcome and preserve the primary error. -/
def finish [Monad m] [MonadExceptOf ε m] (action : m α) (cleanup : m Unit) : m α := do
  let result ← attempt (ε := ε) action
  let cleaned ← attempt (ε := ε) cleanup
  match result, cleaned with
  | .error error, _ | .ok _, .error error => throw error
  | .ok value, .ok () => pure value

/-- Kernel-checked by the interpretation below. The native wrapper runs
this schedule inside the already-acquired root-lock scope. -/
def Cell.withSession [Monad m] [MonadExceptOf ε m] (cell : Cell m W) (invalid : ε)
    (recover : m Session) (use : m α) (closeWal : W → m Unit) (unlock : m Unit) : m α :=
  finish (ε := ε) (do
    let session ← recover
    cell.publish invalid session
    use) (finish (ε := ε) (cell.close closeWal) unlock)

/-- Reads need an online session and do not hide or republish it. -/
def Cell.useSession [Monad m] [MonadExceptOf ε m] (cell : Cell m W) (invalid : ε)
    (use : Session → m α) : m α := do
  let some session := (← cell.read).session | throw invalid
  use session

def Cell.update [Monad m] [MonadExceptOf ε m] (cell : Cell m W) (invalid : ε)
    (operation : Session → m Session) (closeWal : W → m Unit) : m Unit := do
  let some (next, session) := (← cell.read).beginUpdate | throw invalid
  let _ ← cell.swap next
  let result ← attempt (ε := ε) (do cell.publish invalid (← operation session))
  match result with
  | .ok () => pure ()
  | .error error =>
    let _ ← attempt (ε := ε) (cell.close closeWal)
    throw error

namespace Proof

variable {S : Type}

def stateCell : Cell (EStateM ε (Phase W × S)) W where
  read := fun state => .ok state.1 state
  swap := fun next before => .ok before.1 (next, before.2)

/-- The phase at a success or failure boundary of the executable schedule. -/
def reached : EStateM.Result ε (Phase W × S) α → Phase W × S
  | .ok _ phase | .error _ phase => phase

private theorem attempt_state (action : EStateM ε (Phase W × S) α) (phase : Phase W × S) :
    attempt action phase = match action phase with
      | .ok value after => .ok (.ok value) after
      | .error error after => .ok (.error error) after := by
  cases h : action phase <;>
    simp [attempt, h, MonadExceptOf.tryCatch, EStateM.tryCatch, Bind.bind, EStateM.bind,
      Pure.pure, EStateM.pure] <;> rfl

private theorem finish_state (action : EStateM ε (Phase W × S) α) (cleanup) (phase : Phase W × S) :
    finish (ε := ε) action cleanup phase =
      match action phase with
      | .ok value after => match cleanup after with
        | .ok _ closed => .ok value closed
        | .error error closed => .error error closed
      | .error error after => .error error (reached (cleanup after)) := by
  cases h : action phase with
  | ok value after =>
    cases done : cleanup after <;>
      simp [finish, Bind.bind, EStateM.bind, attempt_state, h, done, Pure.pure, EStateM.pure] <;> rfl
  | error error after =>
    cases done : cleanup after <;>
      simp [finish, Bind.bind, EStateM.bind, attempt_state, h, done, reached] <;> rfl

theorem reopen_attaches_before_scan (openWal : EStateM ε (Phase W × S) W)
    (scan : W → EStateM ε (Phase W × S) α) (invalid : ε) (handle : W)
    (before : S) (after : Phase W × S)
    (opened : openWal (.opening, before) = .ok handle after) :
    Cell.reopenWal stateCell invalid openWal scan (.opening, before) =
      scan handle (.recovering handle, after.2) := by
  simp [Cell.reopenWal, stateCell, Phase.attachWal, Bind.bind, EStateM.bind, opened]

theorem reopen_open_failure (openWal : EStateM ε (Phase W × S) W)
    (scan : W → EStateM ε (Phase W × S) α) (invalid error : ε) (before : S)
    (after : Phase W × S)
    (failed : openWal (.opening, before) = .error error after) :
    Cell.reopenWal stateCell invalid openWal scan (.opening, before) = .error error after := by
  simp [Cell.reopenWal, stateCell, Phase.attachWal, Bind.bind, EStateM.bind, failed]

private theorem close_state (closeWal : W → EStateM ε (Phase W × S) Unit)
    (before : Phase W × S) :
    Cell.close stateCell closeWal before =
      match before.1.wal with
      | some handle => closeWal handle (.offline, before.2)
      | none => .ok () (.offline, before.2) := by
  rcases before with ⟨phase, storage⟩
  cases phase <;> rfl

private theorem cleanup_closes (closeWal : W → EStateM ε (Phase W × S) Unit) (unlock)
    (closeFrame : ∀ handle storage, reached (closeWal handle (.offline, storage)) = (.offline, storage))
    (unlockFrame : ∀ storage, reached (unlock (.offline, storage)) = (.offline, storage))
    (before : Phase W × S) :
    reached (finish (ε := ε) (Cell.close stateCell closeWal) unlock before) =
      (.offline, before.2) := by
  have closed : reached (Cell.close stateCell closeWal before) = (.offline, before.2) := by
    rw [close_state]
    cases before.1.wal with
    | none => rfl
    | some handle => exact closeFrame handle before.2
  rw [finish_state]
  cases h : Cell.close stateCell closeWal before with
  | ok _ after =>
    rw [h] at closed
    cases closed
    cases ran : unlock (.offline, before.2) <;>
      simpa [ran, reached] using unlockFrame before.2
  | error error after =>
    rw [h] at closed
    cases closed
    exact unlockFrame before.2

/-- Both a normal callback and a failing recovery leave the phase cell
offline. Close and unlock can fail and leave the reached storage unchanged. -/
theorem withSession_closes
    (recover : EStateM ε (Phase W × S) Session) (use : EStateM ε (Phase W × S) α)
    (invalid : ε) (closeWal : W → EStateM ε (Phase W × S) Unit) (unlock)
    (closeFrame : ∀ handle storage, reached (closeWal handle (.offline, storage)) = (.offline, storage))
    (unlockFrame : ∀ storage, reached (unlock (.offline, storage)) = (.offline, storage))
    (before : Phase W × S) :
    (reached (Cell.withSession stateCell invalid recover use closeWal unlock before)).1 =
      .offline := by
  unfold Cell.withSession
  rw [finish_state]
  split
  · rename_i after _
    have closed := congrArg Prod.fst (cleanup_closes closeWal unlock closeFrame unlockFrame after)
    cases ran : finish (ε := ε) (Cell.close stateCell closeWal) unlock after <;>
      simpa [ran, reached] using closed
  · exact congrArg Prod.fst (cleanup_closes closeWal unlock closeFrame unlockFrame _)

/-- A failed recovery never enters the callback and preserves its error and
reached storage even when either cleanup callback also fails. -/
theorem failed_recovery_closes (recover : EStateM ε (Phase W × S) Session)
    (use : EStateM ε (Phase W × S) α) (invalid error : ε)
    (closeWal : W → EStateM ε (Phase W × S) Unit) (unlock) (before : S)
    (after : Phase W × S)
    (failed : recover (.opening, before) = .error error after)
    (closeFrame : ∀ handle storage, reached (closeWal handle (.offline, storage)) = (.offline, storage))
    (unlockFrame : ∀ storage, reached (unlock (.offline, storage)) = (.offline, storage)) :
    Cell.withSession stateCell invalid recover use closeWal unlock (.opening, before) =
      .error error (.offline, after.2) := by
  unfold Cell.withSession
  rw [finish_state]
  simp [Bind.bind, EStateM.bind, failed, cleanup_closes closeWal unlock closeFrame unlockFrame]

/-- First expose the recovered session with the WAL held by recovery,
then run the client callback starting from the reached storage. -/
theorem successful_recovery_publishes (recover : EStateM ε (Phase W × S) Session)
    (use : EStateM ε (Phase W × S) α) (invalid : ε) (closeWal : W → EStateM ε (Phase W × S) Unit)
    (unlock) (wal : W) (session : Session) (before after : S)
    (ran : recover (.opening, before) = .ok session (.recovering wal, after)) :
    Cell.withSession stateCell invalid recover use closeWal unlock (.opening, before) =
      finish (ε := ε) use (finish (ε := ε) (Cell.close stateCell closeWal) unlock)
        (.online wal session, after) := by
  unfold Cell.withSession
  rw [finish_state, finish_state]
  simp [Bind.bind, EStateM.bind, ran, Cell.publish, stateCell, Phase.publish, Pure.pure, EStateM.pure]

theorem useSession_online (use : Session → EStateM ε (Phase W × S) α) (invalid : ε)
    (wal : W) (session : Session) (storage : S) :
    Cell.useSession stateCell invalid use (.online wal session, storage) =
      use session (.online wal session, storage) := rfl

theorem useSession_offline (use : Session → EStateM ε (Phase W × S) α) (invalid : ε)
    (storage : S) :
    Cell.useSession stateCell invalid use (.offline, storage) =
      .error invalid (.offline, storage) := rfl

theorem update_success (operation : Session → EStateM ε (Phase W × S) Session) (invalid : ε)
    (closeWal : W → EStateM ε (Phase W × S) Unit) (wal : W) (old next : Session)
    (before after : S)
    (ran : operation old (.updating wal, before) = .ok next (.updating wal, after)) :
    Cell.update stateCell invalid operation closeWal (.online wal old, before) =
      .ok () (.online wal next, after) := by
  simp [Cell.update, stateCell, Phase.beginUpdate, Bind.bind, EStateM.bind, attempt_state,
    ran, Cell.publish, Phase.publish, Pure.pure, EStateM.pure]

private theorem read_state (state : Phase W × S) :
    (stateCell (ε := ε)).read state = .ok state.1 state := rfl

private theorem swap_state (state : Phase W × S) (next : Phase W) :
    (stateCell (ε := ε)).swap next state = .ok state.1 (next, state.2) := rfl

theorem update_error (operation : Session → EStateM ε (Phase W × S) Session) (invalid error : ε)
    (closeWal : W → EStateM ε (Phase W × S) Unit) (wal : W) (old : Session) (before : S)
    (after : Phase W × S)
    (ran : operation old (.updating wal, before) = .error error after)
    (closeFrame : ∀ handle storage, reached (closeWal handle (.offline, storage)) = (.offline, storage)) :
    Cell.update stateCell invalid operation closeWal (.online wal old, before) =
      .error error (.offline, after.2) := by
  simp only [Cell.update, read_state, swap_state, Phase.beginUpdate, Bind.bind, EStateM.bind,
    attempt_state, ran, close_state]
  cases h : after.1.wal with
  | none => rfl
  | some handle =>
    have closed := closeFrame handle after.2
    cases ranClose : closeWal handle (.offline, after.2) <;>
      simp [ranClose, reached] at closed ⊢ <;> subst_vars <;> rfl

end Proof
end ExperimentalL0.Lifecycle
