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

end ExperimentalL0.Lifecycle
