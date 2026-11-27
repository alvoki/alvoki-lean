import Alvoki.Storage.Disk.Proofs.Read.NativeReadRecoveryTrace

namespace Alvoki.Storage.DiskSession

open Sequential (SnapshotHandle SnapshotPin)

/-- Snapshot operations use the reached phase. Release also carries the
native comparison of the original handle's token with the current session. -/
inductive NativeSnapshotUpdateObservation (state : NativeReadyState) : Type → Type where
  | acquireAt (sequence : UInt64) : NativeSnapshotUpdateObservation state (Option (Nat × SnapshotPin))
  | acquire : NativeSnapshotUpdateObservation state (Nat × SnapshotPin)
  | release (issuer : Nat) (handle : SnapshotHandle) (sameSession : Bool)
      (compared : sameSession = decide (issuer = state.session.sessionRef)) : NativeSnapshotUpdateObservation state Unit
  | advanceFloor (floor : UInt64) : NativeSnapshotUpdateObservation state Bool

namespace NativeSnapshotUpdateObservation

def update : NativeSnapshotUpdateObservation state α → SnapshotUpdate α
  | .acquireAt sequence => .acquireAt sequence
  | .acquire => .acquire
  | .release issuer handle _ _ => .release issuer handle
  | .advanceFloor floor => .advanceFloor floor

def run (observed : NativeSnapshotUpdateObservation state α) : EStateM.Result IO.Error SegmentedSession α :=
  match observed with
  | .release _ handle sameSession _ => state.session.runRelease sameSession handle
  | .acquireAt sequence => state.session.runAcquireAt sequence
  | .acquire => state.session.runAcquire
  | .advanceFloor floor => state.session.runAdvanceFloor floor

theorem run_eq_update (observed : NativeSnapshotUpdateObservation state α) :
    observed.run = observed.update.run state.session := by
  cases observed with
  | release issuer handle sameSession compared => exact (SnapshotUpdate.run_release handle compared).symm
  | acquireAt | acquire | advanceFloor => rfl

end NativeSnapshotUpdateObservation

private theorem SnapshotUpdate.updatedTable (update : SnapshotUpdate α) {session : SegmentedSession}
    {installed next : Installed} (phase : session.phase = .ready installed) {value : α}
    (updated : update.outcome session = .updated value next) :
    ∃ table, next = { installed with table } ∧ SegmentedTableStep installed.table table := by
  cases update with
  | acquireAt sequence =>
    cases acquired : installed.table.acquireAt sequence with
    | none => simp [SnapshotUpdate.outcome, phase, acquired] at updated
    | some result =>
      obtain ⟨pin, table⟩ := result
      simp only [SnapshotUpdate.outcome, phase, acquired, SnapshotUpdate.Outcome.updated.injEq] at updated
      exact ⟨table, updated.2.symm, .acquireAt acquired⟩
  | acquire =>
    cases acquired : installed.table.acquireAt installed.table.committed with
    | none => simp [SnapshotUpdate.outcome, phase, acquired] at updated
    | some result =>
      obtain ⟨pin, table⟩ := result
      simp only [SnapshotUpdate.outcome, phase, acquired, SnapshotUpdate.Outcome.updated.injEq] at updated
      exact ⟨table, updated.2.symm, .acquireAt acquired⟩
  | release issuer handle =>
    by_cases localToken : issuer = session.sessionRef
    · simp only [SnapshotUpdate.outcome, phase, localToken, ite_true, SnapshotUpdate.Outcome.updated.injEq] at updated
      exact ⟨_, updated.2.symm, .release handle true⟩
    · simp [SnapshotUpdate.outcome, phase, localToken] at updated
  | advanceFloor floor =>
    cases advanced : installed.table.advanceFloor floor with
    | none => simp [SnapshotUpdate.outcome, phase, advanced] at updated
    | some table =>
      simp only [SnapshotUpdate.outcome, phase, advanced, SnapshotUpdate.Outcome.updated.injEq] at updated
      exact ⟨table, updated.2.symm, .advanceFloor advanced⟩

/-- The observed outcome records the exact return and the next table.
Only the phase table can change. The existing physical custody and the
earlier response ledger carry into the next position. -/
structure NativeSnapshotUpdateContinuation (before : NativeReadPosition history log)
    (observed : NativeSnapshotUpdateObservation before.state α) (after : NativeReadPosition history log) : Prop where
  returned : observed.run = match observed.update.outcome before.state.session with
    | .unchanged value | .updated value _ => .ok value after.state.session
    | .failed cause => .error cause after.state.session
  reached : match observed.update.outcome before.state.session with
    | .unchanged _ | .failed _ => after.state = before.state
    | .updated _ installed => after.state = before.state.withTable installed.table
  opened : after.opened = before.opened
  initial : after.initial = before.initial
  reads : after.reads = before.reads
  files : after.state.files = before.state.files
  cache : after.state.cache = before.state.cache
  census : after.state.census = before.state.census
  owner : after.state.owner = before.state.owner
  directorySlot : after.state.directorySlot = before.state.directorySlot
  sessionRef : after.state.session.sessionRef = before.state.session.sessionRef
  phaseRef : after.state.session.phaseRef = before.state.session.phaseRef

/-- Every ready-session snapshot-control outcome comes from the shared
native schedule. Foreign releases, rejected floor changes and unsupported
acquisitions keep the reached state. Successful changes retain the
original open anchor and one replay of earlier responses. -/
theorem NativeReadPosition.updatesSnapshot (current : NativeReadPosition history log)
    (observed : NativeSnapshotUpdateObservation current.state α) :
    ∃ after, NativeSnapshotUpdateContinuation current observed after := by
  have ran := observed.update.run_outcome current.state.session
  have actual := observed.run_eq_update.trans ran
  cases outcome : observed.update.outcome current.state.session with
  | unchanged value =>
    exact ⟨current, by rw [outcome] at actual ⊢; exact actual, by simp only [outcome],
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | failed cause =>
    exact ⟨current, by rw [outcome] at actual ⊢; exact actual, by simp only [outcome],
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | updated value installed =>
    obtain ⟨table, rfl, transition⟩ := observed.update.updatedTable current.readPrefix.refines.1.phase outcome
    have returned : observed.update.run current.state.session = .ok value (current.state.withTable table).session := by
      rw [outcome] at ran
      exact ran
    let next : NativeReadPosition history log :=
      { current with
        state := current.state.withTable table
        readPrefix := .snapshotUpdate observed.update current.readPrefix returned transition }
    refine ⟨next, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [outcome]
      exact observed.run_eq_update.trans returned
    · rw [outcome]

end Alvoki.Storage.DiskSession
