import Alvoki.Storage.Disk.ClientReadTrace
import Alvoki.Storage.Disk.SessionRetentionFloor

namespace Alvoki.Storage.DiskSession

open Sequential (SnapshotHandle SnapshotPin)

variable {session next : SegmentedSession} {installed : Installed} {before : SegmentedWriterState}

/-- Client operations that can update the in-memory snapshot registry or
retention floor. A release carries the issuing session's token and local pin. -/
inductive SnapshotUpdate : Type → Type where
  | acquireAt (snapshot : UInt64) : SnapshotUpdate (Option (Nat × SnapshotPin))
  | acquire : SnapshotUpdate (Nat × SnapshotPin)
  | release (issuer : Nat) (handle : SnapshotHandle) : SnapshotUpdate Unit
  | advanceFloor (floor : UInt64) : SnapshotUpdate Bool

def SnapshotUpdate.run : SnapshotUpdate α → EStateM IO.Error SegmentedSession α
  | .acquireAt snapshot => SegmentedSession.runAcquireAt snapshot
  | .acquire => SegmentedSession.runAcquire
  | .release issuer handle => fun session =>
    session.runRelease (decide (issuer = session.sessionRef)) handle
  | .advanceFloor floor => SegmentedSession.runAdvanceFloor floor

private theorem runAcquireAt_result (phase : session.phase = .ready installed) (snapshot : UInt64) :
    session.runAcquireAt snapshot =
      match installed.table.acquireAt snapshot with
      | none => .ok none session
      | some (pin, table) => .ok (some (session.sessionRef, pin)) { session with phase := .ready { installed with table } } := by
  cases acquired : installed.table.acquireAt snapshot with
  | none => simp [SegmentedSession.runAcquireAt, acquireSnapshotWith, phase, Phase.installed,
      Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, acquired]
  | some found =>
    obtain ⟨pin, table⟩ := found
    exact SegmentedSession.runAcquireAt_ready phase acquired

private theorem runAcquire_result (phase : session.phase = .ready installed) :
    session.runAcquire =
      match installed.table.acquireAt installed.table.committed with
      | none => .error (IO.userError "cannot acquire the latest snapshot") session
      | some (pin, table) => .ok (session.sessionRef, pin) { session with phase := .ready { installed with table } } := by
  cases acquired : installed.table.acquireAt installed.table.committed with
  | none =>
    have explicit := runAcquireAt_result phase installed.table.committed
    rw [acquired] at explicit
    simp only [SegmentedSession.runAcquire, acquireLatestWith, phase, Phase.installed, explicit,
      Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
    rfl
  | some found =>
    obtain ⟨pin, table⟩ := found
    exact SegmentedSession.runAcquire_of_acquireAt phase (SegmentedSession.runAcquireAt_ready phase acquired)

/-- Use the actual pointer comparison that the release schedule reached. -/
theorem SnapshotUpdate.run_release (handle : SnapshotHandle)
    (compared : sameSession = decide (issuer = session.sessionRef)) :
    (SnapshotUpdate.release issuer handle).run session = session.runRelease sameSession handle := by
  rw [compared]
  rfl

/-- On an available session, the actual schedule's successful outcome
supplies the exact next ready cell. The same table step supplies the next
mixed writer with no new WAL submissions. -/
theorem SnapshotUpdate.readyTransition (update : SnapshotUpdate α)
    (phase : session.phase = .ready before.installed) (returned : update.run session = .ok result next) :
    ∃ after, next = { session with phase := .ready after.installed } ∧
      SegmentedBatchDatabaseTrace session.directory session.descriptor before allowCollection [] session.descriptor after := by
  have unchanged (same : next = session) :
      ∃ after, next = { session with phase := .ready after.installed } ∧
        SegmentedBatchDatabaseTrace session.directory session.descriptor before allowCollection [] session.descriptor after := by
    refine ⟨before, ?_, .start⟩
    cases session
    simp_all
  cases update with
  | acquireAt snapshot =>
    rw [SnapshotUpdate.run, runAcquireAt_result phase snapshot] at returned
    cases acquired : before.installed.table.acquireAt snapshot with
    | none => exact unchanged (EStateM.Result.ok.inj (by simpa only [acquired] using returned)).2.symm
    | some found =>
      obtain ⟨pin, table⟩ := found
      rw [acquired] at returned
      exact ⟨before.withTable table, (EStateM.Result.ok.inj returned).2.symm, .table .start (.acquireAt acquired)⟩
  | acquire =>
    rw [SnapshotUpdate.run, runAcquire_result phase] at returned
    cases acquired : before.installed.table.acquireAt before.installed.table.committed with
    | none => simp [acquired] at returned
    | some found =>
      obtain ⟨pin, table⟩ := found
      rw [acquired] at returned
      exact ⟨before.withTable table, (EStateM.Result.ok.inj returned).2.symm, .table .start (.acquireAt acquired)⟩
  | release issuer handle =>
    change session.runRelease (decide (issuer = session.sessionRef)) handle = .ok result next at returned
    rw [SegmentedSession.runRelease_ready phase handle (issuer := issuer) rfl] at returned
    by_cases localToken : issuer = session.sessionRef
    · rw [ite_eq_left localToken] at returned
      exact ⟨before.withTable (before.installed.table.release handle), (EStateM.Result.ok.inj returned).2.symm,
        .table .start (.release handle true)⟩
    · rw [ite_eq_right localToken] at returned
      exact unchanged (EStateM.Result.ok.inj returned).2.symm
  | advanceFloor floor =>
    rw [SnapshotUpdate.run, SegmentedSession.runAdvanceFloor_ready phase] at returned
    cases advanced : before.installed.table.advanceFloor floor with
    | none => exact unchanged (EStateM.Result.ok.inj (by simpa only [advanced] using returned)).2.symm
    | some table =>
      rw [advanced] at returned
      exact ⟨before.withTable table, (EStateM.Result.ok.inj returned).2.symm, .table .start (.advanceFloor advanced)⟩

private theorem SnapshotUpdate.phaseError (update : SnapshotUpdate α)
    (rejected : session.phase.installed (m := EStateM IO.Error SegmentedSession) session =
      .error error session) : update.run session = .error error session := by
  cases update <;>
    simp only [SnapshotUpdate.run, SegmentedSession.runAcquireAt, SegmentedSession.runAcquire,
      SegmentedSession.runRelease, SegmentedSession.runAdvanceFloor, acquireSnapshotWith, acquireLatestWith,
      releaseSnapshotWith, withLocalHandle, advanceFloorWith, Bind.bind, EStateM.bind, rejected]

theorem SnapshotUpdate.closed (update : SnapshotUpdate α) (phase : session.phase = .closed) :
    update.run session = .error (IO.userError "database is closed") session := by
  apply update.phaseError
  rw [phase]
  rfl

theorem SnapshotUpdate.poisoned (update : SnapshotUpdate α) (phase : session.phase = .poisoned) :
    update.run session = .error (IO.userError "publication failed; reopen the database") session := by
  apply update.phaseError
  rw [phase]
  rfl

/-- Extend the chronological trace while keeping the actual returned
session and the existing submissions and recorded reads. -/
theorem SegmentedClientReadTrace.observeSnapshotUpdate
    (trace : SegmentedClientReadTrace session.directory initialDescriptor initial allowCollection log reads
      session.descriptor before)
    (update : SnapshotUpdate α) (phase : session.phase = .ready before.installed)
    (returned : update.run session = .ok result next) :
    ∃ after, next = { session with phase := .ready after.installed } ∧
      SegmentedClientReadTrace session.directory initialDescriptor initial allowCollection log reads session.descriptor after := by
  obtain ⟨after, exactNext, step⟩ := update.readyTransition (allowCollection := allowCollection) phase returned
  exact ⟨after, exactNext, by simpa only [List.append_nil] using trace.advance step⟩

end Alvoki.Storage.DiskSession
