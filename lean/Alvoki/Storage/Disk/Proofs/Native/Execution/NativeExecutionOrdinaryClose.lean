import Alvoki.Storage.Disk.Proofs.Read.NativeReadRecoveryTrace
import Alvoki.Storage.Disk.Proofs.Native.Execution.NativeReadyClose

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

namespace NativeReadyClose

variable {state : NativeReadyState}

/-- Project the actual ordinary close result at the point it returns.
No later slot drop or open contributes to this state. -/
def reached (close : NativeReadyClose state) : CachedCloseState CheckpointOpenHandle FileImage :=
  match close.report.result with
  | .ok () => close.report.finished
  | .error _ => state.closeState

def session (close : NativeReadyClose state) : SegmentedSession :=
  { state.session with phase := close.reached.phase }

def files (close : NativeReadyClose state) : LockedFileState FileImage :=
  ⟨close.reached.files.image.2, close.reached.files.owners⟩

/-- Failed unlock returns the original ready session and still holds
the lock. Success preserves the selected bytes, clears the cache in
schedule order and makes the lock vacant. -/
def Returned (close : NativeReadyClose state) : Prop :=
  match close.report.result with
  | .error cause =>
    close.report.run = .error cause close.reached ∧ close.reached = state.closeState ∧
    close.session = state.session ∧ close.files = state.files ∧
    close.files.owners.Owns state.session.directory state.session.descriptor ∧
    ¬ TryLockObserves close.files.owners state.session.directory (.ok true)
  | .ok () =>
    close.report.run = .ok () close.reached ∧ close.session.phase = .closed ∧
    close.reached.files = ⟨(⟨none, none, []⟩, state.files.image), state.releasedFiles.owners⟩ ∧
    close.reached.descriptors = state.census.afterDrops
      (close.report.drops .active ++ close.report.drops .pending ++ close.report.drops .directory) ∧
    close.files = state.releasedFiles ∧
    TryLockObserves close.files.owners state.session.directory (.ok true)

theorem returns (close : NativeReadyClose state) (valid : state.Valid) : close.Returned := by
  cases reported : close.report.result with
  | error cause =>
    simp only [Returned, reported]
    have same : close.reached = state.closeState := by simp only [reached, reported]
    have sameFiles : close.files = state.files := by rw [files, same]; rfl
    have held := valid.retained.held
    refine ⟨same.symm ▸ close.failed valid reported, same, by rw [session, same]; rfl,
      sameFiles, sameFiles.symm ▸ held, ?_⟩
    intro vacant
    change state.files.owners (state.session.directory.file .lock) = some state.session.descriptor at held
    rw [sameFiles] at vacant
    rw [vacant rfl] at held
    contradiction
  | ok value =>
    cases value
    simp only [Returned, reported]
    obtain ⟨ran, phase, cleared, inventory, vacant⟩ := close.closes valid reported
    have same : close.reached = close.report.finished := by simp only [reached, reported]
    have sameFiles : close.files = state.releasedFiles := by rw [files, same, cleared]; rfl
    exact ⟨same.symm ▸ ran, by simpa only [session, same] using phase, same.symm ▸ cleared,
      same.symm ▸ inventory, sameFiles, sameFiles.symm ▸ vacant⟩

/-- After successful ordinary close, the original session references
encounter the closed phase before acquisition or the handle comparison. -/
theorem rejectsReads (close : NativeReadyClose state) (valid : state.Valid)
    (success : close.report.result = .ok ()) (sequence : UInt64) (sameSession : Bool)
    (read : PackedTable → Option α) :
    close.session.sessionRef = state.session.sessionRef ∧ close.session.phaseRef = state.session.phaseRef ∧
    close.session.runAcquireAt sequence = .error (IO.userError "database is closed") close.session ∧
    close.session.runSnapshotRead sameSession read = .error (IO.userError "database is closed") close.session := by
  have observed := close.returns valid
  simp only [Returned, success] at observed
  have phase := observed.2.1
  refine ⟨rfl, rfl, ?_, SegmentedSession.runSnapshotRead_closed phase sameSession read⟩
  rw [SegmentedSession.runAcquireAt, phase]
  rfl

end NativeReadyClose

/-- The ordinary close returns on the session reached by the native
read prefix. Preserve the earlier submissions and verified responses
even when the execution ends immediately at this return. -/
structure NativeOrdinaryCloseReturn
    (current : NativeReadPosition history log) (close : NativeReadyClose current.state) : Prop where
  returned : close.Returned
  opened : current.opened = .ok current.initial.session (current.initial.census, current.initial.files)
  owner : close.report.slot = current.initial.owner
  stableImage : close.files.image = current.state.files.image
  replay : PendingClientReplay log current.reads history
  readsBounded : ∀ read ∈ current.reads, read.BoundedBy history.length
  readyOnError : (∀ cause, close.report.result = .error cause →
    InstalledClientReplay log current.reads history current.state.writer.installed close.session)

theorem NativeReadPosition.closes (current : NativeReadPosition history log)
    (close : NativeReadyClose current.state) : NativeOrdinaryCloseReturn current close := by
  have result := close.returns current.readPrefix.refines.1
  obtain ⟨opened, _, _, owner, _, replay⟩ := current.readPrefix.reachesClose close
  refine ⟨result, opened, owner, ?_, replay, current.readPrefix.readsBounded, ?_⟩
  · cases reported : close.report.result with
    | error cause =>
      simp only [NativeReadyClose.Returned, reported] at result
      exact congrArg LockedFileState.image result.2.2.2.1
    | ok value =>
      cases value
      simp only [NativeReadyClose.Returned, reported] at result
      have image := congrArg LockedFileState.image result.2.2.2.2.1
      exact image
  · intro cause reported
    simp only [NativeReadyClose.Returned, reported] at result
    exact result.2.2.1.symm ▸ current.readPrefix.guardedReplay

end Alvoki.Storage.DiskSession
