import Alvoki.Storage.Disk.Proofs.Write.NativeExecutionPendingWrite
import Alvoki.Storage.Disk.ClientCachedClose

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WAL.Boundary

/-- The native close starts at the exact poisoned write return. The
reported unlock operates on the original owner slot in that census. -/
structure NativePendingClose {history : List WAL.Write} {log : List DatabaseSubmissions}
    {before : NativeReadPosition history log} (pending : NativePendingWrite before) where
  report : CachedCloseReports before.state.session.directory before.state.session.descriptor pending.poisoned
  owner : report.slot = before.state.owner

namespace NativePendingClose

variable {history : List WAL.Write} {log : List DatabaseSubmissions} {before : NativeReadPosition history log}
  {pending : NativePendingWrite before}

def reached (close : NativePendingClose pending) : CachedCloseState CheckpointOpenHandle WriteFiles :=
  match close.report.result with
  | .ok () => close.report.finished
  | .error _ => pending.poisoned

def session (close : NativePendingClose pending) : SegmentedSession :=
  { pending.session with phase := close.reached.phase }

/-- Preserve the same failed-write file image, including its open crash
choices. Successful close changes the owner projection. -/
def files (close : NativePendingClose pending) : LockedFileState FileImage :=
  ⟨pending.files.image, close.reached.files.owners⟩

theorem binding (close : NativePendingClose pending) :
    close.report.bindings (before.state.session.directory.file .lock) =
      pending.observed.bindings (before.state.session.directory.file .lock) := by
  have observed := close.report.lockObject
  rw [close.owner] at observed
  exact observed.trans pending.observed.lockBound.symm

/-- A returned close error leaves the poisoned session and all physical
projections available. A successful close drops the cache references in
schedule order and releases the owner while preserving the file image. -/
theorem returns (close : NativePendingClose pending) :
    match close.report.result with
    | .error cause =>
      close.report.run = .error cause close.reached ∧ close.reached = pending.poisoned ∧
      close.session = pending.session ∧ close.files = pending.files ∧
      close.files.owners.Owns before.state.session.directory before.state.session.descriptor ∧
      ¬ TryLockObserves close.files.owners before.state.session.directory (.ok true)
    | .ok () =>
      close.report.run = .ok () close.reached ∧ close.reached.phase = .closed ∧
      close.reached.files = ⟨(⟨none, none, []⟩, pending.write.failure.failed), pending.write.failure.released.owners⟩ ∧
      close.reached.descriptors = pending.poisoned.descriptors.afterDrops
        (close.report.drops .active ++ close.report.drops .pending ++ close.report.drops .directory) ∧
      close.files = pending.write.failure.released ∧
      TryLockObserves close.files.owners before.state.session.directory (.ok true) := by
  have held : pending.poisoned.files.owners.Owns before.state.session.directory before.state.session.descriptor :=
    pending.holds
  have observed := close.report.reaches (by simp [NativePendingWrite.poisoned, ObservedBatchFailure.closeState]) held
  cases returned : close.report.result with
  | error cause =>
    simp only [CachedCloseReports.Reached, returned] at observed
    have same : close.reached = pending.poisoned := by simp only [reached, returned]
    have sameFiles : close.files = pending.files := by rw [files, same]; rfl
    exact ⟨same.symm ▸ observed.1, same, by rw [session, same]; rfl, sameFiles,
      sameFiles.symm ▸ pending.holds, sameFiles.symm ▸ pending.custody.1⟩
  | ok value =>
    cases value
    simp only [CachedCloseReports.Reached, returned] at observed
    obtain ⟨ran, phase, cleared, inventory, vacant⟩ := observed
    have exactFiles : close.report.finished.files =
        ⟨(⟨none, none, []⟩, pending.write.failure.failed), pending.write.failure.released.owners⟩ := cleared
    have same : close.reached = close.report.finished := by simp only [reached, returned]
    have files : close.files = pending.write.failure.released := by
      simp only [NativePendingClose.files, same, exactFiles]
      rfl
    exact ⟨same.symm ▸ ran, same.symm ▸ phase, same.symm ▸ exactFiles, same.symm ▸ inventory, files,
      by simpa only [NativePendingClose.files, same] using vacant⟩

/-- The retained session references are unavailable after either close
outcome. Its actual phase distinguishes the two diagnostics. -/
theorem rejectsReads (close : NativePendingClose pending) (sequence : UInt64) (sameSession : Bool)
    (read : PackedTable → Option α) :
    let cause := match close.report.result with
      | .ok () => IO.userError "database is closed"
      | .error _ => IO.userError "publication failed; reopen the database"
    close.session.sessionRef = before.state.session.sessionRef ∧
    close.session.phaseRef = before.state.session.phaseRef ∧
    close.session.runAcquireAt sequence = .error cause close.session ∧
    close.session.runSnapshotRead sameSession read = .error cause close.session := by
  have observed := close.returns
  cases returned : close.report.result with
  | error cause =>
    rw [returned] at observed
    rw [observed.2.2.1]
    exact pending.rejectsReads sequence sameSession read
  | ok value =>
    cases value
    rw [returned] at observed
    have phase : close.session.phase = .closed := observed.2.1
    refine ⟨rfl, rfl, ?_, SegmentedSession.runSnapshotRead_closed phase sameSession read⟩
    rw [SegmentedSession.runAcquireAt, phase]
    rfl

/-- Closing does not change the pending submission or the exact marker
choice. Earlier reads remain bounded in its selected replay. -/
theorem selectsAtReturn (close : NativePendingClose pending) :
    ∃ chosen,
      (chosen = history ∨ chosen = history ++ pending.write.failure.batch) ∧
      close.files.image.directory.active.walBoundary = some (WAL.Boundary.encode (WAL.encode chosen).size.toUInt64) ∧
      PendingClientReplay pending.submissions before.reads chosen ∧
      ∀ read ∈ before.reads, read.BoundedBy chosen.length :=
  pending.selectsAtReturn

end NativePendingClose

end Alvoki.Storage.DiskSession
