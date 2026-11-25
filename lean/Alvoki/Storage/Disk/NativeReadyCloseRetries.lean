import Alvoki.Storage.Disk.NativeExecutionClose
import Alvoki.Storage.Disk.NativeExecutionOrdinaryClose

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- The actual returned unlock error at the current ready session.
Its native close report is tied to the same original owner slot. -/
structure NativeReadyCloseError (state : NativeReadyState) where
  close : NativeReadyClose state
  cause : IO.Error
  failed : close.report.result = .error cause

namespace NativeReadyCloseError

variable {state : NativeReadyState}

theorem trace (attempts : List (NativeReadyCloseError state)) (valid : state.Valid) :
    CachedCloseFailureTrace state.session.directory state.session.descriptor state.closeState
      (attempts.map (·.cause)) state.closeState := by
  induction attempts with
  | nil => exact .nil
  | cons attempt _ prior => exact .cons attempt.close.report (attempt.close.failed valid attempt.failed) prior

/-- A failed close preserves the returned session, the reached cache and
census, and the replay of previous and still-supported guarded reads. -/
theorem returns (current : NativeReadPosition history log) (attempt : NativeReadyCloseError current.state) :
    attempt.close.report.run = .error attempt.cause current.state.closeState ∧
    attempt.close.reached = current.state.closeState ∧ attempt.close.session = current.state.session ∧
    attempt.close.files = current.state.files ∧
    ¬ TryLockObserves attempt.close.files.owners current.state.session.directory (.ok true) ∧
    InstalledClientReplay log current.reads history current.state.writer.installed attempt.close.session := by
  have reached := current.closes attempt.close
  have returned := reached.returned
  simp only [NativeReadyClose.Returned, attempt.failed] at returned
  obtain ⟨actual, unchanged, session, files, _, held⟩ := returned
  exact ⟨by simpa only [unchanged] using actual, unchanged, session, files, held, reached.readyOnError _ attempt.failed⟩

end NativeReadyCloseError

/-- Each failed close starts from the state actually left by its
predecessor. The final close or its subsequent last reference drop
supplies the inventory for the reported healthy aligned open. -/
structure NativeReadyCloseRetryObservation (state : NativeReadyState) (input : FilePath) where
  attempts : List (NativeReadyCloseError state)
  final : NativeCloseReopenObservation state input

structure NativeReadyCloseRetryContinuation (current : NativeReadPosition history log) {input : FilePath}
    (observed : NativeReadyCloseRetryObservation current.state input)
    (next : NativeReadPosition history log) : Prop where
  failed : CachedCloseFailureTrace current.state.session.directory current.state.session.descriptor
    current.state.closeState (observed.attempts.map (·.cause)) current.state.closeState
  returned : ∀ attempt ∈ observed.attempts,
    attempt.close.report.run = .error attempt.cause current.state.closeState ∧
    attempt.close.files = current.state.files ∧ attempt.close.session = current.state.session ∧
    InstalledClientReplay log current.reads history current.state.writer.installed attempt.close.session
  reopened : NativeCloseReopenStep current observed.final next
  replay : InstalledClientReplay log current.reads history next.state.writer.installed next.state.session

/-- Any finite list of unlock failures preserves the exact ready state
and its ordered diagnostics. The actual admitted retry returns a new
ready session with the same checkpoint, history and client reads. -/
theorem NativeReadPosition.closesAndReopensAfterRetries (current : NativeReadPosition history log) {input : FilePath}
    (observed : NativeReadyCloseRetryObservation current.state input) :
    ∃ next, NativeReadyCloseRetryContinuation current observed next := by
  obtain ⟨next, reopened⟩ := current.closesAndReopens observed.final
  refine ⟨next, NativeReadyCloseError.trace observed.attempts current.readPrefix.refines.1, ?_, reopened, ?_⟩
  · intro attempt _
    obtain ⟨reported, _, session, files, _, replay⟩ := attempt.returns current
    exact ⟨reported, files, session, replay⟩
  · rw [← reopened.reads]
    exact next.readPrefix.guardedReplay

end Alvoki.Storage.DiskSession
