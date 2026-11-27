import Alvoki.Storage.Disk.Proofs.Native.Execution.NativePendingCloseReferenceDrop

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

inductive PendingCloseRelease where
  | successfulUnlock
  | lastReferenceDrop

/-- A failed write can require several attempts to release its lock.
The final release is either a returned unlock or the last reference
drop after a returned unlock error. Both use the reached marked files. -/
inductive NativePendingCloseRecovery {current : NativeReadPosition history log}
    (pending : NativePendingWrite current) (input : FilePath) where
  | unlocked (seen : NativePendingCloseRetryOpen pending input)
  | dropped (seen : NativePendingCloseReferenceDrop pending)
      (observe : pending.write.ReleasedMarkedReports input seen.census
        (seen.failed.close.report.bindings (current.state.session.directory.file .lock)))

namespace NativePendingCloseRecovery

variable {current : NativeReadPosition history log} {pending : NativePendingWrite current} {input : FilePath}

def release : NativePendingCloseRecovery pending input → PendingCloseRelease
  | .unlocked _ => .successfulUnlock
  | .dropped _ _ => .lastReferenceDrop

def errors : NativePendingCloseRecovery pending input → List IO.Error
  | .unlocked seen => seen.attempts.map (·.cause)
  | .dropped seen _ => seen.attempts.map (·.cause)

def Reopened (reported : NativePendingCloseRecovery pending input)
    (retained : List WAL.Write) (next : NativeReadPosition (history ++ retained) pending.submissions) : Prop :=
  match reported with
  | .unlocked seen => NativePendingCloseRetryContinuation seen retained next
  | .dropped seen _ => NativePendingCloseDropReopened (input := input) seen retained next

theorem frames (reported : NativePendingCloseRecovery pending input)
    (reopened : reported.Reopened retained next) :
    (retained = [] ∨ retained = pending.write.failure.batch) ∧ next.reads = current.reads := by
  cases reported with
  | unlocked seen =>
    change NativePendingCloseRetryContinuation seen retained next at reopened
    exact ⟨reopened.wholeOrNone, reopened.reads⟩
  | dropped seen _ =>
    change NativePendingCloseDropReopened (input := input) seen retained next at reopened
    exact ⟨reopened.wholeOrNone, reopened.reads⟩

theorem reopens (reported : NativePendingCloseRecovery pending input) :
    ∃ retained next, reported.Reopened retained next := by
  cases reported with
  | unlocked seen => exact pending.recoversAfterCloseRetries seen
  | dropped seen observe => exact pending.recoversAfterFailedClosesAndDrop seen observe

end NativePendingCloseRecovery
end Alvoki.Storage.DiskSession
