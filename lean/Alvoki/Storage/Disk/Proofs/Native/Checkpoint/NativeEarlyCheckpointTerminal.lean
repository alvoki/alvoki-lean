import Alvoki.Storage.Disk.Proofs.Native.Execution.NativeExecutionPrefix
import Alvoki.Storage.Disk.Proofs.Native.Checkpoint.NativeEarlyCheckpointStop

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair

namespace RawEarlyCheckpointStop

variable {heap : Type} {opened : NativeOpenedHandle heap} {current : NativeOpenedPosition opened}
  {view : OpenCloseHeapView heap FileImage} (seen : RawEarlyCheckpointStop current view)

def ending : NativeExecutionEnd current.current :=
  match seen with
  | .file (stop := stop) _ => .interruptedCheckpointRunFile stop
  | .directory (stop := stop) _ => .interruptedCheckpointRunDirectory stop

theorem endingInstruction : seen.ending.instruction = .checkpoint := by
  cases seen <;> rfl

/-- Stop the finite execution at the issued call. The same raw witness
can instead select a reboot and continue through the opened-session proof. -/
def terminalPrefix (ordered : NativeExecutionInstructions instructions events)
    (prior : NativeExecutionTrace start events current.current) :
    NativeReachedExecutionPrefix start instructions .checkpoint :=
  ⟨events, current.current, seen.ending, ordered, prior, seen.endingInstruction, seen.ending.reached⟩

end RawEarlyCheckpointStop

namespace NativeCheckpointSourceStop

variable {heap : Type} {opened : NativeOpenedHandle heap} {current : NativeOpenedPosition opened}
  {primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap} {fsync : CheckpointFsync heap}
  {stage : CheckpointPublication.Step} {reason : FilePath} {reached : CheckpointWorld heap}
  (stop : NativeCheckpointSourceStop current primitives fsync stage reason reached)

/-- The exact source stop is a terminal endpoint on the current writer.
The issued stage indexes the call. Recovery proves what survives separately. -/
def terminalEnd
    (returnedKeeps : ∀ step ∈ stop.completed, ∀ before after,
      (primitives.checkpointStepUntilStop current.current.ready.state.session.directory
        fsync stop.next stop.manifest step).run before = .ok (.ok ()) after →
      opened.contents after.2 opened.phase = opened.contents before.2 opened.phase)
    (stoppedKeeps : opened.contents reached.2 opened.phase = opened.contents stop.atIssue.2 opened.phase) :
    NativeExecutionEnd current.current :=
  .stoppedCheckpoint rfl stop (stop.phaseAtStop returnedKeeps stoppedKeeps)

/-- Use the same terminal endpoint for a modeled finite prefix. -/
def terminalPrefix
    (returnedKeeps : ∀ step ∈ stop.completed, ∀ before after,
      (primitives.checkpointStepUntilStop current.current.ready.state.session.directory
        fsync stop.next stop.manifest step).run before = .ok (.ok ()) after →
      opened.contents after.2 opened.phase = opened.contents before.2 opened.phase)
    (stoppedKeeps : opened.contents reached.2 opened.phase = opened.contents stop.atIssue.2 opened.phase)
    (ordered : NativeExecutionInstructions instructions events)
    (prior : NativeExecutionTrace start events current.current) :
    NativeReachedExecutionPrefix start instructions .checkpoint :=
  let ending := stop.terminalEnd returnedKeeps stoppedKeeps
  ⟨events, current.current, ending, ordered, prior, rfl, ending.reached⟩

/-- The reached source endpoint also refines a ledger proved directly
from raw acknowledgements and reads. -/
theorem refinesTerminalLedger
    {start : NativeExecutionPosition} {events : List NativeExecutionEvent}
    (returnedKeeps : ∀ step ∈ stop.completed, ∀ before after,
      (primitives.checkpointStepUntilStop current.current.ready.state.session.directory
        fsync stop.next stop.manifest step).run before = .ok (.ok ()) after →
      opened.contents after.2 opened.phase = opened.contents before.2 opened.phase)
    (stoppedKeeps : opened.contents reached.2 opened.phase = opened.contents stop.atIssue.2 opened.phase)
    (prior : start.LedgerSuffix events current.current) :
    let ending := stop.terminalEnd returnedKeeps stoppedKeeps
    (∀ event ∈ events, event.uncertainBatchWhole) ∧ ending.Reached ∧
    ∃ chosen, ending.allows chosen ∧ PendingClientReplay ending.submissions current.current.ready.reads chosen ∧
      ∀ read ∈ current.current.ready.reads, read.BoundedBy chosen.length := by
  intro ending
  exact ⟨prior.whole, ending.reached, ending.selectsAtEnd⟩

end NativeCheckpointSourceStop
end Alvoki.Storage.DiskSession
