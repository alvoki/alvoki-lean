import Alvoki.Storage.Disk.NativeExecutionPrefix
import Alvoki.Storage.Disk.NativeEarlyCheckpointStop

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

/-- Use the full interpreted checkpoint call and its reached protected
storage as the terminal endpoint of the same finite replay. -/
def terminalPrefix {storage : heap → CheckpointStorageObservation}
    (early : stage = .syncRunsDirectory ∨ ∃ index, stage = .syncRun index)
    (stable : NativeReadyStorage current.current.ready.state (storage reached.2))
    (returnedKeeps : ∀ step ∈ stop.completed, ∀ before after,
      (primitives.checkpointStepUntilStop current.current.ready.state.session.directory
        fsync stop.next stop.manifest step).run before = .ok (.ok ()) after →
      opened.contents after.2 opened.phase = opened.contents before.2 opened.phase)
    (stoppedKeeps : opened.contents reached.2 opened.phase = opened.contents stop.atIssue.2 opened.phase)
    (ordered : NativeExecutionInstructions instructions events)
    (prior : NativeExecutionTrace start events current.current) :
    NativeReachedExecutionPrefix start instructions .checkpoint :=
  let ending := NativeExecutionEnd.stoppedEarlyCheckpoint rfl stop early (stop.phaseAtStop returnedKeeps stoppedKeeps) stable
  ⟨events, current.current, ending, ordered, prior, rfl, ending.reached⟩

end NativeCheckpointSourceStop
end Alvoki.Storage.DiskSession
