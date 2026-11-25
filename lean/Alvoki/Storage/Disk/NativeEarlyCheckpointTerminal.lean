import Alvoki.Storage.Disk.NativeExecutionPrefix
import Alvoki.Storage.Disk.NativeEarlyCheckpointStop

namespace Alvoki.Storage.DiskSession

open WalSegmentRepair

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
end Alvoki.Storage.DiskSession
