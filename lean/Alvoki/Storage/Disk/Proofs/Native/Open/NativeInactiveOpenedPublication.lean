import Alvoki.Storage.Disk.Proofs.Native.Open.NativeOpenedPosition
import Alvoki.Storage.Disk.Proofs.Native.Execution.NativeInactiveSessionCalls
import Alvoki.Storage.Disk.Proofs.Write.NativeOpenWrite
import Alvoki.Storage.Disk.Proofs.Native.Checkpoint.NativeOpenCheckpoint

namespace Alvoki.Storage.DiskSession.NativeOpenedHandle

variable {heap : Type} (opened : NativeOpenedHandle heap)
  {before : heap} {mode : NativeInactivePhase}

/-- The original closed or poisoned receiver rejects single writes and
batches before checking or modifying any WAL file. The classified API
returns rejected and the plain API exposes the same underlying cause. -/
theorem rejectsInactiveWrite
    (stored : opened.contents before opened.phase = some mode.phase) (request : WriteRequest) :
    opened.table.UsesOpenWriteSchedules opened.directory opened.files opened.phase ∧
    ∀ (calls : WriteRequest.Calls (DescriptorInventory × DescriptorSlot × Nat)) (files : OpenWriteFiles),
      let result := request.runOnOpenPhase opened.directory calls opened.phase opened.get opened.set (before, files)
      result = .error (.rejected mode.error) (before, files) ∧
      WriteRequest.plainResult result = .error mode.error (before, files) := by
  have loaded := opened.phaseEffects.reads before opened.phase _ stored
  have rejected : (mode.phase.installed : Except IO.Error Installed) = .error mode.error := by
    cases mode <;> rfl
  refine ⟨opened.uses.writeSchedules, ?_⟩
  intro calls files result
  have ran := request.runOnOpenPhase_rejectsPhase opened.directory calls opened.phase opened.get opened.set
    loaded rejected files
  refine ⟨ran, ?_⟩
  change WriteRequest.plainResult
    (request.runOnOpenPhase opened.directory calls opened.phase opened.get opened.set (before, files)) = _
  rw [ran]
  rfl

/-- Checkpointing on the same inactive handle returns the phase error
without reaching a checkpoint store or changing the original heap. -/
theorem rejectsInactiveCheckpoint {image : Type}
    (stored : opened.contents before opened.phase = some mode.phase) :
    opened.table.UsesOpenCheckpointSchedule opened.directory opened.files opened.phase ∧
    ∀ (perform : Installed → ByteArray → CheckpointPublication.Step → EStateM IO.Error image Unit) (files : image),
      runCheckpointOnOpenPhase perform opened.phase opened.get opened.set (before, files) =
        .error mode.error (before, files) := by
  have loaded := opened.phaseEffects.reads before opened.phase _ stored
  have rejected : (mode.phase.installed : EStateM IO.Error (heap × image) Installed) =
      (fun state => .error mode.error state) := by
    cases mode <;> rfl
  exact ⟨opened.uses.checkpoint, fun perform files =>
    runCheckpointOnOpenPhase_rejectsPhase perform opened.phase opened.get opened.set loaded rejected files⟩

end Alvoki.Storage.DiskSession.NativeOpenedHandle
