import Alvoki.Storage.Disk.CheckpointPreflight
import Alvoki.Storage.Disk.NativeReadRecoveryTrace

namespace Alvoki.Storage.DiskSession

open CheckpointPublication

/-- Checkpoint preflight rejects at the exact reached ready phase. The
same position, including its file state, descriptors, pins and ledger,
is available to the next instruction. -/
structure NativeCheckpointRejectedStep (current : NativeReadPosition history log)
    (cause : IO.Error) (next : NativeReadPosition history log) : Prop where
  unchanged : next = current
  returned : ∀ {image : Type}
      (perform : Installed → ByteArray → Step → EStateM IO.Error image Unit) (files : LockedFileState image),
    runCheckpointWithEffects perform (current.state.session.phase, files) =
      .error cause (current.state.session.phase, files)

/-- A reported failed flush, bound or manifest check returns its own
diagnostic before poisoning or dispatching any publication callback. -/
theorem NativeReadPosition.rejectsCheckpoint (current : NativeReadPosition history log) {cause : IO.Error}
    (preflight : CheckpointPreflight (.ready current.state.writer.installed) (.error cause)) :
    NativeCheckpointRejectedStep current cause current := by
  refine ⟨rfl, ?_⟩
  intro image perform files
  rw [current.readPrefix.refines.1.phase]
  exact preflight.rejected perform files

end Alvoki.Storage.DiskSession
