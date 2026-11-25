import Alvoki.Storage.Disk.NativeCheckpointSourceCrash
import Alvoki.Storage.Disk.NativeQuietPowerLossRaw

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair

variable {heap : Type} {opened : NativeOpenedHandle heap} {current : NativeOpenedPosition opened}
  {primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap} {fsync : CheckpointFsync heap}
  {stage : CheckpointPublication.Step} {reason : FilePath} {reached : CheckpointWorld heap}
  {view : OpenCloseHeapView heap FileImage} {storage : heap → CheckpointStorageObservation}
  {rebooted : heap} {bytes : heap → Nat → ByteArray}

/-- The optional reboot starts at the source stop's exact heap. It chooses
one joint survivor of the reached protected files. The normalized file
image frames the old logical checkpoint and WAL. Physical run bindings
can change outside that projection. -/
theorem NativeCheckpointSourceStop.observesReboot
    (stop : NativeCheckpointSourceStop current primitives fsync stage reason reached)
    (stable : NativeReadyStorage current.current.ready.state (storage reached.2))
    (previous : view.files reached.2 = current.current.ready.state.files)
    (names : FilePath → Option Nat) (chosen : names ∈ (storage reached.2).crashNames)
    (contents : Nat → ByteArray)
    (durable : ∀ path,
      checkpointSurvivorPath current.current.ready.state.session.directory current.current.ready.state.writer
        current.current.ready.state.writer.target.pair.manifest path →
      ∀ inode, names path = some inode → contents inode ∈ (storage reached.2).files.bytes inode)
    (rebootObjects : Nat → Nat)
    (survivorNames : ∀ path, current.current.ready.state.crashPath path →
      (storage rebooted).files.names path = names path)
    (survivorBytes : ∀ path,
      checkpointSurvivorPath current.current.ready.state.session.directory current.current.ready.state.writer
        current.current.ready.state.writer.target.pair.manifest path →
      ∀ inode, names path = some inode → bytes rebooted inode = contents inode) :
    let crash := stable.observeCrash names chosen contents durable rebootObjects
    (runCheckpointOnOpenPhaseUntilSyncStop current.current.ready.state.session.directory
      opened.phase opened.get opened.set primitives fsync).run
      (current.current.ready.state.cache, current.reached) = .error (stage, reason) reached ∧
    RawQuietRebootEntry crash view (fun atHeap => (storage atHeap).files.names) bytes reached.2 rebooted
      (view.descriptors reached.2) := by
  exact ⟨stop.stoppedCall, ⟨Prod.ext rfl previous, fun _ _ => rfl, survivorNames, survivorBytes⟩⟩

end Alvoki.Storage.DiskSession
