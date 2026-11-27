import Alvoki.Storage.Disk.NativePendingCheckpoint
import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointErrorPowerLoss

namespace Alvoki.Storage.DiskSession

open System

/-- The issued checkpoint stops at final directory sync. Power loss
uses the same reached physical files and the next open uses the
reported reboot namespace. -/
structure NativePendingCheckpointCrashObservation (state : NativeReadyState) (input : FilePath) where
  image : Type
  cut : CheckpointPowerCut state.session.directory state.writer
  stop : NativeCheckpointDirectoryStop (image := image) state cut
  directory : stop.barrier.bindings stop.reached state.session.directory.path =
    stop.barrier.bindings stop.barrier.observed.renamed.2 state.session.directory.path
  lock : stop.barrier.bindings stop.reached (state.session.directory.file .lock) =
    stop.barrier.bindings stop.barrier.observed.renamed.2 (state.session.directory.file .lock)
  crash : NativeCheckpointCrashFiles stop.physical
  plan : crash.Plan
  reopen : NativeCheckpointCrashAlignedReads crash input plan

/-- The original checkpoint never returned. The resumed position starts
at the actual reported open of one allowed survivor, with the same
acknowledged WAL and recorded responses. -/
structure NativePendingCheckpointReopened (current : NativeReadPosition history log) {input : FilePath}
    (observed : NativePendingCheckpointCrashObservation current.state input) (next : NativeReadPosition history log) : Prop
    extends NativeCheckpointRebootContinuation current observed.crash input next where
  pending : NativePendingCheckpoint current observed.stop

theorem NativeReadPosition.recoversStoppedCheckpointWithReader (current : NativeReadPosition history log) {input : FilePath}
    (observed : NativePendingCheckpointCrashObservation current.state input) :
    ∃ next, NativePendingCheckpointReopened current observed next ∧
      observed.reopen.run = next.opened ∧ next.opened = .ok next.state.session (next.state.census, next.state.files) ∧
      next.state.owner = observed.reopen.opening.admission.owner ∧
      next.state.directorySlot = observed.reopen.opening.admission.cached ∧
      next.state.cache = observed.reopen.opening.admission.cache := by
  have stopped := current.stopsDuringCheckpoint observed.stop
  have paths := observed.stop.barrier.issueBindings observed.stop.barrier.observed.renamed.2 (by simp)
  obtain ⟨next, reopened, sameReturn, returned, owner, slot, cache⟩ := current.reopensCheckpointSurvivorWith observed.crash
    (observed.directory.trans paths.1) (observed.lock.trans paths.2) observed.reopen
  exact ⟨next, ⟨reopened, stopped⟩, sameReturn, returned, owner, slot, cache⟩

theorem NativeReadPosition.recoversStoppedCheckpoint (current : NativeReadPosition history log) {input : FilePath}
    (observed : NativePendingCheckpointCrashObservation current.state input) :
    ∃ next, NativePendingCheckpointReopened current observed next := by
  obtain ⟨next, reopened, _⟩ := current.recoversStoppedCheckpointWithReader observed
  exact ⟨next, reopened⟩

end Alvoki.Storage.DiskSession
