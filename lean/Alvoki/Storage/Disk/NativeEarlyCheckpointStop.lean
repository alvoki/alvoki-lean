import Alvoki.Storage.Disk.NativeStoppedRunDirectoryTableOpen
import Alvoki.Storage.Disk.NativeStoppedRunFileTableOpen

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- The original opened checkpoint issues either the selected run fsync
or the first directory fsync. The stop fixes the reached heap before
any reboot image is chosen. -/
inductive RawEarlyCheckpointStop (current : NativeOpenedPosition opened) (view : OpenCloseHeapView heap FileImage) where
  | file {cut : CheckpointPowerCut current.current.ready.state.session.directory current.current.ready.state.writer}
      {stop : NativeCheckpointRunFileStop (image := heap) current.current.ready.state cut}
      (raw : RawCheckpointRunFileStop current stop view)
  | directory {cut : CheckpointPowerCut current.current.ready.state.session.directory current.current.ready.state.writer}
      {stop : NativeCheckpointRunDirectoryStop (image := heap) current.current.ready.state cut}
      (raw : RawCheckpointRunDirectoryStop current stop view)

namespace RawEarlyCheckpointStop

variable {current : NativeOpenedPosition opened} {view : OpenCloseHeapView heap FileImage}
  (seen : RawEarlyCheckpointStop current view)

def stoppedHeap : heap :=
  match seen with
  | .file (stop := stop) _ => stop.effect.after
  | .directory (stop := stop) _ => stop.reached

def census : DescriptorInventory :=
  match seen with
  | .file (stop := stop) _ => stop.effect.handle.1
  | .directory _ => current.current.ready.state.census

def files : LockedFileState FileImage :=
  match seen with
  | .file _ => current.current.ready.state.files
  | .directory (stop := stop) _ => ⟨stop.runs.files stop.reached, current.current.ready.state.files.owners⟩

/-- The modeled WAL and metadata are already settled. The first directory
barrier can settle staged run names in the physical view without changing
this projection. -/
theorem filesPreserved : seen.files = current.current.ready.state.files := by
  cases seen with
  | file _ => rfl
  | @directory cut stop _ =>
    let state := current.current.ready.state
    have valid : state.Valid := current.current.ready.readPrefix.refines.1
    have atIssue := stop.runs.filesAtRun _ (Nat.le_refl _)
    have settled : state.files.image.directory.syncDirectory = state.files.image.directory := by
      change state.writer.files.directory.syncDirectory = state.writer.files.directory
      have choices := valid.retained.resumed.ready.settled.trans
        (congrArg (fun active => [active]) valid.retained.resumed.ready.selected.symm)
      rw [DirectoryPublication.Image.syncDirectory, ← choices]
    have directory : (stop.runs.files stop.reached).directory = state.files.image.directory := by
      rw [stop.directoryEffect, atIssue]
      change (if cut.tookEffect then state.files.image.directory.syncDirectory else state.files.image.directory) =
        state.files.image.directory
      rw [settled, ite_self]
    have wal := stop.walFrame.trans (congrArg CheckpointWalView.ofFiles atIssue)
    have image : stop.runs.files stop.reached = state.files.image := by
      revert directory wal
      generalize stop.runs.files stop.reached = reached
      generalize state.files.image = prior
      cases reached
      cases prior
      simp +contextual [CheckpointWalView.ofFiles]
    exact congrArg (fun files => (⟨files, state.files.owners⟩ : LockedFileState FileImage)) image

include seen in
theorem samePhase : view.phase = opened.contents := by
  cases seen with
  | file raw => exact raw.samePhase
  | directory raw => exact raw.samePhase

/-- The actual raw sync group uses either the consumed pending run slot
or the cached directory slot. Their outer stops issue no public return. -/
def Issued : Prop :=
  match seen with
  | .file (stop := stop) raw =>
    stop.onOpenPhase opened (current.reached, stop.effect.prior.entry.image) =
      .error stop.effect.path (stop.effect.prior.atRun 0, current.current.ready.state.cache, stop.effect.after) ∧
    (∀ getDirectory getActive openRead, raw.group getDirectory getActive openRead stop.effect.flushed =
      .error stop.effect.path stop.effect.after) ∧
    view.cacheAt raw.afterConsume raw.directory raw.active raw.pending = current.current.ready.state.cache ∧
    view.descriptors raw.afterConsume = stop.effect.handle.1 ∧
    stop.effect.handle.2.1 ∈ (view.descriptors stop.effect.after).slots
  | .directory (stop := stop) raw =>
    stop.onOpenPhase opened (current.reached, stop.runs.entry.image) =
      .error current.current.ready.state.session.directory.path
        (stop.runs.atRun 0, current.current.ready.state.cache, stop.reached) ∧
    (∀ pending setPending active openRead, raw.group pending setPending active openRead stop.atIssue =
      .error current.current.ready.state.session.directory.path stop.reached)

/-- The old table is poisoned and still holds its lock at the actual
issued stop, with the cut's exact descriptor census and files. -/
structure Reached : Prop where
  source : opened.table.UsesOpenCheckpointSchedule current.current.ready.state.session.directory opened.files opened.phase
  phase : view.phase seen.stoppedHeap opened.phase = some .poisoned
  oldLock : (view.handle seen.stoppedHeap opened.lock).2.1 = current.current.ready.state.owner
  stoppedFiles : (view.descriptors seen.stoppedHeap, view.files seen.stoppedHeap) = (seen.census, seen.files)
  issued : seen.Issued

theorem reaches : seen.Reached := by
  cases seen with
  | @file _ stop raw =>
    obtain ⟨source, phase, outer, lock, files⟩ := raw.reached
    have live := (stop.custody current.current.ready.readPrefix.refines.1).2.1
    rw [← raw.census] at live
    exact ⟨source, phase, lock, files, outer, raw.stopsGroup, raw.cleared, raw.stillHeld, live⟩
  | directory raw =>
    obtain ⟨source, phase, outer, lock, files⟩ := raw.reached
    exact ⟨source, phase, lock, files, outer, raw.stopsGroup⟩

/-- The modeled files and exact descriptor census at the stopped heap. -/
theorem stoppedState : (view.descriptors seen.stoppedHeap, view.files seen.stoppedHeap) =
    (seen.census, current.current.ready.state.files) := by
  have valid := current.current.ready.readPrefix.refines.1
  have sameFiles := seen.filesPreserved
  cases seen with
  | @file _ stop raw =>
    have sameImage := congrArg (fun image => (⟨image, current.current.ready.state.files.owners⟩ : LockedFileState FileImage))
      stop.effect.filesAtEffect
    exact Prod.ext (raw.census.trans (stop.custody valid).1) (raw.files.trans sameImage)
  | @directory _ stop raw =>
    exact Prod.ext (raw.census.trans (stop.custody valid).2.1) (raw.files.trans sameFiles)

end RawEarlyCheckpointStop

end Alvoki.Storage.DiskSession
