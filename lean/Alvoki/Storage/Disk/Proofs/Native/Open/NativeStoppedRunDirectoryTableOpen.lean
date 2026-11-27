import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointRunDirectoryStop
import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointRunDirectoryReboot
import Alvoki.Storage.Disk.Proofs.Native.Open.NativeQuietPowerLossTableOpen

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair

section

variable {heap : Type} {opened : NativeOpenedHandle heap} {current : NativeOpenedPosition opened}
  {cut : CheckpointPowerCut current.current.ready.state.session.directory current.current.ready.state.writer}
  {stop : NativeCheckpointRunDirectoryStop (image := heap) current.current.ready.state cut}
  {view : OpenCloseHeapView heap FileImage}

/-- Join the actual opened phase and its cache cells to the primitive
run callbacks in one heap. The raw sync reports the same outer cut. -/
structure RawCheckpointRunDirectoryStop (current : NativeOpenedPosition opened)
    {cut : CheckpointPowerCut current.current.ready.state.session.directory current.current.ready.state.writer}
    (stop : NativeCheckpointRunDirectoryStop (image := heap) current.current.ready.state cut)
    (view : OpenCloseHeapView heap FileImage) where
  writesPhase : opened.set opened.phase .poisoned current.reached = .ok () (stop.runs.atRun 0)
  samePhase : view.phase = opened.contents
  keepsPhase : view.phase stop.reached opened.phase = view.phase (stop.runs.atRun 0) opened.phase
  active : IO.Ref (Option (FilePath × IO.FS.Handle))
  pending : IO.Ref (List (FilePath × IO.FS.Handle))
  directory : IO.Ref (Option IO.FS.Handle)
  references : opened.files.UsesCacheReferences active pending directory
  cache : view.cacheAt stop.atIssue directory active pending = current.current.ready.state.cache
  handle : IO.FS.Handle
  cached : view.directory stop.atIssue directory = some handle
  load : IO.Ref (Option IO.FS.Handle) → EStateM IO.Error heap (Option IO.FS.Handle)
  loaded : load directory stop.atIssue = .ok (some handle) stop.atIssue
  sync : IO.FS.Handle → EStateM FilePath heap (Except IO.Error Unit)
  sameSync : stop.fsync (view.handle stop.atIssue handle) = sync handle
  initialLock : (view.handle current.reached opened.lock).2.1 = current.current.ready.state.owner
  retainedLock : (view.handle stop.reached opened.lock).2.1 = (view.handle current.reached opened.lock).2.1
  census : view.descriptors stop.reached = stop.runs.descriptors stop.reached
  files : view.files stop.reached = ⟨stop.runs.files stop.reached, current.current.ready.state.files.owners⟩

namespace RawCheckpointRunDirectoryStop

private abbrev StoppedSync (heap : Type) := ExceptT IO.Error (EStateM FilePath heap)

private def returned {α : Type} (call : EStateM IO.Error heap α) : StoppedSync heap α :=
  fun before => match call before with
    | .ok value after => .ok (.ok value) after
    | .error cause after => .ok (.error cause) after

variable (seen : RawCheckpointRunDirectoryStop current stop view)

theorem cachedHandle : view.handle stop.atIssue seen.handle = stop.handle := by
  have directory := congrArg Cache.directory seen.cache
  simp only [OpenCloseHeapView.cacheAt, seen.cached, Option.map_some, stop.runs.directoryCached] at directory
  exact Option.some.inj directory

def group (getPending : StoppedSync heap (List (FilePath × IO.FS.Handle)))
    (setPending : List (FilePath × IO.FS.Handle) → StoppedSync heap Unit)
    (getActive : StoppedSync heap (Option (FilePath × IO.FS.Handle))) (openRead : FilePath → StoppedSync heap IO.FS.Handle) :
    EStateM FilePath heap (Except IO.Error Unit) :=
  let root := current.current.ready.state.session.directory.path
  (SyncPathGroup.run (fun path => syncWithHandles root path (returned (seen.load seen.directory))
    getPending setPending getActive openRead (fun handle => seen.sync handle)) #[root]).run

theorem stopsGroup (getPending setPending getActive openRead) :
    seen.group getPending setPending getActive openRead stop.atIssue =
      .error current.current.ready.state.session.directory.path stop.reached := by
  have rawSync : seen.sync seen.handle stop.atIssue = .error current.current.ready.state.session.directory.path stop.reached := by
    rw [← seen.sameSync, seen.cachedHandle]
    exact stop.stopped
  simp [group, SyncPathGroup.run, ← Array.forIn_toList, List.forIn_cons, List.forIn_nil, MonadExcept.tryCatch,
    MonadExceptOf.tryCatch, tryCatchThe, ExceptT.tryCatch, syncWithHandles, Bind.bind, ExceptT.bind, ExceptT.run,
    ExceptT.mk, EStateM.bind, ExceptT.bindCont, StateT.pure, Pure.pure, ExceptT.pure, EStateM.pure, returned, seen.loaded, rawSync]

include seen in
theorem reached :
    let state := current.current.ready.state
    opened.table.UsesOpenCheckpointSchedule state.session.directory opened.files opened.phase ∧
    view.phase stop.reached opened.phase = some .poisoned ∧
    stop.onOpenPhase opened (current.reached, stop.runs.entry.image) =
      .error state.session.directory.path (stop.runs.atRun 0, state.cache, stop.reached) ∧
    (view.handle stop.reached opened.lock).2.1 = state.owner ∧
    (view.descriptors stop.reached, view.files stop.reached) =
      (state.census, ⟨stop.runs.files stop.reached, state.files.owners⟩) := by
  intro state
  have valid := current.current.ready.readPrefix.refines.1
  obtain ⟨source, _, _, _, _, poisoned, stored, _, wrote, stopped⟩ :=
    NativeCheckpointRunDirectoryStop.stopsOnOpenPhase current stop
  have same := (EStateM.Result.ok.inj (wrote.symm.trans seen.writesPhase)).2
  refine ⟨source, ?_, same ▸ stopped, seen.retainedLock.trans seen.initialLock,
    Prod.ext (seen.census.trans (stop.custody valid).2.1) seen.files⟩
  rw [seen.keepsPhase, seen.samePhase, ← same]
  exact stored

end RawCheckpointRunDirectoryStop

end
end Alvoki.Storage.DiskSession
