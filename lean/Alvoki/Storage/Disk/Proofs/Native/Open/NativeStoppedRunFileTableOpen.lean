import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointRunFileReboot
import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointRunFileOpenPhase
import Alvoki.Storage.Disk.Proofs.Native.Open.NativeQuietPowerLossTableOpen

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair

section

variable {heap : Type} {opened : NativeOpenedHandle heap} {current : NativeOpenedPosition opened}
  {cut : CheckpointPowerCut current.current.ready.state.session.directory current.current.ready.state.writer}
  {stop : NativeCheckpointRunFileStop (image := heap) current.current.ready.state cut}
  {view : OpenCloseHeapView heap FileImage}

/-- The original opened table's pending ref contains the flushed run.
Its read and consume precede the same stopped raw sync; consuming the
entry does not release its still-issued native descriptor. -/
structure RawCheckpointRunFileStop (current : NativeOpenedPosition opened)
    {cut : CheckpointPowerCut current.current.ready.state.session.directory current.current.ready.state.writer}
    (stop : NativeCheckpointRunFileStop (image := heap) current.current.ready.state cut)
    (view : OpenCloseHeapView heap FileImage) where
  writesPhase : opened.set opened.phase .poisoned current.reached = .ok () (stop.effect.prior.atRun 0)
  samePhase : view.phase = opened.contents
  keepsPhase : view.phase stop.effect.after opened.phase = view.phase (stop.effect.prior.atRun 0) opened.phase
  directory : IO.Ref (Option IO.FS.Handle)
  active : IO.Ref (Option (FilePath × IO.FS.Handle))
  pending : IO.Ref (List (FilePath × IO.FS.Handle))
  references : opened.files.UsesCacheReferences active pending directory
  beforeConsume : view.cacheAt stop.effect.flushed directory active pending = stop.issue.atIssue.1
  handle : IO.FS.Handle
  staged : view.pending stop.effect.flushed pending = [(stop.effect.path, handle)]
  load : IO.Ref (List (FilePath × IO.FS.Handle)) → EStateM IO.Error heap (List (FilePath × IO.FS.Handle))
  store : IO.Ref (List (FilePath × IO.FS.Handle)) → List (FilePath × IO.FS.Handle) → EStateM IO.Error heap Unit
  afterConsume : heap
  loaded : load pending stop.effect.flushed = .ok [(stop.effect.path, handle)] stop.effect.flushed
  consumed : store pending [] stop.effect.flushed = .ok () afterConsume
  selected : view.handle afterConsume handle = view.handle stop.effect.flushed handle
  cleared : view.cacheAt afterConsume directory active pending = current.current.ready.state.cache
  stillHeld : view.descriptors afterConsume = stop.effect.handle.1
  sync : IO.FS.Handle → EStateM FilePath heap (Except IO.Error Unit)
  sameSync : stop.fsync (view.handle afterConsume handle) stop.effect.flushed = sync handle afterConsume
  initialLock : (view.handle current.reached opened.lock).2.1 = current.current.ready.state.owner
  retainedLock : (view.handle stop.effect.after opened.lock).2.1 = (view.handle current.reached opened.lock).2.1
  census : view.descriptors stop.effect.after = stop.effect.prior.descriptors stop.effect.after
  files : view.files stop.effect.after = ⟨stop.effect.prior.files stop.effect.after, current.current.ready.state.files.owners⟩

namespace RawCheckpointRunFileStop

private abbrev StoppedSync (heap : Type) := ExceptT IO.Error (EStateM FilePath heap)

private def returned {α : Type} (call : EStateM IO.Error heap α) : StoppedSync heap α :=
  fun before => match call before with
    | .ok value after => .ok (.ok value) after
    | .error cause after => .ok (.error cause) after

variable (seen : RawCheckpointRunFileStop current stop view)

theorem selectedHandle : view.handle seen.afterConsume seen.handle = stop.effect.handle := by
  have cached := congrArg Cache.pending seen.beforeConsume
  have empty := stop.effect.prior.pending
  simp only [OpenCloseHeapView.cacheAt, seen.staged, List.map_cons, List.map_nil,
    NativeCheckpointRunFileIssue.atIssue, Cache.remember, pushPending, empty,
    List.cons.injEq, Prod.mk.injEq] at cached
  exact seen.selected.trans cached.1.2

def group (getDirectory : StoppedSync heap (Option IO.FS.Handle))
    (getActive : StoppedSync heap (Option (FilePath × IO.FS.Handle)))
    (openRead : FilePath → StoppedSync heap IO.FS.Handle) : EStateM FilePath heap (Except IO.Error Unit) :=
  let root := current.current.ready.state.session.directory.path
  (SyncPathGroup.run (fun path => syncWithHandles root path getDirectory
    (returned (seen.load seen.pending)) (fun entries => returned (seen.store seen.pending entries))
    getActive openRead (fun handle => seen.sync handle)) #[stop.effect.path]).run

theorem stopsGroup (getDirectory getActive openRead) :
    seen.group getDirectory getActive openRead stop.effect.flushed = .error stop.effect.path stop.effect.after := by
  have rawSync : seen.sync seen.handle seen.afterConsume = .error stop.effect.path stop.effect.after := by
    rw [← seen.sameSync, seen.selectedHandle]
    exact stop.stopped
  have different : stop.effect.path ≠ current.current.ready.state.session.directory.path := file_ne_directory _ _
  simp [group, SyncPathGroup.run, ← Array.forIn_toList, List.forIn_cons, List.forIn_nil, MonadExcept.tryCatch,
    MonadExceptOf.tryCatch, tryCatchThe, ExceptT.tryCatch, syncWithHandles, Bind.bind, ExceptT.bind, ExceptT.run,
    ExceptT.mk, EStateM.bind, ExceptT.bindCont, StateT.pure, Pure.pure, ExceptT.pure, EStateM.pure, returned, seen.loaded,
    seen.consumed, rawSync, different]

include seen in
theorem reached :
    let state := current.current.ready.state
    opened.table.UsesOpenCheckpointSchedule state.session.directory opened.files opened.phase ∧
    view.phase stop.effect.after opened.phase = some .poisoned ∧
    stop.onOpenPhase opened (current.reached, stop.effect.prior.entry.image) =
      .error stop.effect.path (stop.effect.prior.atRun 0, state.cache, stop.effect.after) ∧
    (view.handle stop.effect.after opened.lock).2.1 = state.owner ∧
    (view.descriptors stop.effect.after, view.files stop.effect.after) = (stop.effect.handle.1, state.files) := by
  intro state
  have valid := current.current.ready.readPrefix.refines.1
  obtain ⟨source, _, poisoned, stored, _, wrote, stopped⟩ := current.stopsAtCheckpointRunFile stop
  have same := (EStateM.Result.ok.inj (wrote.symm.trans seen.writesPhase)).2
  refine ⟨source, ?_, same ▸ stopped, seen.retainedLock.trans seen.initialLock,
    Prod.ext (seen.census.trans (stop.custody valid).1) (seen.files.trans ?_)⟩
  · rw [seen.keepsPhase, seen.samePhase, ← same]
    exact stored
  · exact congrArg (fun files => LockedFileState.mk files state.files.owners) stop.effect.filesAtEffect

end RawCheckpointRunFileStop

end
end Alvoki.Storage.DiskSession
