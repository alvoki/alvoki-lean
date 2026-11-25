import Alvoki.Storage.Disk.NativeCheckpointRunFileReboot
import Alvoki.Storage.Disk.NativeQuietPowerLossTableOpen

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

variable {stream : Type} {input : FilePath} {rebooted : heap}
  {calls : RawOpenAdmissionCallbacks heap} {init : OpenSyncCacheCallbacks heap}
  {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}

/-- The reported reboot joins the original stopped checkpoint and the
next raw aligned open without assuming a returned run fsync. One surviving name and byte view explains both
the selected files and the table installed on the reached heap. -/
theorem NativeOpenedPosition.opensAfterStoppedRunFile
    (stopped : RawCheckpointRunFileStop current stop view)
    (reboot : NativeCheckpointRunFileReboot stop)
    (valid : current.current.ready.state.Valid) (plan : reboot.Plan valid)
    {reader : NativeReadyRestartReads (reboot.observed valid) input plan.layout plan.selected}
    (raw : RawQuietRestartEffects reader view calls init names bytes stop.effect.after rebooted
      phaseIdentity tokenIdentity allocatePhase allocateToken stream stop.effect.handle.1)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
      IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files))
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects view.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) :
    let state := current.current.ready.state
    opened.table.UsesOpenCheckpointSchedule state.session.directory opened.files opened.phase ∧
    view.phase stop.effect.after opened.phase = some .poisoned ∧
    stop.onOpenPhase opened (current.reached, stop.effect.prior.entry.image) =
      .error stop.effect.path (stop.effect.prior.atRun 0, state.cache, stop.effect.after) ∧
    view.cacheAt stopped.afterConsume stopped.directory stopped.active stopped.pending = state.cache ∧
    view.descriptors stopped.afterConsume = stop.effect.handle.1 ∧
    (∀ getDirectory getActive openRead, stopped.group getDirectory getActive openRead stop.effect.flushed =
      .error stop.effect.path stop.effect.after) ∧
    (view.handle stop.effect.after opened.lock).2.1 = state.owner ∧
    stop.effect.handle.2.1 ∈ (view.descriptors stop.effect.after).slots ∧
    (view.descriptors stop.effect.after, view.files stop.effect.after) =
      (stop.effect.handle.1, state.files) ∧
    (view.descriptors rebooted, view.files rebooted) = ((reboot.observed valid).reboot, (reboot.observed valid).retry) ∧
    (view.descriptors rebooted).slots = [] ∧
    (∀ path payload, checkpointSurvivorPath state.session.directory state.writer state.writer.target.pair.manifest path →
      reader.ReadsSurvivor path payload → ∃ read : reader.opening.reads.reads.ObservesFile path payload,
        names stop.effect.after path = some read.object ∧ names rebooted path = some read.object ∧ bytes rebooted read.object = payload) ∧
    ∃ (next : NativeReadPosition current.current.history current.current.submissions)
      (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
      (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      DiskTable.OpenSyncFiles.IsOpenAction state.session.directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk state.session.directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      reader.ReachedSession next.state current.current.history current.current.submissions current.current.ready.reads ∧
      raw.openTable remove write rename bootstrap assemble makeCache = .ok handle.table start.reached ∧
      start.current = ⟨current.current.history, current.current.submissions, next⟩ ∧
      handle.lock = raw.admission.raw.lock ∧
      handle.files.UsesCacheReferences raw.admission.seed.activeRef raw.admission.seed.pendingRef
        raw.admission.seed.directoryRef ∧ handle.files.AtDirectory state.session.directory.path ∧
      handle.contents = view.phase ∧ handle.get = get ∧ handle.set = set ∧ handle.ptrEq = ptrEq ∧ start.pins = [] ∧
      view.files start.reached = next.state.files ∧ view.descriptors start.reached = next.state.census ∧
      view.cacheAt start.reached raw.admission.seed.directoryRef raw.admission.seed.activeRef
        raw.admission.seed.pendingRef = next.state.cache := by
  intro state
  obtain ⟨reopened⟩ := RawQuietRestartEffects.reopensSelected current.current.ready raw remove write rename bootstrap assemble ptrEq
    plan.target plan.keeper plan.descriptors plan.offsets plan.prepared constructs effects
  obtain ⟨source, phase, issued, stoppedLock, stoppedFiles⟩ := stopped.reached
  have live := (stop.custody valid).2.1
  rw [← stopped.census] at live
  let installed := reopened.installed
  exact ⟨source, phase, issued, stopped.cleared, stopped.stillHeld, stopped.stopsGroup, stoppedLock, live, stoppedFiles,
    reopened.rebooted, reopened.emptyCensus, reopened.selectedBytes,
    reopened.next, installed.cacheOpen, installed.makeCache, installed.handle, installed.start,
    installed.cacheAction, installed.cacheSource, reopened.session, installed.rawOpen, installed.position,
    installed.lock, installed.references, installed.directory, installed.contents, installed.readsPhase,
    installed.writesPhase, installed.comparesTokens, installed.pins, installed.files, installed.census, installed.cache⟩

end
end Alvoki.Storage.DiskSession
