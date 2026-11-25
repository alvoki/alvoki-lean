import Alvoki.Storage.Disk.NativeCheckpointRunDirectoryReboot
import Alvoki.Storage.Disk.NativeQuietPowerLossTableOpen

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

variable {stream : Type} {input : FilePath} {rebooted : heap}
  {calls : RawOpenAdmissionCallbacks heap} {init : OpenSyncCacheCallbacks heap}
  {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}

/-- The reported reboot joins the original stopped checkpoint and the
next raw aligned open. One surviving name and byte view explains both
the selected files and the table installed on the reached heap. -/
theorem NativeOpenedPosition.opensAfterStoppedRunDirectory
    (stopped : RawCheckpointRunDirectoryStop current stop view)
    (reboot : NativeCheckpointRunDirectoryReboot stop)
    (valid : current.current.ready.state.Valid) (plan : reboot.Plan valid)
    {reader : NativeReadyRestartReads (reboot.observed valid) input plan.layout plan.selected}
    (raw : RawQuietRestartEffects reader view calls init names bytes stop.reached rebooted
      phaseIdentity tokenIdentity allocatePhase allocateToken stream)
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
    view.phase stop.reached opened.phase = some .poisoned ∧
    stop.onOpenPhase opened (current.reached, stop.runs.entry.image) =
      .error state.session.directory.path (stop.runs.atRun 0, state.cache, stop.reached) ∧
    (∀ getPending setPending getActive openRead, stopped.group getPending setPending getActive openRead stop.atIssue =
      .error state.session.directory.path stop.reached) ∧
    (view.handle stop.reached opened.lock).2.1 = state.owner ∧
    (view.descriptors stop.reached, view.files stop.reached) =
      (state.census, ⟨stop.runs.files stop.reached, state.files.owners⟩) ∧
    (view.descriptors rebooted, view.files rebooted) = ((reboot.observed valid).reboot, (reboot.observed valid).retry) ∧
    (view.descriptors rebooted).slots = [] ∧
    (∀ path payload, checkpointSurvivorPath state.session.directory state.writer state.writer.target.pair.manifest path →
      reader.ReadsSurvivor path payload → ∃ read : reader.opening.reads.reads.ObservesFile path payload,
        names stop.reached path = some read.object ∧ names rebooted path = some read.object ∧ bytes rebooted read.object = payload) ∧
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
  obtain ⟨_, history, pending⟩ := current.current.ready.readPrefix.refines
  let crash := reboot.observed valid
  obtain ⟨_, installed, reached⟩ := crash.restartsAt valid history pending current.current.ready.readPrefix.readsBounded
    plan.layout plan.target plan.keeper plan.descriptors plan.offsets plan.prepared plan.selected reader
  let next : NativeReadPosition current.current.history current.current.submissions :=
    ⟨reader.run, installed, installed, current.current.ready.reads, reached.1⟩
  obtain ⟨cacheOpen, makeCache, handle, start, cacheAction, cacheSource, ran, nextPosition, lock, cacheRefs,
    cacheDir, contents, get, set, compare, pins, files, census, cache⟩ :=
    raw.installsAligned valid history plan.target plan.keeper plan.descriptors plan.offsets plan.prepared next rfl reached
      remove write rename bootstrap assemble constructs effects ptrEq
  obtain ⟨source, phase, issued, stoppedLock, stoppedFiles⟩ := stopped.reached
  refine ⟨source, phase, issued, stopped.stopsGroup, stoppedLock, stoppedFiles,
    Prod.ext raw.admission.raw.entryCensus raw.admission.raw.entryFiles, ?_, ?_,
    next, cacheOpen, makeCache, handle, start, cacheAction, cacheSource, reached, ran, nextPosition, lock, cacheRefs,
    cacheDir, contents, get, set, compare, pins, files, census, cache⟩
  · rw [raw.admission.raw.entryCensus]
    rfl
  · intro path payload isSelected observed
    obtain ⟨read, bound, contents⟩ := raw.admission.reboot.readsSurvivingFile isSelected observed
    have protectedPath : state.crashPath path := .inr (.inr isSelected)
    have atStop := raw.admission.reboot.liveNames path protectedPath
    have survived := crash.settled crash.names crash.chosen path protectedPath
    have atRestart := raw.admission.reboot.survivorNames path protectedPath
    exact ⟨read, (atStop.trans (survived.symm.trans atRestart.symm)).trans bound, bound, contents⟩

end
end Alvoki.Storage.DiskSession
