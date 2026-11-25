import Alvoki.Storage.Disk.NativeStoppedRunDirectoryTableOpen

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- The first checkpoint directory barrier stops in the original opened
call. The same reported reboot and one fixed aligned reader supply the
raw return used by the next session. -/
structure NativeOpenedStoppedRunDirectoryReport (current : NativeOpenedPosition opened) (input : FilePath)
    (view : OpenCloseHeapView heap FileImage) (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray) where
  cut : CheckpointPowerCut current.current.ready.state.session.directory current.current.ready.state.writer
  stop : NativeCheckpointRunDirectoryStop (image := heap) current.current.ready.state cut
  stopped : RawCheckpointRunDirectoryStop current stop view
  reboot : NativeCheckpointRunDirectoryReboot stop
  plan : reboot.Plan current.current.ready.readPrefix.refines.1
  reader : NativeReadyRestartReads (reboot.observed current.current.ready.readPrefix.refines.1) input plan.layout plan.selected
  rebooted : heap
  calls : RawOpenAdmissionCallbacks heap
  init : OpenSyncCacheCallbacks heap
  stream : Type
  phaseIdentity : IO.Ref (Phase Installed) → Nat
  tokenIdentity : IO.Ref Unit → Nat
  allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))
  allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)
  raw : RawQuietRestartEffects reader view calls init names bytes stop.reached rebooted phaseIdentity tokenIdentity
    allocatePhase allocateToken stream
  remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)
  write : FilePath → ByteArray → EStateM IO.Error heap Unit
  rename : FilePath → FilePath → EStateM IO.Error heap Unit
  bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened
  assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
    IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable
  constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files)

namespace NativeOpenedStoppedRunDirectoryReport

variable {current : NativeOpenedPosition opened} {input : FilePath} {view : OpenCloseHeapView heap FileImage}
  {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}
  (seen : NativeOpenedStoppedRunDirectoryReport current input view names bytes)

def event : NativeExecutionEvent :=
  .interruptedCheckpointRunDirectoryRecovered input seen.cut.tookEffect current.current.ready.state.writer.target.pair.manifest

structure Returned {handle : NativeOpenedHandle heap} (start : NativeOpenedPosition handle) : Prop where
  source : opened.table.UsesOpenCheckpointSchedule current.current.ready.state.session.directory opened.files opened.phase
  phase : view.phase seen.stop.reached opened.phase = some .poisoned
  interrupted : seen.stop.onOpenPhase opened (current.reached, seen.stop.runs.entry.image) =
    .error current.current.ready.state.session.directory.path
      (seen.stop.runs.atRun 0, current.current.ready.state.cache, seen.stop.reached)
  issued : ∀ pending setPending active openRead, seen.stopped.group pending setPending active openRead seen.stop.atIssue =
    .error current.current.ready.state.session.directory.path seen.stop.reached
  oldLock : (view.handle seen.stop.reached opened.lock).2.1 = current.current.ready.state.owner
  stoppedFiles : (view.descriptors seen.stop.reached, view.files seen.stop.reached) =
    (current.current.ready.state.census, ⟨seen.stop.runs.files seen.stop.reached, current.current.ready.state.files.owners⟩)
  rebootFiles : (view.descriptors seen.rebooted, view.files seen.rebooted) =
    ((seen.reboot.observed current.current.ready.readPrefix.refines.1).reboot,
      (seen.reboot.observed current.current.ready.readPrefix.refines.1).retry)
  emptyCensus : (view.descriptors seen.rebooted).slots = []
  selectedBytes : ∀ path payload, checkpointSurvivorPath current.current.ready.state.session.directory
      current.current.ready.state.writer current.current.ready.state.writer.target.pair.manifest path →
    seen.reader.ReadsSurvivor path payload → ∃ read : seen.reader.opening.reads.reads.ObservesFile path payload,
      names seen.stop.reached path = some read.object ∧ names seen.rebooted path = some read.object ∧ bytes seen.rebooted read.object = payload
  reopened : ∃ next : NativeReadPosition current.current.history current.current.submissions,
    start.current = ⟨current.current.history, current.current.submissions, next⟩ ∧
      NativeCheckpointRunDirectoryReopened current.current.ready seen.reboot seen.reader next
  rawOpen : ∃ (action : IO DiskTable.OpenSyncFiles)
    (make : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles),
    DiskTable.OpenSyncFiles.IsOpenAction current.current.ready.state.session.directory.path action ∧
    action = openSyncFilesWith (m := IO) (IO.FS.Handle.mk current.current.ready.state.session.directory.path .read)
      (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
      (fun value => liftM (IO.mkRef value)) make ∧
    seen.raw.openTable seen.remove seen.write seen.rename seen.bootstrap seen.assemble make = .ok handle.table start.reached
  common : NativeExecutionStep current.current seen.event start.current
  lock : handle.lock = seen.raw.admission.raw.lock
  cacheRefs : handle.files.UsesCacheReferences seen.raw.admission.seed.activeRef seen.raw.admission.seed.pendingRef
    seen.raw.admission.seed.directoryRef
  cachePath : handle.files.AtDirectory current.current.ready.state.session.directory.path
  contents : handle.contents = view.phase
  get : handle.get = opened.get
  set : handle.set = opened.set
  ptrEq : handle.ptrEq = opened.ptrEq
  pins : start.pins = []
  files : view.files start.reached = start.current.ready.state.files
  census : view.descriptors start.reached = start.current.ready.state.census
  cache : view.cacheAt start.reached seen.raw.admission.seed.directoryRef seen.raw.admission.seed.activeRef
    seen.raw.admission.seed.pendingRef = start.current.ready.state.cache

/-- Build the next position from the exact returned table and its proved
reader. The first barrier contributes one interruption and reopen event. -/
theorem reaches : ∃ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle), seen.Returned start := by
  let effects : OpenPhaseCellEffects view.phase opened.get opened.set := seen.stopped.samePhase.symm ▸ opened.phaseEffects
  obtain ⟨source, phase, interrupted, issued, oldLock, stoppedFiles, rebootFiles, emptyCensus, selectedBytes,
    next, cacheOpen, makeCache, handle, installed, cacheAction, cacheSource, reader, ran, position, lock, cacheRefs,
    cachePath, contents, get, set, ptrEq, pins, files, census, cache⟩ :=
    NativeOpenedPosition.opensAfterStoppedRunDirectory seen.stopped seen.reboot current.current.ready.readPrefix.refines.1
      seen.plan seen.raw seen.remove seen.write seen.rename seen.bootstrap seen.assemble seen.constructs effects opened.ptrEq
  let ready : NativeReadPosition current.current.history current.current.submissions :=
    ⟨seen.reader.run, next.state, next.state, current.current.ready.reads, reader.1⟩
  have sameState : installed.current.ready.state = next.state := by rw [position]
  let start : NativeOpenedPosition handle :=
    ⟨⟨current.current.history, current.current.submissions, ready⟩, installed.reached,
      sameState ▸ installed.directory, sameState ▸ installed.stored, installed.pins⟩
  have reopened : NativeCheckpointRunDirectoryReopened current.current.ready seen.reboot seen.reader ready :=
    ⟨current.current.ready.stopsAtCheckpointRunDirectory seen.stop, ⟨rfl, reader⟩, rfl⟩
  exact ⟨handle, start, source, phase, interrupted, issued, oldLock, stoppedFiles, rebootFiles, emptyCensus,
    selectedBytes, ⟨ready, rfl, reopened⟩, ⟨cacheOpen, makeCache, cacheAction, cacheSource, ran⟩,
    .recoverInterruptedCheckpointRunDirectory current.current seen.reboot seen.reader ready reopened,
    lock, cacheRefs, cachePath, contents, get, set, ptrEq, pins, files, census, cache⟩

end NativeOpenedStoppedRunDirectoryReport
end Alvoki.Storage.DiskSession
