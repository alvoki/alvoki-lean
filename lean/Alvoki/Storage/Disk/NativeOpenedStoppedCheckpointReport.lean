import Alvoki.Storage.Disk.NativeStoppedCheckpointTableOpen

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair CheckpointPublication

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- One checkpoint is interrupted at its issued final directory sync.
The same reported stop and its selected healthy aligned reboot supply
the physical observations for the next raw table. -/
structure NativeOpenedStoppedCheckpointReport (current : NativeOpenedPosition opened) (input : FilePath)
    (view : OpenCloseHeapView heap FileImage) (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray) where
  observed : NativePendingCheckpointCrashObservation current.current.ready.state input
  rebooted : heap
  calls : RawOpenAdmissionCallbacks heap
  init : OpenSyncCacheCallbacks heap
  stream : Type
  phaseIdentity : IO.Ref (Phase Installed) → Nat
  tokenIdentity : IO.Ref Unit → Nat
  allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))
  allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)
  physical : RawStoppedCheckpointReopenEffects observed view calls init names bytes rebooted
    phaseIdentity tokenIdentity allocatePhase allocateToken stream
  samePhase : view.phase = opened.contents
  remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)
  write : FilePath → ByteArray → EStateM IO.Error heap Unit
  rename : FilePath → FilePath → EStateM IO.Error heap Unit
  bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened
  assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
    IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable
  constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files)

variable {current : NativeOpenedPosition opened} {input : FilePath} {view : OpenCloseHeapView heap FileImage}
  {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}

/-- Record the interruption and the manifest selected at the reboot. -/
def NativeOpenedStoppedCheckpointReport.event (seen : NativeOpenedStoppedCheckpointReport current input view names bytes) :
    NativeExecutionEvent :=
  .interruptedCheckpointRecovered input seen.observed.crash.pair.manifest

/-- The next ready position comes from the exact raw return after the
interruption. Its report retains the outer stop and the selected reader
alongside the canonical cache initializer and recovered table. -/
structure NativeOpenedStoppedCheckpointReport.Returned (seen : NativeOpenedStoppedCheckpointReport current input view names bytes)
    {handle : NativeOpenedHandle heap} (start : NativeOpenedPosition handle) : Prop where
  sourceCheckpoint : opened.table.UsesOpenCheckpointSchedule current.current.ready.state.session.directory
    opened.files opened.phase
  interrupted :
    let state := current.current.ready.state
    ∃ poisoned, view.phase poisoned opened.phase = some .poisoned ∧
      seen.observed.stop.onOpenPhase opened (current.reached, seen.observed.stop.barrier.entry.image) =
        .error state.session.directory.path (poisoned, state.cache, seen.observed.stop.reached)
  rebootProjection : (view.descriptors seen.rebooted, view.files seen.rebooted) =
    (seen.observed.crash.reboot, seen.observed.crash.retry)
  emptyCensus : (view.descriptors seen.rebooted).slots = []
  lockObject : names seen.rebooted (current.current.ready.state.session.directory.file .lock) =
    some ((view.handle seen.physical.raw.afterFlock seen.physical.raw.lock).1.inode
      (view.handle seen.physical.raw.afterFlock seen.physical.raw.lock).2.1.description)
  directoryObject : names seen.rebooted current.current.ready.state.session.directory.path =
    some ((view.handle seen.physical.seed.afterPending seen.physical.seed.handle).1.inode
      (view.handle seen.physical.seed.afterPending seen.physical.seed.handle).2.1.description)
  selected : seen.observed.reopen.SelectedReads
  survivorBytes : ∀ path payload, checkpointSurvivorPath current.current.ready.state.session.directory
    current.current.ready.state.writer seen.observed.crash.pair.manifest path →
      seen.observed.reopen.ReadsSurvivor path payload → ∃ read : seen.observed.reopen.opening.reads.reads.ObservesFile path payload,
        names seen.rebooted path = some read.object ∧ bytes seen.rebooted read.object = payload
  recovery : ∃ next : NativeReadPosition current.current.history current.current.submissions,
    NativePendingCheckpointReopened current.current.ready seen.observed next ∧
    seen.observed.reopen.run = next.opened ∧ next.opened = .ok next.state.session (next.state.census, next.state.files) ∧
    start.current = ⟨current.current.history, current.current.submissions, next⟩
  sourceOpen : ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles),
    let directory := current.current.ready.state.session.directory
    DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
    cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
      (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
      (fun value => liftM (IO.mkRef value)) makeCache ∧
    seen.physical.toRawAlignedCheckpointReopenEffects.openTable seen.remove seen.write seen.rename
      seen.bootstrap seen.assemble makeCache = .ok handle.table start.reached
  common : NativeExecutionStep current.current seen.event start.current
  watermark : current.current.ready.state.writer.target.range.watermark ≤ start.current.ready.state.writer.target.range.watermark
  lock : handle.lock = seen.physical.raw.lock
  cache : handle.files.UsesCacheReferences seen.physical.seed.activeRef seen.physical.seed.pendingRef
    seen.physical.seed.directoryRef
  cacheDirectory : handle.files.AtDirectory current.current.ready.state.session.directory.path
  contents : handle.contents = view.phase
  get : handle.get = opened.get
  set : handle.set = opened.set
  ptrEq : handle.ptrEq = opened.ptrEq
  token : seen.tokenIdentity handle.token = start.current.ready.state.session.sessionRef
  unpinned : start.pins = []
  files : view.files start.reached = start.current.ready.state.files
  census : view.descriptors start.reached = start.current.ready.state.census
  cached : view.cacheAt start.reached seen.physical.seed.directoryRef seen.physical.seed.activeRef
    seen.physical.seed.pendingRef = start.current.ready.state.cache

/-- Use the existing exact raw open to reach the next position of the
session trace. The same common event carries the interrupted checkpoint. -/
theorem NativeOpenedStoppedCheckpointReport.reaches (seen : NativeOpenedStoppedCheckpointReport current input view names bytes) :
    ∃ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle), seen.Returned start := by
  obtain ⟨source, interrupted, rebootProjection, emptyCensus, lockObject, directoryObject,
    selected, surviving, next, cacheOpen, makeCache, handle, start, cacheAction, cacheSource, reopened, reader, nextReturned,
    common, watermark, rawOpen, reached, lock, cache, directory, contents, get, set, compare, token, pins, files, census, cached⟩ :=
    current.opensAfterStoppedCheckpoint seen.physical seen.samePhase seen.remove seen.write seen.rename
      seen.bootstrap seen.assemble seen.constructs
  refine ⟨handle, start, source, interrupted, rebootProjection, emptyCensus, lockObject, directoryObject,
    selected, surviving, ⟨next, reopened, reader, nextReturned, reached⟩, ⟨cacheOpen, makeCache, cacheAction, cacheSource, rawOpen⟩,
    common, ?_, lock, cache, directory, contents, get, set, compare, ?_, pins, ?_, ?_, ?_⟩
  · rw [reached]
    exact watermark
  · rw [reached]
    exact token
  · rw [reached]
    exact files
  · rw [reached]
    exact census
  · rw [reached]
    exact cached

end Alvoki.Storage.DiskSession
