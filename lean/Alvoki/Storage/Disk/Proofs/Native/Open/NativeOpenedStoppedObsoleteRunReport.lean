import Alvoki.Storage.Disk.Proofs.Native.Open.NativeStoppedObsoleteRunTableOpen

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- One prescribed collector stop and its reboot are observed at the
same reached heap. The aligned reader uses that exact reboot. -/
structure NativeOpenedStoppedObsoleteRunReport (current : NativeOpenedPosition opened)
    (held : List UInt64) (input : FilePath) (view : OpenCloseHeapView heap FileImage)
    (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray) where
  cut : NativeObsoleteRunUnlinkCut current.current.ready.state
  stop : NativeObsoleteRunUnlinkStop cut
  physical : OpenObsoleteRunUnlinkObservation current held cut stop
  stoppedHeap : heap
  stopped : physical.Reached stoppedHeap
  crash : NativeObsoleteRunUnlinkCrash cut
  layout : CanonicalKeeperLayout crash.observed.retry.image current.current.ready.state.writer.history
  target : layout.target = current.current.ready.state.writer.target
  keeper : layout.keeper = current.current.ready.state.writer.wal.active
  descriptors : layout.sealed ++ [layout.keeper] =
    current.current.ready.state.writer.wal.readDescriptors layout.range.watermark
  offsets : selectWalSegmentReads (current.current.ready.state.writer.wal.segments.map WalSegment.first)
    layout.range.watermark = some (layout.first,
      (current.current.ready.state.writer.wal.readDescriptors layout.range.watermark).map WalSegment.first)
  prepared : Prepared crash.observed.retry.image layout.target layout.plan
  selected : SelectedIntegrityCheckpoint crash.runs crash.observed.retry.image.directory.active.manifest
    current.current.ready.state.writer.checkpoint
  reader : NativeReadyRestartReads crash.observed input layout selected
  rebooted : heap
  stream : Type
  calls : RawOpenAdmissionCallbacks heap
  init : OpenSyncCacheCallbacks heap
  phaseIdentity : IO.Ref (Phase Installed) → Nat
  tokenIdentity : IO.Ref Unit → Nat
  allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))
  allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)
  observed : RawQuietRestartEffects reader view calls init names bytes stoppedHeap rebooted
    phaseIdentity tokenIdentity allocatePhase allocateToken stream
  remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)
  write : FilePath → ByteArray → EStateM IO.Error heap Unit
  rename : FilePath → FilePath → EStateM IO.Error heap Unit
  bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened
  assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
    IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable
  constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files)
  samePhase : view.phase = opened.contents

variable {current : NativeOpenedPosition opened} {held : List UInt64} {input : FilePath}
  {view : OpenCloseHeapView heap FileImage} {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}

/-- The interrupted call has no ordinary result. One reader and the
actual raw open supply the next position and its common event. -/
structure NativeOpenedStoppedObsoleteRunReport.Returned
    (seen : NativeOpenedStoppedObsoleteRunReport current held input view names bytes)
    {handle : NativeOpenedHandle heap} (start : NativeOpenedPosition handle) : Prop where
  stopped : ∀ sync, seen.physical.run sync = .error seen.cut.path seen.stoppedHeap
  reboot : (view.descriptors seen.rebooted, view.files seen.rebooted) =
    (seen.crash.observed.reboot, seen.crash.observed.retry)
  emptyCensus : (view.descriptors seen.rebooted).slots = []
  selectedFiles : ∀ path payload,
    checkpointSurvivorPath current.current.ready.state.session.directory current.current.ready.state.writer
      current.current.ready.state.writer.target.pair.manifest path →
    seen.reader.ReadsSurvivor path payload →
    ∃ read : seen.reader.opening.reads.reads.ObservesFile path payload,
      names seen.stoppedHeap path = some read.object ∧ names seen.rebooted path = some read.object ∧
      bytes seen.rebooted read.object = payload
  reader : seen.reader.run = start.current.ready.opened
  recovery : ∃ next : NativeReadPosition current.current.history current.current.submissions,
    NativeObsoleteRunUnlinkCrashReopen current.current.ready next seen.stop seen.crash input ∧
    start.current = ⟨current.current.history, current.current.submissions, next⟩
  sourceOpen : ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles),
    let directory := current.current.ready.state.session.directory
    DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
    cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
      (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
      (fun value => liftM (IO.mkRef value)) makeCache ∧
    seen.observed.openTable seen.remove seen.write seen.rename seen.bootstrap seen.assemble makeCache =
      .ok handle.table start.reached
  common : NativeExecutionStep current.current (.interruptedRunUnlinkRecovered held input) start.current
  lock : handle.lock = seen.observed.admission.raw.lock
  cache : handle.files.UsesCacheReferences seen.observed.admission.seed.activeRef seen.observed.admission.seed.pendingRef
    seen.observed.admission.seed.directoryRef
  cacheDirectory : handle.files.AtDirectory current.current.ready.state.session.directory.path
  contents : handle.contents = view.phase
  get : handle.get = opened.get
  set : handle.set = opened.set
  ptrEq : handle.ptrEq = opened.ptrEq
  unpinned : start.pins = []
  files : view.files start.reached = start.current.ready.state.files
  census : view.descriptors start.reached = start.current.ready.state.census
  cached : view.cacheAt start.reached seen.observed.admission.seed.directoryRef
    seen.observed.admission.seed.activeRef seen.observed.admission.seed.pendingRef = start.current.ready.state.cache

theorem NativeOpenedStoppedObsoleteRunReport.reaches
    (seen : NativeOpenedStoppedObsoleteRunReport current held input view names bytes) :
    ∃ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle), seen.Returned start := by
  have effects : OpenPhaseCellEffects view.phase opened.get opened.set :=
    seen.samePhase.symm ▸ opened.phaseEffects
  obtain ⟨stopped, _, _, selectedFiles, reboot, empty, next, cacheOpen, makeCache, handle, start,
    recovered, reader, common, cacheAction, cacheSource, returned, reached, lock, cache, directory,
    contents, get, set, compare, pins, files, census, cached⟩ :=
    NativeOpenedPosition.opensAfterStoppedObsoleteRunUnlink seen.stopped seen.crash seen.target seen.keeper
      seen.descriptors seen.offsets seen.prepared seen.observed seen.remove seen.write seen.rename seen.bootstrap
      seen.assemble seen.constructs effects opened.ptrEq
  refine ⟨handle, start, stopped, reboot, empty, selectedFiles, ?_, ⟨next, recovered, reached⟩,
    ⟨cacheOpen, makeCache, cacheAction, cacheSource, returned⟩, common, lock, cache, directory, contents, get, set,
    compare, pins, ?_, ?_, ?_⟩
  · rwa [reached]
  · rwa [reached]
  · rwa [reached]
  · rwa [reached]

end Alvoki.Storage.DiskSession
