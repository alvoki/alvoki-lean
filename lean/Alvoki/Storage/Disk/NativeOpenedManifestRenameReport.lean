import Alvoki.Storage.Disk.NativeCheckpointManifestRenameTableOpen

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair CheckpointPublication

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- A returned manifest rename failure at the current opened phase cell,
followed by a reported reboot and one aligned reader of its survivor. -/
structure NativeOpenedManifestRenameReport (current : NativeOpenedPosition opened) (input : FilePath)
    (view : OpenCloseHeapView heap FileImage) (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray) where
  fileModel : Type
  cut : CheckpointPowerCut current.current.ready.state.session.directory current.current.ready.state.writer
  checkpoint : NativeCheckpointManifestRenameError (image := fileModel) current.current.ready.state cut
  cause : IO.Error
  failedHeap : heap
  failedFiles : CensusDirectoryCache × fileModel
  failed : runCheckpointOnOpenPhase checkpoint.synced.settled.runs.perform opened.phase opened.get opened.set
    (current.reached, checkpoint.synced.settled.runs.entry.image) = .error cause (failedHeap, failedFiles)
  crash : NativeCheckpointManifestRenameCrash checkpoint
  plan : crash.Plan
  reader : NativeCheckpointManifestRenameReads crash input plan
  rebooted : heap
  calls : RawOpenAdmissionCallbacks heap
  init : OpenSyncCacheCallbacks heap
  stream : Type
  phaseIdentity : IO.Ref (Phase Installed) → Nat
  tokenIdentity : IO.Ref Unit → Nat
  allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))
  allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)
  observed : RawManifestRenameReopenEffects reader view calls init names bytes failedHeap rebooted
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

/-- This action records the original diagnostic and the manifest binding
in the reported survivor used by the next actual open. -/
def NativeOpenedManifestRenameReport.event (seen : NativeOpenedManifestRenameReport current input view names bytes) :
    NativeExecutionEvent :=
  .checkpointManifestRenameCrashRecovered input seen.cause seen.crash.pair.manifest

/-- The reached position belongs to the reopened raw table and to the
same recovered session in the common trace. The selected evidence
retains either manifest outcome and its watermark bound. -/
structure NativeOpenedManifestRenameReport.Returned (seen : NativeOpenedManifestRenameReport current input view names bytes)
    {handle : NativeOpenedHandle heap} (start : NativeOpenedPosition handle) : Prop where
  sourceCheckpoint : opened.table.UsesOpenCheckpointSchedule current.current.ready.state.session.directory
    opened.files opened.phase
  cause : seen.cause = seen.checkpoint.cause
  failedFiles : seen.failedFiles = (current.current.ready.state.cache, seen.checkpoint.after)
  poisoned : view.phase seen.failedHeap opened.phase = some .poisoned
  failedProjection : (view.descriptors seen.failedHeap, view.files seen.failedHeap) =
    (seen.checkpoint.synced.settled.runs.descriptors seen.failedFiles.2,
      ⟨seen.checkpoint.synced.settled.runs.files seen.failedFiles.2, current.current.ready.state.files.owners⟩)
  rebootProjection : (view.descriptors seen.rebooted, view.files seen.rebooted) = (seen.crash.reboot, seen.crash.retry)
  emptyCensus : (view.descriptors seen.rebooted).slots = []
  lockObject : names seen.rebooted (current.current.ready.state.session.directory.file .lock) =
    some ((view.handle seen.observed.raw.afterFlock seen.observed.raw.lock).1.inode
      (view.handle seen.observed.raw.afterFlock seen.observed.raw.lock).2.1.description)
  directoryObject : names seen.rebooted current.current.ready.state.session.directory.path =
    some ((view.handle seen.observed.seed.afterPending seen.observed.seed.handle).1.inode
      (view.handle seen.observed.seed.afterPending seen.observed.seed.handle).2.1.description)
  selected : seen.reader.SelectedReads
  survivorBytes : ∀ path payload, checkpointSurvivorPath current.current.ready.state.session.directory
    current.current.ready.state.writer seen.crash.pair.manifest path →
      seen.reader.ReadsSurvivor path payload → ∃ read : seen.reader.opening.reads.reads.ObservesFile path payload,
        names seen.rebooted path = some read.object ∧ bytes seen.rebooted read.object = payload
  recovery : ∃ next : NativeReadPosition current.current.history current.current.submissions,
    NativeCheckpointManifestRenameReopened current.current.ready seen.crash input next ∧
    seen.reader.run = next.opened ∧ next.opened = .ok next.state.session (next.state.census, next.state.files) ∧
    start.current = ⟨current.current.history, current.current.submissions, next⟩
  sourceOpen : ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles),
    let directory := current.current.ready.state.session.directory
    DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
    cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
      (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
      (fun value => liftM (IO.mkRef value)) makeCache ∧
    seen.observed.toRawAlignedCheckpointReopenEffects.openTable seen.remove seen.write seen.rename
      seen.bootstrap seen.assemble makeCache =
      .ok handle.table start.reached
  common : NativeExecutionStep current.current seen.event start.current
  watermark : current.current.ready.state.writer.target.range.watermark ≤ start.current.ready.state.writer.target.range.watermark
  lock : handle.lock = seen.observed.raw.lock
  cache : handle.files.UsesCacheReferences seen.observed.seed.activeRef seen.observed.seed.pendingRef
    seen.observed.seed.directoryRef
  cacheDirectory : handle.files.AtDirectory current.current.ready.state.session.directory.path
  contents : handle.contents = view.phase
  get : handle.get = opened.get
  set : handle.set = opened.set
  ptrEq : handle.ptrEq = opened.ptrEq
  token : seen.tokenIdentity handle.token = start.current.ready.state.session.sessionRef
  unpinned : start.pins = []
  files : view.files start.reached = start.current.ready.state.files
  census : view.descriptors start.reached = start.current.ready.state.census
  cached : view.cacheAt start.reached seen.observed.seed.directoryRef seen.observed.seed.activeRef
    seen.observed.seed.pendingRef = start.current.ready.state.cache

theorem NativeOpenedManifestRenameReport.reaches (seen : NativeOpenedManifestRenameReport current input view names bytes) :
    ∃ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle), seen.Returned start := by
  obtain ⟨source, cause, failedFiles, poisoned, failedProjection, rebootProjection, emptyCensus, lockObject, directoryObject,
    selected, surviving, next, cacheOpen, makeCache, handle, start, cacheAction, cacheSource, reopened, reader, nextReturned,
    common, watermark, rawOpen, reached, lock, cache, directory, contents, get, set, compare, token, pins, files, census, cached⟩ :=
    current.opensAfterManifestRenameError seen.observed seen.failed seen.samePhase seen.remove seen.write seen.rename
      seen.bootstrap seen.assemble seen.constructs
  refine ⟨handle, start, source, cause, failedFiles, poisoned, failedProjection, rebootProjection, emptyCensus,
    lockObject, directoryObject, selected, surviving,
    ⟨next, reopened, reader, nextReturned, reached⟩, ⟨cacheOpen, makeCache, cacheAction, cacheSource, rawOpen⟩,
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
