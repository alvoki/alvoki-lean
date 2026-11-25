import Alvoki.Storage.Disk.NativeQuietPowerLossTableOpen
import Alvoki.Storage.Disk.NativeObsoleteRunUnlinkPowerLoss

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair

variable {heap stream : Type} {opened : NativeOpenedHandle heap} {current : NativeOpenedPosition opened}
  {held : List UInt64} {cut : NativeObsoleteRunUnlinkCut current.current.ready.state} {stop : NativeObsoleteRunUnlinkStop cut}
  {physical : OpenObsoleteRunUnlinkObservation current held cut stop}
  {stoppedHeap rebooted : heap} {input : FilePath}
  {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
  {init : OpenSyncCacheCallbacks heap} {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}

/-- The original raw collector stops inside one unlink. The observed
reboot starts at that same heap and uses one allowed run map and one
chronological aligned reader for both the replay and the public table. -/
theorem NativeOpenedPosition.opensAfterStoppedObsoleteRunUnlink
    (stopped : physical.Reached stoppedHeap)
    (crash : NativeObsoleteRunUnlinkCrash cut)
    {layout : CanonicalKeeperLayout crash.observed.retry.image current.current.ready.state.writer.history}
    (target : layout.target = current.current.ready.state.writer.target)
    (keeper : layout.keeper = current.current.ready.state.writer.wal.active)
    (descriptors : layout.sealed ++ [layout.keeper] =
      current.current.ready.state.writer.wal.readDescriptors layout.range.watermark)
    (offsets : selectWalSegmentReads (current.current.ready.state.writer.wal.segments.map WalSegment.first)
      layout.range.watermark = some (layout.first,
        (current.current.ready.state.writer.wal.readDescriptors layout.range.watermark).map WalSegment.first))
    (prepared : Prepared crash.observed.retry.image layout.target layout.plan)
    {selected : SelectedIntegrityCheckpoint crash.runs
      crash.observed.retry.image.directory.active.manifest current.current.ready.state.writer.checkpoint}
    {reader : NativeReadyRestartReads crash.observed input layout selected}
    (raw : RawQuietRestartEffects reader view calls init names bytes stoppedHeap rebooted phaseIdentity tokenIdentity
      allocatePhase allocateToken stream)
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
    (∀ sync, physical.run sync = .error cut.path stoppedHeap) ∧
    view.descriptors stoppedHeap = physical.view.descriptors stoppedHeap ∧
    (∀ path, (cut.survivor crash.runs).crashPath path →
      names stoppedHeap path =
        (cut.bindings (cut.reachedCensus, cut.reached) path).map cut.plan.lifetime.namespaceView.modelObject) ∧
    (∀ path payload, checkpointSurvivorPath state.session.directory state.writer state.writer.target.pair.manifest path →
      reader.ReadsSurvivor path payload →
      ∃ read : reader.opening.reads.reads.ObservesFile path payload,
        names stoppedHeap path = some read.object ∧ names rebooted path = some read.object ∧
        bytes rebooted read.object = payload) ∧
    (view.descriptors rebooted, view.files rebooted) = (crash.observed.reboot, crash.observed.retry) ∧
    (view.descriptors rebooted).slots = [] ∧
    ∃ (next : NativeReadPosition current.current.history current.current.submissions)
      (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
      (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      NativeObsoleteRunUnlinkCrashReopen current.current.ready next stop crash input ∧ reader.run = next.opened ∧
      NativeExecutionStep current.current (.interruptedRunUnlinkRecovered held input) start.current ∧
      DiskTable.OpenSyncFiles.IsOpenAction state.session.directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk state.session.directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
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
  obtain ⟨valid, history, pending⟩ := current.current.ready.readPrefix.refines
  have survivorValid := cut.survivorValid valid crash.survived
  obtain ⟨lost, returned, reached⟩ := crash.observed.restartsAt survivorValid history pending
    current.current.ready.readPrefix.readsBounded layout target keeper descriptors offsets prepared selected reader
  let next : NativeReadPosition current.current.history current.current.submissions :=
    ⟨reader.run, returned, returned, current.current.ready.reads, reached.1⟩
  have reopened := NativeObsoleteRunUnlinkCrashReopen.fromReader current.current.ready stop crash reader reached lost
  obtain ⟨cacheOpen, makeCache, handle, start, cacheAction, cacheSource, ran, currentEq, lock, references, cacheDirectory,
    contents, getEq, setEq, compareEq, pins, sameFiles, sameCensus, sameCache⟩ :=
    raw.installsAligned survivorValid history target keeper descriptors offsets prepared next rfl reached
      remove write rename bootstrap assemble constructs effects ptrEq
  have sameCutCensus := (congrArg Prod.fst raw.admission.reboot.previous).trans (congrArg Prod.fst stopped.files).symm
  refine ⟨stopped.stopped, sameCutCensus, ?_, ?_, Prod.ext raw.admission.raw.entryCensus raw.admission.raw.entryFiles, ?_,
    next, cacheOpen, makeCache, handle, start, reopened, rfl, ?_, cacheAction, cacheSource, ran, currentEq, lock, references,
    cacheDirectory, contents, getEq, setEq, compareEq, pins, sameFiles, sameCensus, sameCache⟩
  · exact fun path selected => (raw.admission.reboot.liveNames path selected).trans (crash.reachedBindings path selected)
  · intro path payload selected observed
    obtain ⟨read, named, actual⟩ := raw.admission.reboot.readsSurvivingFile selected observed
    have stable : (cut.survivor crash.runs).crashPath path := .inr (.inr selected)
    have sameName := (raw.admission.reboot.liveNames path stable).trans
      ((crash.observed.settled _ crash.observed.chosen _ stable).symm.trans
        (raw.admission.reboot.survivorNames path stable).symm)
    exact ⟨read, sameName.trans named, named, actual⟩
  · rw [raw.admission.raw.entryCensus]
    rfl
  · rw [currentEq, ← stopped.holds]
    exact .recoverInterruptedRunUnlink current.current stop crash next reopened

end Alvoki.Storage.DiskSession
