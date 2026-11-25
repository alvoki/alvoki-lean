import Alvoki.Storage.Disk.NativeQuietPowerLossRaw
import Alvoki.Storage.Disk.NativeMarkedTableOpen

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair CheckpointPublication

variable {heap stream : Type} {state : NativeReadyState} {input : FilePath}
  {crash : NativeReadyQuietCrash state}
  {layout : CanonicalKeeperLayout crash.retry.image state.writer.history}
  {selected : SelectedIntegrityCheckpoint state.writer.published.durable
    crash.retry.image.directory.active.manifest state.writer.checkpoint}
  {reader : NativeReadyRestartReads crash input layout selected}
  {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
  {init : OpenSyncCacheCallbacks heap} {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}
  {before after : heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}

/-- The report that selects the reboot files is also the input to the
raw marked worker. Its existing read and release chronology indexes
each primitive report through the final allocation. -/
structure RawQuietRestartEffects (reader : NativeReadyRestartReads crash input layout selected)
    (view : OpenCloseHeapView heap FileImage) (calls : RawOpenAdmissionCallbacks heap)
    (init : OpenSyncCacheCallbacks heap) (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray)
    (before after : heap)
    (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat)
    (allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed)))
    (allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)) (stream : Type)
    (beforeCensus : DescriptorInventory := state.census) where
  admission : RawQuietRestartAdmission reader view calls init names bytes before after beforeCensus
  fileCalls : MarkedTemporaryReadCalls heap
  directoryCalls : MarkedDirectoryReadCalls heap stream
  slotOf : heap → stream → DescriptorSlot
  callbacks : AlignedKeeperCacheCallbacks heap
  checkpoint : NativeMarkedCheckpointReadHeap admission.seed reader.capturedChronology fileCalls
  listing : MarkedDirectoryReadReport checkpoint directoryCalls slotOf
  extents : MarkedWalExtentReports checkpoint listing
  beforeKeeper : heap
  seals : MarkedSealReadChain admission.seed fileCalls reader.capturedChronology.seals listing.reached beforeKeeper
  keeper : AlignedKeeperCacheReport reader.opening.finish view init admission.raw.afterFlock admission.seed
    (callbacks.withFileReads fileCalls) beforeKeeper
  sameLookup : fileCalls.stat = calls.lookup
  flat : optionalMetadataWith (fileCalls.stat (state.session.directory.file .wal)) admission.seed.afterPending =
    .ok none admission.seed.afterPending
  marker : IO.FS.Metadata
  marked : optionalMetadataWith (fileCalls.stat (state.session.directory.file .walBoundary)) admission.seed.afterPending =
    .ok (some marker) admission.seed.afterPending
  allocations : ∀ opened,
    reader.opening.finish.recoverFromCensus reader.capturedChronology.metadataRelease reader.capturedChronology.runs.released
      reader.capturedChronology.sealRelease state.session.directory reader.opening.admission.cache
      (reader.opening.admission.reached, reader.opening.admission.held) =
      .ok opened (view.descriptors keeper.reached, view.files keeper.reached) →
    ∃ allocation : OpenReferenceAllocations allocatePhase allocateToken view.phase opened.installed keeper.reached,
      phaseIdentity allocation.phase = reader.opening.callbacks.nextRef ∧
      tokenIdentity allocation.token = reader.opening.callbacks.nextRef + 1 ∧
      CacheAllocationFrame view admission.seed.directoryRef admission.seed.activeRef admission.seed.pendingRef
        keeper.reached allocation.afterPhase ∧
      CacheAllocationFrame view admission.seed.directoryRef admission.seed.activeRef admission.seed.pendingRef
        allocation.afterPhase allocation.afterToken

/-- The source open schedule, interpreted from the observed reboot heap
with the actual admission and held worker callbacks. -/
def RawQuietRestartEffects.openTable
    {beforeCensus : DescriptorInventory}
    (seen : RawQuietRestartEffects reader view calls init names bytes before after phaseIdentity tokenIdentity
      allocatePhase allocateToken stream beforeCensus)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
      IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles) : EStateM.Result IO.Error heap DiskTable :=
  let seed := seen.admission.seed
  calls.runOpen input init makeCache (fun resolved lock cache => do
    let opened ← calls.recoverMarkedWithCacheRefs seen.fileCalls seen.directoryCalls seen.callbacks seed.directoryRef
      seed.activeRef seed.pendingRef remove write rename bootstrap resolved cache
    installReady opened.installed allocatePhase allocateToken
      (fun phase token => pure (assemble resolved lock cache phase token))) after

/-- Project one quiet reboot reader into the aligned marked proof. This
keeps its exact admission, captured reads and repair worker. -/
def NativeReadyRestartReads.markedReport (seen : NativeReadyRestartReads crash input layout selected)
    (retained : state.writer.RetainedReady state.session.directory state.session.descriptor)
    (target : layout.target = state.writer.target) (keeper : layout.keeper = state.writer.wal.active)
    (descriptors : layout.sealed ++ [layout.keeper] = state.writer.wal.readDescriptors layout.range.watermark)
    (offsets : selectWalSegmentReads (state.writer.wal.segments.map WalSegment.first) layout.range.watermark =
      some (layout.first, (state.writer.wal.readDescriptors layout.range.watermark).map WalSegment.first))
    (prepared : Prepared crash.retry.image layout.target layout.plan)
    (pending : PendingClientReplay log reads state.writer.history)
    (bounded : ∀ read ∈ reads, read.BoundedBy state.writer.history.length) :
    MarkedOpenSuccessReports input state.session.directory state.writer.history log reads where
  inventory := crash.reboot
  retry := crash.retry
  layout := layout
  published := state.writer.published
  checkpoint := state.writer.checkpoint
  selected := selected
  vacant := crash.vacant
  opening := ⟨seen.opening.admission, seen.opening.callbacks, seen.opening.reads, .aligned seen.opening.finish,
    seen.capturedChronology, seen.opening.marker, seen.opening.markerFound⟩
  prepared := prepared
  following := seen.opening.reads.walReads.selectedAfterWatermark offsets descriptors
  accepted := retained.resumed.accepted
  ordered := retained.resumed.ordered
  wal := state.writer.wal
  walLayout := retained.layout
  walValid := retained.valid
  spans := retained.spans
  active := retained.walPair.trans (congrArg Target.pair target).symm
  keeper := congrArg WalSegment.first keeper
  kept := retained.sealedFiles
  pending := pending
  bounded := bounded

section

variable {directory : DiskDirectory} {history modelHistory : List WAL.Write}
  {log : List DatabaseSubmissions} {recorded : List RecordedSnapshotRead}
  {report : MarkedOpenSuccessReports input directory modelHistory log recorded}
  {entry reached : heap} {seed : OpenSyncCacheAllocations report.opening.admission.opened view init entry}
  {lock : IO.FS.Handle} {lockIdentity : IO.FS.Handle → Nat}

/-- Compare the selected modeled session with the exact raw return
using the previous client history's refinement equality. -/
private theorem startsAtRebootedPosition
    (installed : MarkedHeapInstallation report view init entry seed lock lockIdentity phaseIdentity tokenIdentity
      allocatePhase allocateToken reached)
    (sameHistory : modelHistory = history) (next : NativeReadPosition history log)
    (sameReturn : report.opening.finish.run report.opening.chronology = next.opened)
    (returned : next.opened = .ok next.state.session (next.state.census, next.state.files))
    (cache : next.state.cache = report.opening.admission.cache)
    (owner : next.state.owner = report.opening.admission.owner)
    (slot : next.state.directorySlot = report.opening.admission.cached)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects view.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) :
    ∃ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      start.current = ⟨history, log, next⟩ ∧ handle.table = installed.table ∧
      handle.lock = lock ∧ handle.files = installed.files ∧
      handle.phase = installed.allocation.phase ∧ handle.token = installed.allocation.token ∧
      handle.contents = view.phase ∧ handle.get = get ∧ handle.set = set ∧ handle.ptrEq = ptrEq ∧
      start.reached = installed.allocation.afterToken ∧ start.pins = [] ∧
      view.files start.reached = next.state.files ∧ view.descriptors start.reached = next.state.census ∧
      view.cacheAt start.reached seed.directoryRef seed.activeRef seed.pendingRef = next.state.cache := by
  subst history
  obtain ⟨handle, start, table, _, sameLock, sameCache, phase, token, contents, getEq, setEq, compared,
    current, heap, pins, files, census, cached, _, _, _, _, _⟩ :=
    installed.startsAtReportedPosition next sameReturn returned cache owner slot effects ptrEq
  exact ⟨handle, start, current, table, sameLock, sameCache, phase, token, contents, getEq, setEq, compared, heap, pins, files,
    census, cached⟩

end

/-- Install the exact session of the one chosen chronological reader.
The same marked callbacks and cache allocation produce the returned
table used by the next public call. -/
theorem RawQuietRestartEffects.installsAligned
    {beforeCensus : DescriptorInventory}
    (seen : RawQuietRestartEffects reader view calls init names bytes before after phaseIdentity tokenIdentity
      allocatePhase allocateToken stream beforeCensus)
    (valid : state.Valid) (sameHistory : state.writer.history = history)
    (target : layout.target = state.writer.target) (keeper : layout.keeper = state.writer.wal.active)
    (descriptors : layout.sealed ++ [layout.keeper] = state.writer.wal.readDescriptors layout.range.watermark)
    (offsets : selectWalSegmentReads (state.writer.wal.segments.map WalSegment.first) layout.range.watermark =
      some (layout.first, (state.writer.wal.readDescriptors layout.range.watermark).map WalSegment.first))
    (prepared : Prepared crash.retry.image layout.target layout.plan)
    (next : NativeReadPosition history log)
    (sameReturn : reader.run = next.opened)
    (reached : reader.ReachedSession next.state history log next.reads)
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
    ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
      (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      DiskTable.OpenSyncFiles.IsOpenAction state.session.directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk state.session.directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      seen.openTable remove write rename bootstrap assemble makeCache = .ok handle.table start.reached ∧
      start.current = ⟨history, log, next⟩ ∧
      handle.lock = seen.admission.raw.lock ∧
      handle.files.UsesCacheReferences seen.admission.seed.activeRef seen.admission.seed.pendingRef
        seen.admission.seed.directoryRef ∧ handle.files.AtDirectory state.session.directory.path ∧
      handle.contents = view.phase ∧ handle.get = get ∧ handle.set = set ∧ handle.ptrEq = ptrEq ∧ start.pins = [] ∧
      view.files start.reached = next.state.files ∧ view.descriptors start.reached = next.state.census ∧
      view.cacheAt start.reached seen.admission.seed.directoryRef seen.admission.seed.activeRef
        seen.admission.seed.pendingRef = next.state.cache := by
  have pending : PendingClientReplay log next.reads state.writer.history :=
    sameHistory.symm ▸ next.readPrefix.refines.2.2
  have bounded : ∀ read ∈ next.reads, read.BoundedBy state.writer.history.length :=
    sameHistory.symm ▸ next.readPrefix.readsBounded
  let report := reader.markedReport valid.retained target keeper descriptors offsets prepared pending bounded
  obtain ⟨installed, cacheOpen, makeCache, cacheAction, cacheSource, ran⟩ :=
    report.opensAlignedFromAdmission seen.admission.raw seen.admission.seed reader.opening.finish rfl
      seen.checkpoint seen.listing seen.extents seen.seals seen.keeper seen.sameLookup seen.flat seen.marked
      remove write rename bootstrap assemble constructs seen.allocations
  obtain ⟨readyPrefix, _, owner, slot, cache, _⟩ := reached
  obtain ⟨handle, start, currentEq, rawTable, lock, files, _, _, contents, getEq, setEq, compareEq, reachedHeap, pins,
    sameFiles, sameCensus, sameCache⟩ :=
    startsAtRebootedPosition installed sameHistory next sameReturn (sameReturn.symm.trans readyPrefix.frames.1)
      cache owner slot effects ptrEq
  refine ⟨cacheOpen, makeCache, handle, start, cacheAction, cacheSource, ?_, currentEq, lock,
    files.symm ▸ installed.cacheReferences, files.symm ▸ installed.cacheDirectory, contents, getEq, setEq, compareEq,
    pins, sameFiles, sameCensus, sameCache⟩
  rw [rawTable, reachedHeap]
  exact ran

variable {opened : NativeOpenedHandle heap} {initial current : NativeOpenedPosition opened}

/-- Start a new raw opened-table trace after one settled power loss.
One selected reader supplies the exact physical survivor, the marked
worker, the returned table and the next common ready position. -/
theorem NativeOpenedTrace.restartsThenOpensAligned
    (prior : NativeOpenedTrace initial instructions events current)
    (crash : NativeReadyQuietCrash current.current.ready.state)
    {layout : CanonicalKeeperLayout crash.retry.image current.current.ready.state.writer.history}
    (target : layout.target = current.current.ready.state.writer.target)
    (keeper : layout.keeper = current.current.ready.state.writer.wal.active)
    (descriptors : layout.sealed ++ [layout.keeper] =
      current.current.ready.state.writer.wal.readDescriptors layout.range.watermark)
    (offsets : selectWalSegmentReads (current.current.ready.state.writer.wal.segments.map WalSegment.first)
      layout.range.watermark = some (layout.first,
        (current.current.ready.state.writer.wal.readDescriptors layout.range.watermark).map WalSegment.first))
    (prepared : Prepared crash.retry.image layout.target layout.plan)
    {selected : SelectedIntegrityCheckpoint current.current.ready.state.writer.published.durable
      crash.retry.image.directory.active.manifest current.current.ready.state.writer.checkpoint}
    {reader : NativeReadyRestartReads crash input layout selected}
    (seen : RawQuietRestartEffects reader view calls init names bytes current.reached after phaseIdentity tokenIdentity
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
    (view.descriptors after, view.files after) = (crash.reboot, crash.retry) ∧ (view.descriptors after).slots = [] ∧
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
      reader.run = next.opened ∧ next.opened = .ok next.state.session (next.state.census, next.state.files) ∧
      NativeReadRecoveryStep current.current.ready (.restart input) next ∧
      NativeExecutionTrace initial.current (events ++ [.readOrRestart (.restart input)]) start.current ∧
      seen.openTable remove write rename bootstrap assemble makeCache = .ok handle.table start.reached ∧
      start.current = ⟨current.current.history, current.current.submissions, next⟩ ∧
      handle.lock = seen.admission.raw.lock ∧
      handle.files.UsesCacheReferences seen.admission.seed.activeRef seen.admission.seed.pendingRef
        seen.admission.seed.directoryRef ∧ handle.files.AtDirectory state.session.directory.path ∧
      handle.contents = view.phase ∧ handle.get = get ∧ handle.set = set ∧ handle.ptrEq = ptrEq ∧ start.pins = [] ∧
      view.files start.reached = next.state.files ∧ view.descriptors start.reached = next.state.census ∧
      view.cacheAt start.reached seen.admission.seed.directoryRef seen.admission.seed.activeRef
        seen.admission.seed.pendingRef = next.state.cache := by
  intro state
  obtain ⟨valid, rows, priorReplay⟩ := current.current.ready.readPrefix.refines
  obtain ⟨lost, reached, restart⟩ := crash.restartsAt valid rows priorReplay current.current.ready.readPrefix.readsBounded
    layout target keeper descriptors offsets prepared selected reader
  have reachedSession := restart
  obtain ⟨readyPrefix, directory, owner, slot, cache, census, freshToken, freshPhase, lockInode, directoryInode, _,
    table, checkpoint, durable, _⟩ := restart
  let next : NativeReadPosition current.current.history current.current.submissions :=
    ⟨reader.run, reached, reached, current.current.ready.reads, readyPrefix⟩
  have step : NativeReadRecoveryStep current.current.ready (.restart input) next :=
    .restart current.current.ready crash lost layout selected reader reached readyPrefix owner slot cache census freshToken freshPhase
      ⟨directory, directoryInode, lockInode, table, checkpoint, durable⟩
  obtain ⟨cacheOpen, makeCache, handle, start, cacheAction, cacheSource, ran, currentEq, lock, references, cacheDirectory,
    contents, getEq, setEq, compareEq, pins, sameFiles, sameCensus, sameCache⟩ :=
    seen.installsAligned valid rows target keeper descriptors offsets prepared next rfl reachedSession
      remove write rename bootstrap assemble constructs effects ptrEq
  refine ⟨Prod.ext seen.admission.raw.entryCensus seen.admission.raw.entryFiles, ?_, next, cacheOpen, makeCache, handle, start,
    cacheAction, cacheSource, reachedSession, rfl, readyPrefix.frames.1, step, ?_, ran, currentEq, lock, references,
    cacheDirectory, contents, getEq, setEq, compareEq, pins, sameFiles, sameCensus, sameCache⟩
  · rw [seen.admission.raw.entryCensus]
    rfl
  · rw [currentEq]
    exact .step prior.common (.readOrRestart current.current step)

end Alvoki.Storage.DiskSession
