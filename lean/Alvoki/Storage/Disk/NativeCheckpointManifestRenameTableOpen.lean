import Alvoki.Storage.Disk.NativeClassifiedCheckpointRenameError
import Alvoki.Storage.Disk.NativeMarkedTableOpen

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair CheckpointPublication

variable {heap stream image : Type} {state : NativeReadyState} {input : FilePath}
  {cut : CheckpointPowerCut state.session.directory state.writer}
  {report : NativeCheckpointManifestRenameError (image := image) state cut}
  {crash : NativeCheckpointManifestRenameCrash report} {plan : crash.Plan}
  {reader : NativeCheckpointManifestRenameReads crash input plan}
  {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
  {init : OpenSyncCacheCallbacks heap} {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}
  {reached rebooted : heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}

private def renameRebootPath (crash : NativeCheckpointManifestRenameCrash report) (path : FilePath) : Prop :=
  path = state.session.directory.path ∨ path = state.session.directory.file .lock ∨
    checkpointSurvivorPath state.session.directory state.writer crash.pair.manifest path

/-- The power-loss observation connects the returned rename's physical
projection and the reboot heap to the same selected namespace. -/
structure RawManifestRenameReboot (crash : NativeCheckpointManifestRenameCrash report)
    (view : OpenCloseHeapView heap FileImage) (names : heap → FilePath → Option Nat)
    (bytes : heap → Nat → ByteArray) (reached rebooted : heap) : Prop where
  returnedFiles : view.files reached = ⟨report.synced.settled.runs.files report.after, state.files.owners⟩
  returnedCensus : view.descriptors reached = report.synced.settled.runs.descriptors report.after
  priorNames : ∀ path, renameRebootPath crash path → names reached path = report.view.visible path
  survivorNames : ∀ path, renameRebootPath crash path → names rebooted path = crash.names path
  survivorBytes : ∀ path, checkpointSurvivorPath state.session.directory state.writer crash.pair.manifest path →
    ∀ inode, crash.names path = some inode →
      bytes rebooted inode ∈ (report.synced.settled.runs.inodes report.after).crashBytes inode

theorem RawManifestRenameReboot.readsSurvivingFile
    (entry : RawManifestRenameReboot crash view names bytes reached rebooted)
    {path : FilePath} {payload : ByteArray}
    (selectedPath : checkpointSurvivorPath state.session.directory state.writer crash.pair.manifest path)
    (read : reader.ReadsSurvivor path payload) :
    ∃ seen : reader.opening.reads.reads.ObservesFile path payload,
      names rebooted path = some seen.object ∧ bytes rebooted seen.object = payload := by
  obtain ⟨seen, bound, durable⟩ := read
  have contents := entry.survivorBytes path selectedPath seen.object bound
  rw [durable] at contents
  exact ⟨seen, (entry.survivorNames path (.inr (.inr selectedPath))).trans bound, List.mem_singleton.mp contents⟩

/-- Use the exact reported reader to index each callback from the reboot
heap through the marked keeper and its final table allocations. -/
structure RawManifestRenameReopenEffects (reader : NativeCheckpointManifestRenameReads crash input plan)
    (view : OpenCloseHeapView heap FileImage) (calls : RawOpenAdmissionCallbacks heap)
    (init : OpenSyncCacheCallbacks heap) (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray)
    (reached rebooted : heap)
    (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat)
    (allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed)))
    (allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)) (stream : Type) where
  reboot : RawManifestRenameReboot crash view names bytes reached rebooted
  raw : RawOpenAdmissionReport reader.opening.admission view calls rebooted
  seed : OpenSyncCacheAllocations reader.opening.admission.opened view init raw.afterFlock
  fileCalls : MarkedTemporaryReadCalls heap
  directoryCalls : MarkedDirectoryReadCalls heap stream
  slotOf : heap → stream → DescriptorSlot
  callbacks : AlignedKeeperCacheCallbacks heap
  checkpoint : NativeMarkedCheckpointReadHeap seed reader.chronology fileCalls
  listing : MarkedDirectoryReadReport checkpoint directoryCalls slotOf
  extents : MarkedWalExtentReports checkpoint listing
  beforeKeeper : heap
  seals : MarkedSealReadChain seed fileCalls reader.chronology.seals listing.reached beforeKeeper
  keeper : AlignedKeeperCacheReport reader.opening.finish view init raw.afterFlock seed
    (callbacks.withFileReads fileCalls) beforeKeeper
  sameLookup : fileCalls.stat = calls.lookup
  flat : optionalMetadataWith (fileCalls.stat (state.session.directory.file .wal)) seed.afterPending =
    .ok none seed.afterPending
  marker : IO.FS.Metadata
  marked : optionalMetadataWith (fileCalls.stat (state.session.directory.file .walBoundary)) seed.afterPending =
    .ok (some marker) seed.afterPending
  allocations : ∀ opened,
    reader.opening.finish.recoverFromCensus reader.chronology.metadataRelease reader.chronology.runs.released
      reader.chronology.sealRelease state.session.directory reader.opening.admission.cache
      (reader.opening.admission.reached, reader.opening.admission.held) =
      .ok opened (view.descriptors keeper.reached, view.files keeper.reached) →
    ∃ allocation : OpenReferenceAllocations allocatePhase allocateToken view.phase opened.installed keeper.reached,
      phaseIdentity allocation.phase = reader.opening.callbacks.nextRef ∧
      tokenIdentity allocation.token = reader.opening.callbacks.nextRef + 1 ∧
      CacheAllocationFrame view seed.directoryRef seed.activeRef seed.pendingRef keeper.reached allocation.afterPhase ∧
      CacheAllocationFrame view seed.directoryRef seed.activeRef seed.pendingRef allocation.afterPhase allocation.afterToken

def RawManifestRenameReopenEffects.openTable
    (seen : RawManifestRenameReopenEffects reader view calls init names bytes reached rebooted phaseIdentity tokenIdentity
      allocatePhase allocateToken stream)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles) : EStateM.Result IO.Error heap DiskTable :=
  let seed := seen.seed
  calls.runOpen input init makeCache (fun resolved lock cache => do
    let opened ← calls.recoverMarkedWithCacheRefs seen.fileCalls seen.directoryCalls seen.callbacks seed.directoryRef
      seed.activeRef seed.pendingRef remove write rename bootstrap resolved cache
    installReady opened.installed allocatePhase allocateToken
      (fun phase token => pure (assemble resolved lock cache phase token))) rebooted

/-- The marked-worker input uses the observed reader's selected manifest,
the rebooted WAL directory and the same checked read chronology. -/
private def NativeCheckpointManifestRenameReads.markedReport (seen : NativeCheckpointManifestRenameReads crash input plan)
    (valid : state.Valid) (pending : PendingClientReplay log reads state.writer.history)
    (bounded : ∀ read ∈ reads, read.BoundedBy state.writer.history.length) :
    MarkedOpenSuccessReports input state.session.directory state.writer.history log reads where
  inventory := crash.reboot
  retry := crash.retry
  layout := plan.layout
  published := crash.publication
  checkpoint := plan.checkpoint
  selected := plan.selected
  vacant := crash.vacant
  opening := ⟨seen.opening.admission, seen.opening.callbacks, seen.opening.reads, .aligned seen.opening.finish,
    seen.chronology, seen.opening.marker, seen.opening.markerFound⟩
  prepared := plan.prepared
  following := seen.opening.reads.walReads.selectedAfterWatermark plan.offsets plan.descriptors
  accepted := plan.accepted
  ordered := valid.retained.resumed.ordered
  wal := crash.rebootWal
  walLayout := ⟨valid.retained.layout.ordered, valid.retained.layout.forward, valid.retained.layout.activeEnd,
    valid.retained.layout.activeBytes⟩
  walValid := plan.walValid
  spans := valid.retained.spans
  active := plan.prepared.pair
  keeper := congrArg WalSegment.first plan.keeper
  kept := congrArg FileImage.kept (crash.reachedFiles valid)
  pending := pending
  bounded := bounded

section

variable {directory : DiskDirectory} {history modelHistory : List WAL.Write}
  {log : List DatabaseSubmissions} {recorded : List RecordedSnapshotRead}
  {marked : MarkedOpenSuccessReports input directory modelHistory log recorded}
  {entry final : heap} {seed : OpenSyncCacheAllocations marked.opening.admission.opened view init entry}
  {lock : IO.FS.Handle} {lockIdentity : IO.FS.Handle → Nat}

private theorem startsAtRenameReopen
    (installed : MarkedHeapInstallation marked view init entry seed lock lockIdentity phaseIdentity tokenIdentity
      allocatePhase allocateToken final)
    (rows : modelHistory = history) (next : NativeReadPosition history log)
    (sameReturn : marked.opening.finish.run marked.opening.chronology = next.opened)
    (returned : next.opened = .ok next.state.session (next.state.census, next.state.files))
    (cache : next.state.cache = marked.opening.admission.cache) (owner : next.state.owner = marked.opening.admission.owner)
    (slot : next.state.directorySlot = marked.opening.admission.cached)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects view.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) :
    ∃ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      start.current = ⟨history, log, next⟩ ∧ handle.table = installed.table ∧ handle.lock = lock ∧
      handle.files = installed.files ∧ handle.contents = view.phase ∧ handle.get = get ∧ handle.set = set ∧
      handle.ptrEq = ptrEq ∧ tokenIdentity handle.token = next.state.session.sessionRef ∧
      start.reached = installed.allocation.afterToken ∧ start.pins = [] ∧
      view.files start.reached = next.state.files ∧ view.descriptors start.reached = next.state.census ∧
      view.cacheAt start.reached seed.directoryRef seed.activeRef seed.pendingRef = next.state.cache := by
  subst history
  obtain ⟨handle, start, table, _, sameLock, sameCache, _, _, contents, getEq, setEq, compared,
    current, heap, pins, files, census, cached, _, _, _, _, token⟩ :=
    installed.startsAtReportedPosition next sameReturn returned cache owner slot effects ptrEq
  exact ⟨handle, start, current, table, sameLock, sameCache, contents, getEq, setEq, compared, token,
    heap, pins, files, census, cached⟩

end

section

variable {opened : NativeOpenedHandle heap} (current : NativeOpenedPosition opened)
  {cut : CheckpointPowerCut current.current.ready.state.session.directory current.current.ready.state.writer}
  {report : NativeCheckpointManifestRenameError (image := image) current.current.ready.state cut}
  {crash : NativeCheckpointManifestRenameCrash report} {plan : crash.Plan}
  {reader : NativeCheckpointManifestRenameReads crash input plan}

/-- The observed checkpoint return and power loss lead to the table
allocated by the same selected reader, with one common history step. -/
theorem NativeOpenedPosition.opensAfterManifestRenameError
    (seen : RawManifestRenameReopenEffects reader view calls init names bytes reached rebooted phaseIdentity tokenIdentity
      allocatePhase allocateToken stream)
    {cause : IO.Error} {after : CensusDirectoryCache × image}
    (returned : runCheckpointOnOpenPhase report.synced.settled.runs.perform opened.phase opened.get opened.set
      (current.reached, report.synced.settled.runs.entry.image) = .error cause (reached, after))
    (samePhase : view.phase = opened.contents)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files)) :
    let state := current.current.ready.state
    opened.table.UsesOpenCheckpointSchedule state.session.directory opened.files opened.phase ∧
    cause = report.cause ∧ after = (state.cache, report.after) ∧ view.phase reached opened.phase = some .poisoned ∧
    (view.descriptors reached, view.files reached) = (report.synced.settled.runs.descriptors after.2,
      ⟨report.synced.settled.runs.files after.2, state.files.owners⟩) ∧
    (view.descriptors rebooted, view.files rebooted) = (crash.reboot, crash.retry) ∧ (view.descriptors rebooted).slots = [] ∧
    names rebooted (state.session.directory.file .lock) = some ((view.handle seen.raw.afterFlock seen.raw.lock).1.inode
      (view.handle seen.raw.afterFlock seen.raw.lock).2.1.description) ∧
    names rebooted state.session.directory.path = some ((view.handle seen.seed.afterPending seen.seed.handle).1.inode
      (view.handle seen.seed.afterPending seen.seed.handle).2.1.description) ∧
    reader.SelectedReads ∧
    (∀ path payload, checkpointSurvivorPath state.session.directory state.writer crash.pair.manifest path →
      reader.ReadsSurvivor path payload → ∃ read : reader.opening.reads.reads.ObservesFile path payload,
        names rebooted path = some read.object ∧ bytes rebooted read.object = payload) ∧
    ∃ (next : NativeReadPosition current.current.history current.current.submissions)
      (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
      (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle),
      DiskTable.OpenSyncFiles.IsOpenAction state.session.directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk state.session.directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      NativeCheckpointManifestRenameReopened current.current.ready crash input next ∧
      reader.run = next.opened ∧ next.opened = .ok next.state.session (next.state.census, next.state.files) ∧
      NativeExecutionStep current.current (.checkpointManifestRenameCrashRecovered input cause crash.pair.manifest)
        start.current ∧
      state.writer.target.range.watermark ≤ next.state.writer.target.range.watermark ∧
      seen.openTable remove write rename bootstrap assemble makeCache = .ok handle.table start.reached ∧
      start.current = ⟨current.current.history, current.current.submissions, next⟩ ∧
      handle.lock = seen.raw.lock ∧ handle.files.UsesCacheReferences seen.seed.activeRef seen.seed.pendingRef
        seen.seed.directoryRef ∧ handle.files.AtDirectory state.session.directory.path ∧
      handle.contents = view.phase ∧ handle.get = opened.get ∧ handle.set = opened.set ∧ handle.ptrEq = opened.ptrEq ∧
      tokenIdentity handle.token = next.state.session.sessionRef ∧ start.pins = [] ∧
      view.files start.reached = next.state.files ∧ view.descriptors start.reached = next.state.census ∧
      view.cacheAt start.reached seen.seed.directoryRef seen.seed.activeRef seen.seed.pendingRef = next.state.cache := by
  intro state
  obtain ⟨source, diagnostic, image, poison⟩ := current.checkpointManifestRenameErrorFromReturn report returned
  obtain ⟨valid, rows, replay⟩ := current.current.ready.readPrefix.refines
  have pending : PendingClientReplay current.current.submissions current.current.ready.reads state.writer.history := rows.symm ▸ replay
  have bounded : ∀ read ∈ current.current.ready.reads, read.BoundedBy state.writer.history.length :=
    rows.symm ▸ current.current.ready.readPrefix.readsBounded
  let marked := reader.markedReport valid pending bounded
  obtain ⟨next, reopened, sameReturn, nextReturned, owner, slot, cache⟩ :=
    current.current.ready.reopensCheckpointManifestRenameWith crash reader
  obtain ⟨installed, cacheOpen, makeCache, cacheAction, cacheSource, ran⟩ := marked.opensAlignedFromAdmission seen.raw seen.seed
    reader.opening.finish rfl seen.checkpoint seen.listing seen.extents seen.seals seen.keeper seen.sameLookup
    seen.flat seen.marked remove write rename bootstrap assemble constructs seen.allocations
  have phaseEffects : OpenPhaseCellEffects view.phase opened.get opened.set := samePhase.symm ▸ opened.phaseEffects
  obtain ⟨handle, start, currentEq, rawTable, lock, files, contents, getEq, setEq, compareEq, token,
    reachedHeap, pins, sameFiles, sameCensus, sameCache⟩ :=
    startsAtRenameReopen installed rows next sameReturn nextReturned cache owner slot phaseEffects opened.ptrEq
  have stored : view.phase reached opened.phase = some .poisoned := by
    rw [samePhase]
    exact poison
  refine ⟨source, diagnostic, image, stored, ?_,
    Prod.ext seen.raw.entryCensus seen.raw.entryFiles, ?_, ?_, ?_, reader.readsSelected valid,
    fun _ _ => seen.reboot.readsSurvivingFile, next, cacheOpen, makeCache, handle, start, cacheAction, cacheSource,
    reopened, sameReturn, nextReturned, ?_, reopened.checkpointWatermark.1, ?_, currentEq, lock,
    files.symm ▸ installed.cacheReferences, files.symm ▸ installed.cacheDirectory, contents, getEq, setEq,
    compareEq, token, pins, sameFiles, sameCensus, sameCache⟩
  · rw [image]
    exact Prod.ext seen.reboot.returnedCensus seen.reboot.returnedFiles
  · rw [seen.raw.entryCensus]
    rfl
  · rw [seen.raw.sameLock, seen.raw.appendHandle]
    exact (seen.reboot.survivorNames _ (.inr (.inl rfl))).trans
      ((reader.opening.reads.sameObjects.2.1.symm).trans reader.lockObject).symm
  · rw [seen.seed.sameHandle, seen.seed.openedHandle]
    exact (seen.reboot.survivorNames _ (.inl rfl)).trans
      ((reader.opening.reads.sameObjects.1.symm).trans reader.directoryObject).symm
  · rw [currentEq, diagnostic]
    exact .recoverCheckpointManifestRenameError current.current crash next reopened
  · rw [rawTable, reachedHeap]
    exact ran

end

end Alvoki.Storage.DiskSession
