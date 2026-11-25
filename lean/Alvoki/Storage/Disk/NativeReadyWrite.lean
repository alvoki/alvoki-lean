import Alvoki.Storage.Disk.NativeReadyReadPrefix
import Alvoki.Storage.Disk.AppendHandleCustody

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair WalSegmentCommit WAL.Boundary

private abbrev WriteHandle := DescriptorInventory × DescriptorSlot × Nat

/-- Preflight for a nonempty publication from the exact ready state. -/
structure NativeReadyWritePreparation (before : NativeReadyState) where
  rows : List (UInt64 × Option UInt64)
  batch : List WAL.Write
  table : PackedTable
  nonempty : rows ≠ []
  prepared : prepareBatch before.writer.installed.table rows = some (batch, table)
  fits : before.writer.installed.walBytes + WAL.frameSize * rows.length < UInt64.size
  guard : BatchActiveGuard before.session.directory before.writer.installed
  tails : List ByteArray

namespace NativeReadyWritePreparation

variable {before : NativeReadyState}

abbrev keeperPath (_prepared : NativeReadyWritePreparation before) : FilePath :=
  before.session.directory.file (.walSegment before.writer.installed.activeFirst)

abbrev stagedPath (_prepared : NativeReadyWritePreparation before) : FilePath :=
  before.session.directory.file .stagedWalBoundary

abbrev markerPath (_prepared : NativeReadyWritePreparation before) : FilePath :=
  before.session.directory.file .walBoundary

def count (prepared : NativeReadyWritePreparation before) : Nat :=
  before.writer.installed.walBytes + WAL.frameSize * prepared.rows.length

def marker (prepared : NativeReadyWritePreparation before) : ByteArray :=
  WAL.Boundary.encode prepared.count.toUInt64

private theorem encodeCount (prepared : NativeReadyWritePreparation before) :
    WAL.Boundary.encode prepared.count.toUInt64 = prepared.marker := rfl

def effects (prepared : NativeReadyWritePreparation before) : WriteEffects :=
  ⟨.ok (), prepared.tails, .ok (), .ok (), .success, .success⟩

def initial (_prepared : NativeReadyWritePreparation before) : WriteFiles :=
  WriteFiles.initial before.writer.history (before.files.image.directory.staged .walBoundary)

def appended (prepared : NativeReadyWritePreparation before) : WriteFiles :=
  { prepared.initial with
    visibleTail := WAL.encode prepared.batch
    crashTails := ByteArray.empty :: prepared.tails
    crashPossible := by simp }

def staged (prepared : NativeReadyWritePreparation before) : WriteFiles :=
  { prepared.appended with marker := { prepared.appended.marker with staged := some (prepared.marker, false) } }

def keeperSynced (prepared : NativeReadyWritePreparation before) : WriteFiles :=
  prepared.staged.syncWal .complete

def bothSynced (prepared : NativeReadyWritePreparation before) : WriteFiles :=
  { prepared.keeperSynced with marker := { prepared.keeperSynced.marker with staged := some (prepared.marker, true) } }

def renamed (prepared : NativeReadyWritePreparation before) : WriteFiles :=
  { prepared.bothSynced with marker := ⟨some prepared.marker, some prepared.marker :: prepared.initial.marker.crashImages, none⟩ }

def settled (prepared : NativeReadyWritePreparation before) : WriteFiles :=
  { prepared.renamed with marker := .settled (some prepared.marker) }

end NativeReadyWritePreparation

/-- The first append after reopen uses a cold active cache. The successful
append and marker allocations extend the reached inventory in order.
The reported staging close is the only additional descriptor drop before
return. The filesystem supplies the individual callback effects. -/
structure NativeReadyWriteReport {before : NativeReadyState} (prepared : NativeReadyWritePreparation before) where
  cold : before.cache.active = none
  pendingEmpty : before.cache.pending = []
  directoryCapture : DescriptorInventory
  directoryCached : before.cache.directory = some (directoryCapture, before.directorySlot, 0)
  sameDirectoryInode : directoryCapture.inode before.directorySlot.description = before.census.inode before.directorySlot.description
  root : DeviceInode
  view : DirectoryReadNamespace
  directoryIdentity : view.modelObject root = before.census.inode before.directorySlot.description
  lockLookup : RunChildLookup root "LOCK" view
  lockIdentity : view.modelObject lockLookup.child = before.census.inode before.owner.description
  keeperSlot : DescriptorSlot
  keeperFree : ∀ old ∈ before.census.slots, old.address ≠ keeperSlot.address
  keeperFresh : before.census.references keeperSlot.description = []
  keeperOffset : Nat
  checkedKeeper : RunChildLookup root (renderWalSegmentName before.writer.installed.activeFirst) view
  openedKeeper : RunChildLookup root (renderWalSegmentName before.writer.installed.activeFirst) view
  keeperIdentity : view.modelObject openedKeeper.child = before.census.inode keeperSlot.description
  markerSlot : DescriptorSlot
  markerFree : ∀ old ∈ (before.census.insert keeperSlot keeperFree).slots, old.address ≠ markerSlot.address
  markerFresh : (before.census.insert keeperSlot keeperFree).references markerSlot.description = []
  markerOffset : Nat
  stageView : DirectoryReadNamespace
  openedMarker : RunChildLookup root "WAL.commit.next" stageView
  stageIdentity : stageView.modelObject openedMarker.child = before.census.inode markerSlot.description
  differentFiles : before.census.inode markerSlot.description ≠ before.census.inode keeperSlot.description
  publishedView : DirectoryReadNamespace
  publishedMarker : RunChildLookup root "WAL.commit" publishedView
  renameIdentity : publishedView.modelObject publishedMarker.child = stageView.modelObject openedMarker.child
  openAppend : FilePath → EStateM IO.Error WriteFiles WriteHandle
  appendWrite : WriteHandle → ByteArray → EStateM IO.Error WriteFiles Unit
  appendFlush : WriteHandle → EStateM IO.Error WriteFiles Unit
  tryStage : FilePath → EStateM IO.Error WriteFiles (Except IO.Error WriteHandle)
  detachStale : FilePath → EStateM IO.Error WriteFiles Unit
  createStage : FilePath → EStateM IO.Error WriteFiles WriteHandle
  stageWrite : WriteHandle → ByteArray → EStateM IO.Error WriteFiles Unit
  stageFlush : WriteHandle → EStateM IO.Error WriteFiles Unit
  openRead : FilePath → EStateM IO.Error WriteFiles WriteHandle
  fsync : WriteHandle → EStateM IO.Error WriteFiles Unit
  rename : FilePath → FilePath → EStateM IO.Error WriteFiles Unit
  buffered : WriteFiles
  opened : openAppend prepared.keeperPath prepared.initial =
    .ok (before.census.insert keeperSlot keeperFree, keeperSlot, keeperOffset) prepared.initial
  wrote : appendWrite (before.census.insert keeperSlot keeperFree, keeperSlot, keeperOffset)
    (WAL.encodeBatch prepared.batch) prepared.initial = .ok () buffered
  flushed : appendFlush (before.census.insert keeperSlot keeperFree, keeperSlot, keeperOffset) buffered =
    .ok () prepared.appended
  staged : writeFreshStagedWith tryStage detachStale createStage stageWrite stageFlush prepared.stagedPath prepared.marker
    prepared.appended = .ok ((before.census.insert keeperSlot keeperFree).insert markerSlot markerFree, markerSlot, markerOffset)
      prepared.staged
  syncedKeeper : fsync (before.census.insert keeperSlot keeperFree, keeperSlot, keeperOffset) prepared.staged =
    .ok () prepared.keeperSynced
  syncedMarker : fsync ((before.census.insert keeperSlot keeperFree).insert markerSlot markerFree, markerSlot, markerOffset)
    prepared.keeperSynced = .ok () prepared.bothSynced
  release : LockReferenceDrop
  closeStage : release = markerSlot.closeEvent
  renamed : rename prepared.stagedPath prepared.markerPath prepared.bothSynced = .ok () prepared.renamed
  syncedDirectory : fsync (directoryCapture, before.directorySlot, 0) prepared.renamed = .ok () prepared.settled

namespace NativeReadyWriteReport

variable {before : NativeReadyState} {prepared : NativeReadyWritePreparation before}

abbrev afterKeeperOpen (seen : NativeReadyWriteReport prepared) : DescriptorInventory :=
  before.census.insert seen.keeperSlot seen.keeperFree

abbrev afterMarkerOpen (seen : NativeReadyWriteReport prepared) : DescriptorInventory :=
  seen.afterKeeperOpen.insert seen.markerSlot seen.markerFree

abbrev keeperHandle (seen : NativeReadyWriteReport prepared) : WriteHandle :=
  (seen.afterKeeperOpen, seen.keeperSlot, seen.keeperOffset)

abbrev stageHandle (seen : NativeReadyWriteReport prepared) : WriteHandle :=
  (seen.afterMarkerOpen, seen.markerSlot, seen.markerOffset)

abbrev appendCache (seen : NativeReadyWriteReport prepared) : CensusDirectoryCache :=
  { before.cache with active := some (prepared.keeperPath, seen.keeperHandle) }

private abbrev groupCache (seen : NativeReadyWriteReport prepared) : CensusDirectoryCache :=
  seen.appendCache.remember prepared.stagedPath seen.stageHandle

def census (seen : NativeReadyWriteReport prepared) : DescriptorInventory :=
  seen.afterMarkerOpen.afterDrops [seen.release]

/-- The reached census comes from the same observed marker allocation and
its release. The original directory and lock survive together with the
active append slot. -/
theorem censusAfterClose (seen : NativeReadyWriteReport prepared) : seen.census = seen.afterKeeperOpen := by
  rw [census, seen.closeStage]
  have drop := DescriptorInventory.insert_thenClose seen.afterKeeperOpen seen.markerSlot seen.markerFree []
  simp only [List.nil_append] at drop
  rw [drop]
  have filtered : ∀ slot ∈ seen.afterKeeperOpen.slots, (!seen.markerSlot.closeEvent.removes slot.reference) = true := by
    intro slot live
    cases same : seen.markerSlot.closeEvent.removes slot.reference with
    | false => rfl
    | true =>
      exfalso
      apply seen.markerFree slot live
      simpa [DescriptorSlot.address, DescriptorSlot.closeEvent, LockReferenceDrop.removes,
        Bool.and_eq_true, beq_iff_eq, Prod.mk.injEq] using same
  cases reached : seen.afterKeeperOpen with
  | mk slots distinct inode =>
    simp only [DescriptorInventory.afterDrops, List.all_cons, List.all_nil, Bool.and_true,
      DescriptorInventory.mk.injEq, and_true]
    exact List.filter_eq_self.mpr (by simpa only [reached] using filtered)

/-- The descriptors issued by the group refer to the checked keeper
and the staged marker on the held root. The cached directory stays the
same object, including after the observed staged-handle release. -/
theorem physicalCustody (seen : NativeReadyWriteReport prepared) (valid : before.Valid) :
    seen.checkedKeeper.child = seen.openedKeeper.child ∧
    seen.view.modelObject seen.checkedKeeper.child = seen.census.inode seen.keeperSlot.description ∧
    seen.publishedView.modelObject seen.publishedMarker.child = seen.census.inode seen.markerSlot.description ∧
    seen.census.inode seen.markerSlot.description ≠ seen.census.inode seen.keeperSlot.description ∧
    seen.directoryCapture.inode before.directorySlot.description = seen.view.modelObject seen.root ∧
    seen.view.modelObject seen.lockLookup.child = seen.census.inode before.owner.description ∧
    seen.keeperSlot ∈ seen.afterMarkerOpen.slots ∧ seen.markerSlot ∈ seen.afterMarkerOpen.slots ∧
    before.owner ∈ seen.census.slots ∧ before.directorySlot ∈ seen.census.slots ∧
    before.census.references seen.keeperSlot.description = [] ∧ seen.census.references seen.markerSlot.description = [] := by
  have bound := seen.openedKeeper.binds
  rw [seen.openedKeeper.atRoot, seen.openedKeeper.atName] at bound
  have same := seen.checkedKeeper.child_eq bound
  rw [seen.censusAfterClose]
  exact ⟨same, (congrArg seen.view.modelObject same).trans seen.keeperIdentity,
    seen.renameIdentity.trans seen.stageIdentity, seen.differentFiles,
    seen.sameDirectoryInode.trans seen.directoryIdentity.symm, seen.lockIdentity,
    List.mem_cons_of_mem _ List.mem_cons_self, List.mem_cons_self,
    List.mem_cons_of_mem _ valid.ownerLive, List.mem_cons_of_mem _ valid.directoryLive, seen.keeperFresh, seen.markerFresh⟩

noncomputable def calls (seen : NativeReadyWriteReport prepared) : WriteRequest.Calls WriteHandle where
  cache := before.cache
  lookup := prepared.guard.lookup
  append := fun path bytes => runAppendWithCache path bytes seen.openAppend seen.appendWrite seen.appendFlush
  stage := fun path bytes => stageFreshWithCache path bytes
    (writeFreshStagedWith seen.tryStage seen.detachStale seen.createStage seen.stageWrite seen.stageFlush)
  sync := SyncPathGroup.run (sync before.session.directory.path seen.openRead seen.fsync)
  rename := fun source target (cache, files) => withCache cache (seen.rename source target files)

private theorem appendReturns (seen : NativeReadyWriteReport prepared) :
    seen.calls.append prepared.keeperPath (WAL.encodeBatch prepared.batch) (before.cache, prepared.initial) =
      .ok () (seen.appendCache, prepared.appended) := by
  simp only [calls, runAppendWithCache_effect, seen.cold, selectAppendHandle, seen.opened, seen.wrote, seen.flushed]

private theorem stageReturns (seen : NativeReadyWriteReport prepared) :
    seen.calls.stage prepared.stagedPath prepared.marker (seen.appendCache, prepared.appended) =
      .ok () (seen.groupCache, prepared.staged) := by
  simp only [calls, stageFreshWithCache, seen.staged]

/-- The group uses the handle from the append for the keeper and consumes
the handle from the staged write for the marker. -/
theorem groupReturns (seen : NativeReadyWriteReport prepared) :
    seen.calls.sync #[prepared.keeperPath, prepared.stagedPath] (seen.groupCache, prepared.staged) =
      .ok () (seen.appendCache, prepared.bothSynced) := by
  let directory := before.session.directory
  have keeperNe : prepared.keeperPath ≠ prepared.stagedPath := by
    intro same
    obtain ⟨_, impossible⟩ := DiskDirectory.walSegment_exclusive same.symm
    cases impossible
  have miss : seen.groupCache.pending.find? (fun entry => entry.1 == prepared.keeperPath) = none := by
    simp [Cache.remember, pushPending, seen.pendingEmpty, keeperNe.symm]
  have hit : seen.groupCache.pending.find? (fun entry => entry.1 == prepared.stagedPath) =
      some (prepared.stagedPath, seen.stageHandle) := by
    simp [Cache.remember, pushPending]
  change SyncPathGroup.run (sync directory.path seen.openRead seen.fsync)
    #[prepared.keeperPath, prepared.stagedPath] (seen.groupCache, prepared.staged) = _
  rw [groupedActivePending (file_ne_directory directory (.walSegment before.writer.installed.activeFirst))
    (file_ne_directory directory .stagedWalBoundary) miss (show seen.groupCache.active = _ from rfl)
    hit seen.openRead seen.fsync, seen.syncedKeeper]
  have consumed : seen.groupCache.consume prepared.stagedPath = seen.appendCache := by
    simp [Cache.remember, Cache.consume, pushPending, appendCache, seen.pendingEmpty]
  simp only [seen.syncedMarker]
  change EStateM.Result.ok () (seen.groupCache.consume prepared.stagedPath, prepared.bothSynced) = _
  rw [consumed]

private theorem renameReturns (seen : NativeReadyWriteReport prepared) :
    seen.calls.rename prepared.stagedPath prepared.markerPath (seen.appendCache, prepared.bothSynced) =
      .ok () (seen.appendCache, prepared.renamed) := by
  simp [calls, seen.renamed, withCache]

private theorem directoryReturns (seen : NativeReadyWriteReport prepared) :
    seen.calls.sync #[before.session.directory.path] (seen.appendCache, prepared.renamed) =
      .ok () (seen.appendCache, prepared.settled) := by
  simp [calls, SyncPathGroup.run_single, sync, Cache.resolve, appendCache, seen.directoryCached, seen.syncedDirectory, withCache]

/-- The actual append-first schedule reaches every successful action in
order. The returned cache still uses the original directory and the live
append handle, with the temporary marker entry consumed. -/
theorem publishes (seen : NativeReadyWriteReport prepared) :
    commitBytesAt before.session.directory before.writer.installed.activeFirst (WAL.encodeBatch prepared.batch)
      prepared.count seen.calls.append seen.calls.stage seen.calls.sync seen.calls.rename (before.cache, prepared.initial) =
      .ok () (seen.appendCache, prepared.settled) := by
  rw [commitBytesAt_fileEffects]
  simp only [WAL.Boundary.commit, Bind.bind, EStateM.bind, prepared.encodeCount,
    seen.appendReturns, seen.stageReturns, seen.groupReturns, seen.renameReturns, seen.directoryReturns, Pure.pure, EStateM.pure]

private noncomputable def appendFiles (seen : NativeReadyWriteReport prepared)
    (path : FilePath) (bytes : ByteArray) : EStateM IO.Error WriteFiles Unit :=
  fun files => withoutWriteGroupCache (seen.calls.append path bytes (before.cache, files))

private noncomputable def stageFiles (seen : NativeReadyWriteReport prepared)
    (path : FilePath) (bytes : ByteArray) : EStateM IO.Error WriteFiles Unit :=
  fun files => withoutWriteGroupCache (seen.calls.stage path bytes (seen.appendCache, files))

private noncomputable def syncFiles (seen : NativeReadyWriteReport prepared)
    (paths : Array FilePath) : EStateM IO.Error WriteFiles Unit := fun files =>
  let cache := if paths = #[before.session.directory.path] then seen.appendCache else seen.groupCache
  withoutWriteGroupCache (seen.calls.sync paths (cache, files))

private theorem groupFiles (seen : NativeReadyWriteReport prepared) :
    seen.syncFiles #[prepared.keeperPath, prepared.stagedPath] prepared.staged = .ok () prepared.bothSynced := by
  have distinct : #[prepared.keeperPath, prepared.stagedPath] ≠ #[before.session.directory.path] := by
    intro equal
    have size := congrArg Array.size equal
    change (2 : Nat) = 1 at size
    omega
  simp only [syncFiles, ite_eq_right distinct, seen.groupReturns, withoutWriteGroupCache]

private theorem directoryFiles (seen : NativeReadyWriteReport prepared) :
    seen.syncFiles #[before.session.directory.path] prepared.renamed = .ok () prepared.settled := by
  simp [syncFiles, seen.directoryReturns, withoutWriteGroupCache]

private theorem modelAppend : appendBatch prepared.effects prepared.batch prepared.initial = .ok () prepared.appended := rfl

private theorem modelStage : prepared.effects.markerStep prepared.marker .writeStaged prepared.appended =
    .ok () prepared.staged := rfl

private theorem modelGroup : prepared.effects.markerStep prepared.marker .syncStaged prepared.staged =
    .ok () prepared.bothSynced := rfl

private theorem modelRename : prepared.effects.markerStep prepared.marker .renameStaged prepared.bothSynced =
    .ok () prepared.renamed := rfl

private theorem modelDirectory : prepared.effects.markerStep prepared.marker .syncDirectory prepared.renamed =
    .ok () prepared.settled := rfl

private theorem markerReports (seen : NativeReadyWriteReport prepared) {prior remaining : List Publication.Step}
    {action : Publication.Step} {files : WriteFiles} (scheduled : Publication.steps = prior ++ action :: remaining)
    (reached : (prior.forM (prepared.effects.markerStep prepared.marker)) prepared.appended = .ok () files) :
    forgetError (performMarkerAt before.session.directory before.writer.installed.activeFirst prepared.count
      seen.stageFiles seen.syncFiles seen.rename action) files = prepared.effects.markerStep prepared.marker action files := by
  rcases prior with _ | ⟨first, _ | ⟨second, _ | ⟨third, _ | ⟨fourth, _⟩⟩⟩⟩
  all_goals simp only [Publication.steps, List.nil_append, List.cons_append, List.cons.injEq] at scheduled
  · obtain ⟨rfl, _⟩ := scheduled
    obtain rfl := (EStateM.Result.ok.inj reached).2
    simp only [performMarkerAt, Publication.performReplacement, prepared.encodeCount,
      stageFiles, seen.stageReturns, withoutWriteGroupCache, forgetError, modelStage]
  · obtain ⟨rfl, rfl, _⟩ := scheduled
    simp only [List.forM_eq_forM, List.forM_cons, Bind.bind, EStateM.bind, List.forM_nil,
      modelStage, Pure.pure, EStateM.pure, EStateM.Result.ok.injEq, true_and] at reached
    subst files
    change forgetError (seen.syncFiles #[prepared.keeperPath, prepared.stagedPath]) prepared.staged = _
    simp only [forgetError, seen.groupFiles, modelGroup]
  · obtain ⟨rfl, rfl, rfl, _⟩ := scheduled
    simp only [List.forM_eq_forM, List.forM_cons, Bind.bind, EStateM.bind, List.forM_nil,
      modelStage, modelGroup, Pure.pure, EStateM.pure, EStateM.Result.ok.injEq, true_and] at reached
    subst files
    simp only [performMarkerAt, Publication.performReplacement, seen.renamed, forgetError, modelRename]
  · obtain ⟨rfl, rfl, rfl, rfl, _⟩ := scheduled
    simp only [List.forM_eq_forM, List.forM_cons, Bind.bind, EStateM.bind, List.forM_nil,
      modelStage, modelGroup, modelRename, Pure.pure, EStateM.pure, EStateM.Result.ok.injEq, true_and] at reached
    subst files
    simp only [performMarkerAt, Publication.performReplacement, seen.directoryFiles, forgetError, modelDirectory]
  · simp at scheduled

private theorem modelReports (seen : NativeReadyWriteReport prepared) :
    BatchCommitReports before.session.directory before.writer.installed.activeFirst before.writer.history prepared.batch
      prepared.count prepared.effects (before.files.image.directory.staged .walBoundary)
      seen.appendFiles seen.stageFiles seen.syncFiles seen.rename := by
  constructor
  · change forgetError (seen.appendFiles prepared.keeperPath (WAL.encodeBatch prepared.batch)) prepared.initial = _
    simp only [appendFiles, seen.appendReturns, withoutWriteGroupCache, forgetError]
    exact modelAppend.symm
  · intro appended ran prior action remaining files scheduled reached
    change appendBatch prepared.effects prepared.batch prepared.initial = .ok () appended at ran
    have same := (EStateM.Result.ok.inj (ran.symm.trans (modelAppend (prepared := prepared)))).2
    subst appended
    exact seen.markerReports scheduled reached

private theorem commitsFiles (seen : NativeReadyWriteReport prepared) :
    commitBytesAt before.session.directory before.writer.installed.activeFirst (WAL.encodeBatch prepared.batch)
      prepared.count seen.appendFiles seen.stageFiles seen.syncFiles seen.rename prepared.initial = .ok () prepared.settled := by
  rw [commitBytesAt_fileEffects]
  simp only [WAL.Boundary.commit, Bind.bind, EStateM.bind, prepared.encodeCount, appendFiles,
    seen.appendReturns, stageFiles, seen.stageReturns, withoutWriteGroupCache, seen.groupFiles, seen.renamed,
    seen.directoryFiles, Pure.pure, EStateM.pure]

/-- Construct the retained-writer report from the individual callbacks. -/
noncomputable def publication (seen : NativeReadyWriteReport prepared) :
    SegmentedBatchAppendReport before.session.directory before.writer :=
  ⟨prepared.rows, prepared.batch, prepared.table, prepared.effects, seen.appendFiles, seen.stageFiles,
    seen.syncFiles, seen.rename, prepared.settled, prepared.nonempty, prepared.prepared, prepared.fits,
    seen.modelReports, seen.commitsFiles⟩

noncomputable def next (seen : NativeReadyWriteReport prepared) (target : Target) : NativeReadyState :=
  { before with
    session := { before.session with phase := .ready seen.publication.nextInstalled }
    writer := seen.publication.next target
    census := seen.census
    cache := seen.appendCache }

/-- Both public write entry points acknowledge the same exact reached
files and cache. The next writer retains the same owner and session
references, with the newly selected history and active append slot. -/
theorem acknowledges (seen : NativeReadyWriteReport prepared) (valid : before.Valid)
    (request : WriteRequest) (rows : request.rows = prepared.rows) :
    ∃ target, seen.publication.Selects target ∧ (seen.next target).Valid ∧
      seen.calls.run request before.session.directory before.writer =
        .ok prepared.table.committed ((seen.next target).session.phase,
          ⟨((seen.next target).cache, prepared.settled), (seen.next target).files.owners⟩) ∧
      (seen.next target).writer.history = before.writer.history ++ prepared.batch ∧
      (seen.next target).files = ⟨seen.publication.files, before.files.owners⟩ ∧
      (seen.next target).session.sessionRef = before.session.sessionRef ∧
      (seen.next target).session.phaseRef = before.session.phaseRef ∧
      seen.keeperSlot ∈ (seen.next target).census.slots := by
  obtain ⟨target, selected, retained⟩ := seen.publication.preservesRetained valid.retained
  have keepLive (slot : DescriptorSlot) (live : slot ∈ before.census.slots) : slot ∈ seen.census.slots := by
    rw [seen.censusAfterClose]
    exact List.mem_cons_of_mem _ live
  have appendLive : seen.keeperSlot ∈ seen.census.slots := by
    rw [seen.censusAfterClose]
    exact List.mem_cons_self
  have returned : seen.calls.run request before.session.directory before.writer =
      .ok prepared.table.committed (.ready seen.publication.nextInstalled, ⟨(seen.appendCache, prepared.settled), before.writer.owners⟩) := by
    rw [WriteRequest.Calls.run, request.runReported_eq_batch valid.retained, rows]
    exact runBatchWrite_acknowledges prepared.guard prepared.nonempty prepared.prepared prepared.fits seen.publishes
  exact ⟨target, selected, ⟨rfl, valid.owner, keepLive _ valid.ownerLive, keepLive _ valid.directoryLive,
      ⟨seen.directoryCapture, seen.directoryCached⟩, retained⟩,
    returned, rfl, rfl, rfl, rfl, appendLive⟩

end NativeReadyWriteReport

/-- Begin the write after the exact returned native session and any
reached snapshot-read prefix. Register the acknowledged batch in the
same ordered submission ledger and carry the actual next writer. -/
theorem NativeReadyReadPrefix.acknowledgesWrite
    {opened : EStateM.Result IO.Error CensusOpenState SegmentedSession}
    {initial before : NativeReadyState} {history : List WAL.Write} {log : List DatabaseSubmissions}
    {reads : List RecordedSnapshotRead}
    (prior : NativeReadyReadPrefix opened initial history log reads before)
    {prepared : NativeReadyWritePreparation before} (seen : NativeReadyWriteReport prepared)
    (request : WriteRequest) (rows : request.rows = prepared.rows) :
    ∃ target, opened = .ok initial.session (initial.census, initial.files) ∧
      before.files = initial.files ∧ before.census = initial.census ∧ before.cache = initial.cache ∧
      (seen.next target).Valid ∧
      seen.calls.run request before.session.directory before.writer =
        .ok prepared.table.committed ((seen.next target).session.phase,
          ⟨((seen.next target).cache, prepared.settled), (seen.next target).files.owners⟩) ∧
      (seen.next target).writer.history = history ++ prepared.batch ∧
      DatabaseBatchRetention (log ++ [.acknowledgedBatch prepared.batch]) (seen.next target).writer.history := by
  obtain ⟨valid, sameHistory, _, _, retention, _, _, _⟩ := prior.refines
  obtain ⟨returned, files, census, cache, _, _, _, _⟩ := prior.frames
  obtain ⟨target, _, ready, wrote, extended, _, _, _, _⟩ := seen.acknowledges valid request rows
  have recorded := retention.append (entry := .acknowledgedBatch prepared.batch) rfl
  have nextHistory := extended.trans (congrArg (· ++ prepared.batch) sameHistory)
  exact ⟨target, returned, files, census, cache, ready, wrote, nextHistory, nextHistory.symm ▸ recorded⟩

end Alvoki.Storage.DiskSession
