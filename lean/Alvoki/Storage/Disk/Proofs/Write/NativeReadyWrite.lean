import Alvoki.Storage.Disk.Proofs.Read.NativeReadyReadPrefix
import Alvoki.Storage.Disk.Proofs.Append.AppendHandleCustody

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
  tails : List ByteArray

namespace NativeReadyWritePreparation

variable {before : NativeReadyState}

abbrev keeperPath (_prepared : NativeReadyWritePreparation before) : FilePath :=
  before.session.directory.file (.walSegment before.writer.installed.activeFirst)

abbrev keeperName (_prepared : NativeReadyWritePreparation before) : String :=
  renderWalSegmentName before.writer.installed.activeFirst

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

private theorem rootedChild {root name view} (lookup : RunChildLookup root name view) :
    view.child root name = some lookup.child := by
  simpa only [lookup.atRoot, lookup.atName] using lookup.binds

/-- The actual append selection either opens a fresh slot from a cold
cache or reuses the live handle recorded at the checked canonical path.
Only the open branch changes the inventory. -/
inductive NativeReadyKeeperSelection {before : NativeReadyState} (prepared : NativeReadyWritePreparation before)
    {root : DeviceInode} {view : DirectoryReadNamespace} (checked : RunChildLookup root prepared.keeperName view)
    (openAppend : FilePath → EStateM IO.Error WriteFiles WriteHandle) : WriteHandle → DescriptorInventory → Prop where
  | fresh (slot : DescriptorSlot) (offset : Nat)
      (cold : before.cache.active = none)
      (free : ∀ previous ∈ before.census.slots, previous.address ≠ slot.address)
      (freshDescription : before.census.references slot.description = [])
      (resolved : RunChildLookup root prepared.keeperName view)
      (identity : view.modelObject resolved.child = before.census.inode slot.description)
      (opened : openAppend prepared.keeperPath prepared.initial =
        .ok (before.census.insert slot free, slot, offset) prepared.initial) :
      NativeReadyKeeperSelection prepared checked openAppend (before.census.insert slot free, slot, offset)
        (before.census.insert slot free)
  | cached (handle : WriteHandle) (found : before.cache.active = some (prepared.keeperPath, handle))
      (live : handle.2.1 ∈ before.census.slots)
      (sameInode : handle.1.inode handle.2.1.description = before.census.inode handle.2.1.description)
      (identity : view.modelObject checked.child = before.census.inode handle.2.1.description) :
      NativeReadyKeeperSelection prepared checked openAppend handle before.census

namespace NativeReadyKeeperSelection

variable {before : NativeReadyState} {prepared : NativeReadyWritePreparation before}
  {root : DeviceInode} {view : DirectoryReadNamespace} {checked : RunChildLookup root prepared.keeperName view}
  {openAppend : FilePath → EStateM IO.Error WriteFiles WriteHandle} {handle : WriteHandle} {reached : DescriptorInventory}

theorem selects (observed : NativeReadyKeeperSelection prepared checked openAppend handle reached) :
    selectAppendHandle before.cache.active openAppend prepared.keeperPath prepared.initial = .ok handle prepared.initial := by
  cases observed with
  | fresh _ _ cold _ _ _ _ opened => simp only [selectAppendHandle, cold, opened]
  | cached _ found _ _ _ => simp [selectAppendHandle, found, Pure.pure, EStateM.pure]

theorem custody (observed : NativeReadyKeeperSelection prepared checked openAppend handle reached) :
    (∀ slot ∈ before.census.slots, slot ∈ reached.slots) ∧ reached.inode = before.census.inode ∧
    handle.2.1 ∈ reached.slots ∧ handle.1.inode handle.2.1.description = reached.inode handle.2.1.description ∧
    view.modelObject checked.child = reached.inode handle.2.1.description := by
  cases observed with
  | fresh _ _ _ _ _ resolved identity _ =>
    have child := checked.child_eq (rootedChild resolved)
    exact ⟨fun _ present => List.mem_cons_of_mem _ present, rfl, List.mem_cons_self, rfl,
      (congrArg view.modelObject child).trans identity⟩
  | cached _ _ live sameInode identity => exact ⟨fun _ present => present, rfl, live, sameInode, identity⟩

/-- An exact cache hit forces reuse of that handle with no allocation. -/
theorem cachedResult (observed : NativeReadyKeeperSelection prepared checked openAppend handle reached)
    {active : WriteHandle} (atPath : before.cache.active = some (prepared.keeperPath, active)) :
    handle = active ∧ reached = before.census := by
  cases observed with
  | fresh _ _ cold _ _ _ _ _ => rw [cold] at atPath; contradiction
  | cached _ found _ _ _ => exact ⟨(Prod.mk.inj (Option.some.inj (found.symm.trans atPath))).2, rfl⟩

end NativeReadyKeeperSelection

/-- The guarded append and subsequent exclusive marker allocation use the
same held directory and reached inventory. -/
structure NativeReadyWriteStageAllocation {before : NativeReadyState} (prepared : NativeReadyWritePreparation before) where
  pendingEmpty : before.cache.pending = []
  directoryCapture : DescriptorInventory
  directoryCached : before.cache.directory = some (directoryCapture, before.directorySlot, 0)
  sameDirectoryInode : directoryCapture.inode before.directorySlot.description = before.census.inode before.directorySlot.description
  root : DeviceInode
  view : DirectoryReadNamespace
  directoryIdentity : view.modelObject root = before.census.inode before.directorySlot.description
  lockLookup : RunChildLookup root "LOCK" view
  lockIdentity : view.modelObject lockLookup.child = before.census.inode before.owner.description
  checkedKeeper : RunChildLookup root prepared.keeperName view
  lstat : FilePath → Except IO.Error (IO.FS.Metadata × Nat)
  metadata : IO.FS.Metadata
  statReturned : lstat prepared.keeperPath = .ok (metadata, view.modelObject checkedKeeper.child)
  regular : metadata.type = .file
  privateFile : metadata.numLinks = 1
  extent : metadata.byteSize.toNat = before.writer.installed.walBytes - before.writer.installed.activeFirst * WAL.frameSize
  openAppend : FilePath → EStateM IO.Error WriteFiles WriteHandle
  keeperHandle : WriteHandle
  afterSelect : DescriptorInventory
  selectsKeeper : NativeReadyKeeperSelection prepared checkedKeeper openAppend keeperHandle afterSelect
  markerSlot : DescriptorSlot
  markerFree : ∀ old ∈ afterSelect.slots, old.address ≠ markerSlot.address
  markerFresh : afterSelect.references markerSlot.description = []
  markerOffset : Nat
  stageView : DirectoryReadNamespace
  stageObjects : stageView.modelObject = view.modelObject
  stageNames : ∀ name, name ≠ "WAL.commit.next" → stageView.child root name = view.child root name
  openedMarker : RunChildLookup root "WAL.commit.next" stageView
  stageIdentity : stageView.modelObject openedMarker.child = before.census.inode markerSlot.description
  differentFiles : before.census.inode markerSlot.description ≠ before.census.inode keeperHandle.2.1.description
  appendWrite : WriteHandle → ByteArray → EStateM IO.Error WriteFiles Unit
  appendFlush : WriteHandle → EStateM IO.Error WriteFiles Unit
  buffered : WriteFiles
  wrote : appendWrite keeperHandle (WAL.encodeBatch prepared.batch) prepared.initial = .ok () buffered
  flushed : appendFlush keeperHandle buffered = .ok () prepared.appended

/-- The returned staging write and flush remember that same marker handle. -/
structure NativeReadyWriteStaging {before : NativeReadyState} (prepared : NativeReadyWritePreparation before)
    extends NativeReadyWriteStageAllocation prepared where
  tryStage : FilePath → EStateM IO.Error WriteFiles (Except IO.Error WriteHandle)
  detachStale : FilePath → EStateM IO.Error WriteFiles Unit
  createStage : FilePath → EStateM IO.Error WriteFiles WriteHandle
  stageWrite : WriteHandle → ByteArray → EStateM IO.Error WriteFiles Unit
  stageFlush : WriteHandle → EStateM IO.Error WriteFiles Unit
  staged : writeFreshStagedWith tryStage detachStale createStage stageWrite stageFlush prepared.stagedPath prepared.marker
    prepared.appended = .ok (afterSelect.insert markerSlot markerFree, markerSlot, markerOffset) prepared.staged

/-- The completed two-file barrier consumes the pending entry and closes
its temporary staging slot before the next marker operation. -/
structure NativeReadyWriteFileSyncs {before : NativeReadyState} (prepared : NativeReadyWritePreparation before)
    extends NativeReadyWriteStaging prepared where
  openRead : FilePath → EStateM IO.Error WriteFiles WriteHandle
  fsync : WriteHandle → EStateM IO.Error WriteFiles Unit
  syncedKeeper : fsync keeperHandle prepared.staged = .ok () prepared.keeperSynced
  syncedMarker : fsync (afterSelect.insert markerSlot markerFree, markerSlot, markerOffset)
    prepared.keeperSynced = .ok () prepared.bothSynced
  release : LockReferenceDrop
  closeStage : release = markerSlot.closeEvent

/-- A returned marker rename after the same successful file barriers. -/
structure NativeReadyWriteRenamed {before : NativeReadyState} (prepared : NativeReadyWritePreparation before)
    extends NativeReadyWriteFileSyncs prepared where
  publishedView : DirectoryReadNamespace
  renameObjects : publishedView.modelObject = stageView.modelObject
  renameNames : ∀ name, name ≠ "WAL.commit.next" → name ≠ "WAL.commit" →
    publishedView.child root name = stageView.child root name
  publishedMarker : RunChildLookup root "WAL.commit" publishedView
  renameChild : publishedMarker.child = openedMarker.child
  rename : FilePath → FilePath → EStateM IO.Error WriteFiles Unit
  renamed : rename prepared.stagedPath prepared.markerPath prepared.bothSynced = .ok () prepared.renamed

/-- The returned write also completes the cached directory barrier. -/
structure NativeReadyWriteReport {before : NativeReadyState} (prepared : NativeReadyWritePreparation before)
    extends NativeReadyWriteRenamed prepared where
  settledView : DirectoryReadNamespace
  directoryObjects : settledView.modelObject = publishedView.modelObject
  directoryNames : ∀ name, settledView.child root name = publishedView.child root name
  syncedDirectory : fsync (directoryCapture, before.directorySlot, 0) prepared.renamed = .ok () prepared.settled

namespace NativeReadyWriteStageAllocation

variable {before : NativeReadyState} {prepared : NativeReadyWritePreparation before}

/-- The production active-file guard projects the metadata from the
identity-bearing no-follow stat of the exact checked child. -/
def activeGuard (seen : NativeReadyWriteStageAllocation prepared) : BatchActiveGuard before.session.directory before.writer.installed where
  lookup := fun path => (seen.lstat path).map Prod.fst
  metadata := seen.metadata
  reached := by rw [show before.session.directory.file (.walSegment before.writer.installed.activeFirst) = prepared.keeperPath from rfl,
    seen.statReturned]; rfl
  regular := seen.regular
  privateFile := seen.privateFile
  extent := seen.extent

abbrev keeperSlot (seen : NativeReadyWriteStageAllocation prepared) : DescriptorSlot :=
  seen.keeperHandle.2.1

abbrev afterMarkerOpen (seen : NativeReadyWriteStageAllocation prepared) : DescriptorInventory :=
  seen.afterSelect.insert seen.markerSlot seen.markerFree

abbrev stageHandle (seen : NativeReadyWriteStageAllocation prepared) : WriteHandle :=
  (seen.afterMarkerOpen, seen.markerSlot, seen.markerOffset)

abbrev appendCache (seen : NativeReadyWriteStageAllocation prepared) : CensusDirectoryCache :=
  { before.cache with active := some (prepared.keeperPath, seen.keeperHandle) }

def append (seen : NativeReadyWriteStageAllocation prepared) (path : FilePath) (bytes : ByteArray) :=
  runAppendWithCache path bytes seen.openAppend seen.appendWrite seen.appendFlush

theorem appendReturns (seen : NativeReadyWriteStageAllocation prepared) :
    seen.append prepared.keeperPath (WAL.encodeBatch prepared.batch) (before.cache, prepared.initial) =
      .ok () (seen.appendCache, prepared.appended) := by
  simp only [append, runAppendWithCache_effect, seen.selectsKeeper.selects, seen.wrote, seen.flushed]

theorem stageBindings (seen : NativeReadyWriteStageAllocation prepared) :
    seen.stageView.child seen.root prepared.keeperName = some seen.checkedKeeper.child ∧
    seen.stageView.child seen.root "LOCK" = some seen.lockLookup.child ∧
    seen.stageView.child seen.root "WAL.commit.next" = some seen.openedMarker.child := by
  have differentStage : prepared.keeperName ≠ "WAL.commit.next" := by
    intro same
    have samePrefix := congrArg (fun name : String => name.toList.take 4) same
    simp [NativeReadyWritePreparation.keeperName, renderWalSegmentName, String.toList_append] at samePrefix
  exact ⟨(seen.stageNames _ differentStage).trans (rootedChild seen.checkedKeeper),
    (seen.stageNames _ (by decide)).trans (rootedChild seen.lockLookup), rootedChild seen.openedMarker⟩

end NativeReadyWriteStageAllocation

namespace NativeReadyWriteStaging

open NativeReadyWriteStageAllocation

variable {before : NativeReadyState} {prepared : NativeReadyWritePreparation before}

abbrev appendCache (seen : NativeReadyWriteStaging prepared) : CensusDirectoryCache :=
  seen.toNativeReadyWriteStageAllocation.appendCache

abbrev groupCache (seen : NativeReadyWriteStaging prepared) : CensusDirectoryCache :=
  seen.appendCache.remember prepared.stagedPath seen.stageHandle

noncomputable def stage (seen : NativeReadyWriteStaging prepared) (path : FilePath) (bytes : ByteArray) :=
  stageFreshWithCache path bytes
    (writeFreshStagedWith seen.tryStage seen.detachStale seen.createStage seen.stageWrite seen.stageFlush)

theorem stageReturns (seen : NativeReadyWriteStaging prepared) :
    seen.stage prepared.stagedPath prepared.marker (seen.appendCache, prepared.appended) =
      .ok () (seen.groupCache, prepared.staged) := by
  simp only [stage, stageFreshWithCache, seen.staged]

/-- A staged marker has a different path from the keeper. The first
sync in the group therefore finds the active handle with no cache change. -/
theorem selectsKeeperSync (seen : NativeReadyWriteStaging prepared)
    (openRead : FilePath → EStateM IO.Error image WriteHandle) (files : image) :
    seen.groupCache.resolve before.session.directory.path prepared.keeperPath openRead files =
      .ok seen.keeperHandle (seen.groupCache, files) := by
  have distinct : prepared.keeperPath ≠ prepared.stagedPath := by
    intro same
    obtain ⟨_, impossible⟩ := DiskDirectory.walSegment_exclusive same.symm
    cases impossible
  have miss : seen.groupCache.pending.find? (fun entry => entry.1 == prepared.keeperPath) = none := by
    simp [Cache.remember, pushPending, seen.pendingEmpty, distinct.symm]
  simp only [Cache.resolve, beq_eq_false_iff_ne.mpr
    (file_ne_directory before.session.directory (.walSegment before.writer.installed.activeFirst)),
    Bool.false_eq_true, ↓reduceIte, miss, show seen.groupCache.active = some (prepared.keeperPath, seen.keeperHandle) from rfl,
    beq_self_eq_true]

/-- The stage path consumes its pending entry before issuing the sync.
The selected handle remains the handle returned by the fresh stage. -/
theorem selectsStageSync (seen : NativeReadyWriteStaging prepared)
    (openRead : FilePath → EStateM IO.Error image WriteHandle) (files : image) :
    seen.groupCache.resolve before.session.directory.path prepared.stagedPath openRead files =
      .ok seen.stageHandle (seen.appendCache, files) := by
  have distinct : prepared.stagedPath ≠ before.session.directory.path :=
    file_ne_directory before.session.directory .stagedWalBoundary
  have hit : seen.groupCache.pending.find? (fun entry => entry.1 == prepared.stagedPath) =
      some (prepared.stagedPath, seen.stageHandle) := by
    simp [Cache.remember, pushPending]
  have consumed : seen.groupCache.consume prepared.stagedPath = seen.appendCache := by
    simp [Cache.remember, Cache.consume, pushPending, appendCache, seen.pendingEmpty]
  simp [Cache.resolve, distinct, hit, consumed]

end NativeReadyWriteStaging

namespace NativeReadyWriteFileSyncs

open NativeReadyWriteStaging NativeReadyWriteStageAllocation

variable {before : NativeReadyState} {prepared : NativeReadyWritePreparation before}

def census (seen : NativeReadyWriteFileSyncs prepared) : DescriptorInventory :=
  seen.afterMarkerOpen.afterDrops [seen.release]

/-- The reached census comes from the same observed marker allocation and
its release. The original directory and lock survive together with the
active append slot. -/
theorem censusAfterClose (seen : NativeReadyWriteFileSyncs prepared) : seen.census = seen.afterSelect := by
  rw [census, seen.closeStage]
  have drop := DescriptorInventory.insert_thenClose seen.afterSelect seen.markerSlot seen.markerFree []
  simp only [List.nil_append] at drop
  rw [drop]
  have filtered : ∀ slot ∈ seen.afterSelect.slots, (!seen.markerSlot.closeEvent.removes slot.reference) = true := by
    intro slot live
    cases same : seen.markerSlot.closeEvent.removes slot.reference with
    | false => rfl
    | true =>
      exfalso
      apply seen.markerFree slot live
      simpa [DescriptorSlot.address, DescriptorSlot.closeEvent, LockReferenceDrop.removes,
        Bool.and_eq_true, beq_iff_eq, Prod.mk.injEq] using same
  cases reached : seen.afterSelect with
  | mk slots distinct inode =>
    simp only [DescriptorInventory.afterDrops, List.all_cons, List.all_nil, Bool.and_true,
      DescriptorInventory.mk.injEq, and_true]
    exact List.filter_eq_self.mpr (by simpa only [reached] using filtered)

def sync (seen : NativeReadyWriteFileSyncs prepared) :=
  SyncPathGroup.run (SyncHandleRouting.sync before.session.directory.path seen.openRead seen.fsync)

/-- The group uses the handle from the append for the keeper and consumes
the handle from the staged write for the marker. -/
theorem groupReturns (seen : NativeReadyWriteFileSyncs prepared) :
    seen.sync #[prepared.keeperPath, prepared.stagedPath] (seen.groupCache, prepared.staged) =
      .ok () (seen.appendCache, prepared.bothSynced) := by
  rw [NativeReadyWriteFileSyncs.sync, SyncPathGroup.run_pair]
  have keeper : SyncHandleRouting.sync before.session.directory.path seen.openRead seen.fsync prepared.keeperPath (seen.groupCache, prepared.staged) =
      .ok () (seen.groupCache, prepared.keeperSynced) := by
    simp only [SyncHandleRouting.sync, seen.selectsKeeperSync, seen.syncedKeeper, withCache]
  rw [keeper]
  simp only [SyncHandleRouting.sync, seen.selectsStageSync, seen.syncedMarker, withCache]

end NativeReadyWriteFileSyncs

namespace NativeReadyWriteRenamed

variable {before : NativeReadyState} {prepared : NativeReadyWritePreparation before}

def replace (seen : NativeReadyWriteRenamed prepared) (source target : FilePath) :
    EStateM IO.Error (CensusDirectoryCache × WriteFiles) Unit :=
  fun (cache, files) => withCache cache (seen.rename source target files)

theorem renameReturns (seen : NativeReadyWriteRenamed prepared) :
    seen.replace prepared.stagedPath prepared.markerPath (seen.appendCache, prepared.bothSynced) =
      .ok () (seen.appendCache, prepared.renamed) := by
  simp only [replace, seen.renamed, withCache]

/-- Renaming the staged marker changes neither the append name nor the
lock, and the active marker is the file written and synced earlier. -/
theorem renameBindings (seen : NativeReadyWriteRenamed prepared) :
    seen.publishedView.child seen.root prepared.keeperName = some seen.checkedKeeper.child ∧
    seen.publishedView.child seen.root "LOCK" = some seen.lockLookup.child ∧
    seen.publishedView.child seen.root "WAL.commit" = some seen.openedMarker.child := by
  have differentStage : prepared.keeperName ≠ "WAL.commit.next" := by
    intro same
    have samePrefix := congrArg (fun name : String => name.toList.take 4) same
    simp [NativeReadyWritePreparation.keeperName, renderWalSegmentName, String.toList_append] at samePrefix
  have differentMarker : prepared.keeperName ≠ "WAL.commit" := by
    intro same
    have samePrefix := congrArg (fun name : String => name.toList.take 4) same
    simp [NativeReadyWritePreparation.keeperName, renderWalSegmentName, String.toList_append] at samePrefix
  obtain ⟨keeper, lock, _⟩ := seen.stageBindings
  exact ⟨(seen.renameNames _ differentStage differentMarker).trans keeper,
    (seen.renameNames "LOCK" (by decide) (by decide)).trans lock,
    (rootedChild seen.publishedMarker).trans (congrArg some seen.renameChild)⟩

end NativeReadyWriteRenamed

namespace NativeReadyWriteReport

open NativeReadyWriteStaging NativeReadyWriteStageAllocation NativeReadyWriteFileSyncs

variable {before : NativeReadyState} {prepared : NativeReadyWritePreparation before}

/-- The group syncs the checked keeper and staged marker on the held
root. The reached census keeps the writer's live slots after closing
the temporary marker handle. -/
structure Custody (seen : NativeReadyWriteReport prepared) : Prop where
  keeperIdentity : seen.keeperHandle.1.inode seen.keeperSlot.description = seen.census.inode seen.keeperSlot.description
  keeperNamed : seen.view.modelObject seen.checkedKeeper.child = seen.census.inode seen.keeperSlot.description
  markerNamed : seen.settledView.modelObject seen.publishedMarker.child = seen.census.inode seen.markerSlot.description
  separate : seen.census.inode seen.markerSlot.description ≠ seen.census.inode seen.keeperSlot.description
  directoryNamed : seen.directoryCapture.inode before.directorySlot.description = seen.settledView.modelObject seen.root
  lockNamed : seen.view.modelObject seen.lockLookup.child = seen.census.inode before.owner.description
  keeperAtGroup : seen.keeperSlot ∈ seen.afterMarkerOpen.slots
  markerAtGroup : seen.markerSlot ∈ seen.afterMarkerOpen.slots
  ownerLive : before.owner ∈ seen.census.slots
  directoryLive : before.directorySlot ∈ seen.census.slots
  keeperLive : seen.keeperSlot ∈ seen.census.slots
  markerClosed : seen.census.references seen.markerSlot.description = []

theorem physicalCustody (seen : NativeReadyWriteReport prepared) (valid : before.Valid) : seen.Custody := by
  obtain ⟨previous, inode, live, same, checked⟩ := seen.selectsKeeper.custody
  constructor
  all_goals try simp only [seen.censusAfterClose]
  · exact same
  · exact checked
  · rw [seen.directoryObjects, seen.renameObjects, seen.renameChild, inode]
    exact seen.stageIdentity
  · rw [inode]
    exact seen.differentFiles
  · rw [seen.directoryObjects, seen.renameObjects, seen.stageObjects]
    exact seen.sameDirectoryInode.trans seen.directoryIdentity.symm
  · rw [inode]
    exact seen.lockIdentity
  · exact List.mem_cons_of_mem _ live
  · exact List.mem_cons_self
  · exact previous _ valid.ownerLive
  · exact previous _ valid.directoryLive
  · exact live
  · exact seen.markerFresh

/-- The canonical keeper and lock stay bound to their original children
at the grouped sync, at directory fsync after rename, and on return. -/
structure BindingFrames (seen : NativeReadyWriteReport prepared) : Prop where
  keeperAtGroup : seen.stageView.child seen.root prepared.keeperName = some seen.checkedKeeper.child
  lockAtGroup : seen.stageView.child seen.root "LOCK" = some seen.lockLookup.child
  keeperAtBarrier : seen.publishedView.child seen.root prepared.keeperName = some seen.checkedKeeper.child
  lockAtBarrier : seen.publishedView.child seen.root "LOCK" = some seen.lockLookup.child
  keeperAtReturn : seen.settledView.child seen.root prepared.keeperName = some seen.checkedKeeper.child
  lockAtReturn : seen.settledView.child seen.root "LOCK" = some seen.lockLookup.child
  markerAtReturn : seen.settledView.child seen.root "WAL.commit" = some seen.openedMarker.child

theorem bindingFrames (seen : NativeReadyWriteReport prepared) : seen.BindingFrames := by
  obtain ⟨keeperStaged, lockStaged, _⟩ := seen.stageBindings
  obtain ⟨keeperRenamed, lockRenamed, markerRenamed⟩ := seen.renameBindings
  exact ⟨keeperStaged, lockStaged, keeperRenamed, lockRenamed,
    (seen.directoryNames _).trans keeperRenamed, (seen.directoryNames _).trans lockRenamed,
    (seen.directoryNames _).trans markerRenamed⟩

noncomputable def calls (seen : NativeReadyWriteReport prepared) : WriteRequest.Calls WriteHandle where
  cache := before.cache
  lookup := seen.activeGuard.lookup
  append := seen.toNativeReadyWriteStageAllocation.append
  stage := seen.toNativeReadyWriteStaging.stage
  sync := seen.toNativeReadyWriteFileSyncs.sync
  rename := seen.toNativeReadyWriteRenamed.replace

private theorem appendReturns (seen : NativeReadyWriteReport prepared) :
    seen.calls.append prepared.keeperPath (WAL.encodeBatch prepared.batch) (before.cache, prepared.initial) =
      .ok () (seen.appendCache, prepared.appended) := by
  exact seen.toNativeReadyWriteStageAllocation.appendReturns

private theorem stageReturns (seen : NativeReadyWriteReport prepared) :
    seen.calls.stage prepared.stagedPath prepared.marker (seen.appendCache, prepared.appended) =
      .ok () (seen.groupCache, prepared.staged) := by
  exact seen.toNativeReadyWriteStaging.stageReturns

/-- The healthy continuation uses the same append handle and staged file
barrier as the prefix at the next operation. -/
theorem groupReturns (seen : NativeReadyWriteReport prepared) :
    seen.calls.sync #[prepared.keeperPath, prepared.stagedPath] (seen.groupCache, prepared.staged) =
      .ok () (seen.appendCache, prepared.bothSynced) :=
  seen.toNativeReadyWriteFileSyncs.groupReturns

private theorem renameReturns (seen : NativeReadyWriteReport prepared) :
    seen.calls.rename prepared.stagedPath prepared.markerPath (seen.appendCache, prepared.bothSynced) =
      .ok () (seen.appendCache, prepared.renamed) := by
  exact seen.toNativeReadyWriteRenamed.renameReturns

private theorem directoryReturns (seen : NativeReadyWriteReport prepared) :
    seen.calls.sync #[before.session.directory.path] (seen.appendCache, prepared.renamed) =
      .ok () (seen.appendCache, prepared.settled) := by
  simp [calls, NativeReadyWriteFileSyncs.sync, SyncPathGroup.run_single, SyncHandleRouting.sync, Cache.resolve,
    seen.directoryCached, seen.syncedDirectory, withCache]

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

/-- The next append's canonical path still denotes the live active
handle in the returned cache, and the same root and lock bindings remain. -/
theorem nextCacheBindings (seen : NativeReadyWriteReport prepared) (valid : before.Valid) (target : Target) :
    (seen.next target).cache.directory = some (seen.directoryCapture, (seen.next target).directorySlot, 0) ∧
    (seen.next target).cache.active = some ((seen.next target).session.directory.file
      (.walSegment (seen.next target).writer.installed.activeFirst), seen.keeperHandle) ∧
    (seen.next target).cache.pending = [] ∧
    seen.settledView.modelObject seen.root = seen.directoryCapture.inode (seen.next target).directorySlot.description ∧
    (seen.settledView.child seen.root (renderWalSegmentName (seen.next target).writer.installed.activeFirst)).map
      seen.settledView.modelObject = some ((seen.next target).census.inode seen.keeperSlot.description) ∧
    (seen.settledView.child seen.root "LOCK").map seen.settledView.modelObject =
      some ((seen.next target).census.inode (seen.next target).owner.description) := by
  have custody := seen.physicalCustody valid
  refine ⟨seen.directoryCached, rfl, seen.pendingEmpty, custody.directoryNamed.symm, ?_, ?_⟩
  · change (seen.settledView.child seen.root prepared.keeperName).map seen.settledView.modelObject = _
    rw [seen.bindingFrames.keeperAtReturn, seen.directoryObjects, seen.renameObjects, seen.stageObjects]
    exact congrArg some custody.keeperNamed
  · rw [seen.bindingFrames.lockAtReturn, seen.directoryObjects, seen.renameObjects, seen.stageObjects]
    exact congrArg some custody.lockNamed

/-- A new no-follow stat over the settled view may report a new extent.
Its exact path still selects the old live handle. The selector's append
open callback is arbitrary because reuse never calls it. -/
theorem cachedSelectionForNext (seen : NativeReadyWriteReport prepared) (valid : before.Valid)
    {target : Target} (nextPrepared : NativeReadyWritePreparation (seen.next target))
    (checked : RunChildLookup seen.root nextPrepared.keeperName seen.settledView)
    (openAppend : FilePath → EStateM IO.Error WriteFiles WriteHandle) :
    NativeReadyKeeperSelection nextPrepared checked openAppend seen.keeperHandle (seen.next target).census := by
  have custody := seen.physicalCustody valid
  have names := seen.nextCacheBindings valid target
  have bound := names.2.2.2.2.1
  change (seen.settledView.child seen.root nextPrepared.keeperName).map seen.settledView.modelObject = _ at bound
  rw [rootedChild checked] at bound
  exact .cached seen.keeperHandle names.2.1 custody.keeperLive custody.keeperIdentity (Option.some.inj bound)

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
  have custody := seen.physicalCustody valid
  have returned : seen.calls.run request before.session.directory before.writer =
      .ok prepared.table.committed (.ready seen.publication.nextInstalled, ⟨(seen.appendCache, prepared.settled), before.writer.owners⟩) := by
    rw [WriteRequest.Calls.run, request.runReported_eq_batch valid.retained, rows]
    exact runBatchWrite_acknowledges seen.activeGuard prepared.nonempty prepared.prepared prepared.fits seen.publishes
  exact ⟨target, selected, ⟨rfl, valid.owner, custody.ownerLive, custody.directoryLive,
      ⟨seen.directoryCapture, seen.directoryCached⟩, retained⟩,
    returned, rfl, rfl, rfl, rfl, custody.keeperLive⟩

/-- Issue the next write at the previous publication's exact ready state.
The new stat names the same canonical child, and the native selector
reuses the old append handle without allocating another keeper slot.
The staged marker slot closes before the new ready state returns. -/
theorem acknowledgesAgain (previous : NativeReadyWriteReport prepared) (valid : before.Valid)
    {target : Target} (ready : (previous.next target).Valid)
    {nextPrepared : NativeReadyWritePreparation (previous.next target)}
    (current : NativeReadyWriteReport nextPrepared)
    (sameRoot : current.root = previous.root) (sameView : current.view = previous.settledView)
    (request : WriteRequest) (rows : request.rows = nextPrepared.rows) :
    current.checkedKeeper.child = previous.checkedKeeper.child ∧
    current.keeperHandle = previous.keeperHandle ∧ current.census = (previous.next target).census ∧
    current.appendCache = (previous.next target).cache ∧
    ∃ nextTarget, (current.next nextTarget).Valid ∧
      current.calls.run request (previous.next target).session.directory (previous.next target).writer =
        .ok nextPrepared.table.committed ((current.next nextTarget).session.phase,
          ⟨((current.next nextTarget).cache, nextPrepared.settled), (current.next nextTarget).files.owners⟩) ∧
      (current.next nextTarget).writer.history = (previous.next target).writer.history ++ nextPrepared.batch := by
  have keeperBound : current.view.child current.root nextPrepared.keeperName = some previous.checkedKeeper.child := by
    rw [sameRoot, sameView]
    exact previous.bindingFrames.keeperAtReturn
  have cacheHit : (previous.next target).cache.active = some (nextPrepared.keeperPath, previous.keeperHandle) :=
    (previous.nextCacheBindings valid target).2.1
  obtain ⟨handle, census⟩ := current.selectsKeeper.cachedResult cacheHit
  have cache : current.appendCache = (previous.next target).cache := by
    dsimp only [NativeReadyWriteStageAllocation.appendCache, NativeReadyWriteStaging.appendCache]
    rw [handle, ← cacheHit]
  obtain ⟨nextTarget, _, installed, returned, extended, _, _, _, _⟩ := current.acknowledges ready request rows
  exact ⟨current.checkedKeeper.child_eq keeperBound, handle, current.censusAfterClose.trans census, cache,
    nextTarget, installed, returned, extended⟩

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
