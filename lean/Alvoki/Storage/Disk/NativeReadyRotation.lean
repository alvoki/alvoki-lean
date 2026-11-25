import Alvoki.Storage.Disk.NativeReadRecoveryTrace
import Alvoki.Storage.Disk.RotationExistingSuccessor

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair SyncHandleRouting
open WAL (frameSize)

private abbrev Files := DescriptorInventory × RotationCreateFiles

/-- For a private runtime handle, clearing the active reference reports the
close of its original slot. Other kernel aliases are left in the census. -/
private def releaseRotationActive (cache : CensusDirectoryCache) (files : Files) : Files :=
  (files.1.afterDrops (cache.active.toList.map (fun entry => entry.2.2.1.closeEvent)), files.2)

private theorem releaseRotationActive_closes (cache : CensusDirectoryCache) (files : Files)
    {entry : FilePath × RotationSuccessorHandle} (active : cache.active = some entry) :
    entry.2.2.1 ∉ (releaseRotationActive cache files).1.slots := by
  simp [releaseRotationActive, active, DescriptorInventory.afterDrops, DescriptorSlot.closeEvent,
    LockReferenceDrop.removes]

/-- At the active reset, the cache still owns the original append handle
when present. The report gives the observed descriptor-only release at
this step, including the live root and writer slots after reset. -/
structure NativeRotationCacheReset (state : NativeReadyState) (cache : CensusDirectoryCache) (files : Files) where
  live : ∀ entry ∈ cache.active, entry.2.2.1 ∈ files.1.slots
  drops : List LockReferenceDrop
  observed : drops = cache.active.toList.map (fun entry => entry.2.2.1.closeEvent)
  owner : state.owner ∈ (files.1.afterDrops drops).slots
  directory : state.directorySlot ∈ (files.1.afterDrops drops).slots

private def NativeReadyState.withRotatedWal (state : NativeReadyState) (valid : state.Valid)
    (census : DescriptorInventory) : NativeReadyState :=
  let writer := state.writer.rotated valid.retained.rotationTarget
  { state with
    session := { state.session with phase := .ready writer.installed }
    writer := writer
    cache := { state.cache with active := none }
    census }

private theorem NativeRotationCacheReset.validNext
    {state : NativeReadyState} {cache : CensusDirectoryCache} {files : Files}
    (reset : NativeRotationCacheReset state cache files) (valid : state.Valid)
    (nonempty : state.writer.installed.activeFirst < state.writer.installed.walBytes / frameSize) :
    (state.withRotatedWal valid (releaseRotationActive cache files).1).Valid := by
  have retained := valid.retained.rotates nonempty (target := valid.retained.rotationTarget) ⟨rfl, rfl, rfl⟩
  refine ⟨rfl, valid.owner, ?_, ?_, valid.captured, retained⟩
  · simpa only [NativeReadyState.withRotatedWal, releaseRotationActive, ← reset.observed] using reset.owner
  · simpa only [NativeReadyState.withRotatedWal, releaseRotationActive, ← reset.observed] using reset.directory

/-- Both physical routes share the same client and logical WAL frame. -/
structure NativeRotationFrame (current next : NativeReadPosition history log) : Prop where
  sessionRef : next.state.session.sessionRef = current.state.session.sessionRef
  phaseRef : next.state.session.phaseRef = current.state.session.phaseRef
  table : next.state.writer.installed.table = current.state.writer.installed.table
  range : next.state.writer.target.range = current.state.writer.target.range
  checkpoint : next.state.writer.checkpoint = current.state.writer.checkpoint
  durable : next.state.writer.published.durable = current.state.writer.published.durable
  sealed : next.state.writer.wal.sealed = current.state.writer.wal.sealed ++ [current.state.writer.wal.active]
  keeper : next.state.writer.wal.active = ⟨history.length, history.length, ByteArray.empty⟩
  reads : next.reads = current.reads

private def NativeReadPosition.afterRotation (current : NativeReadPosition history log)
    (census : DescriptorInventory) (valid : (current.state.withRotatedWal current.readPrefix.refines.1 census).Valid) :
    NativeReadPosition history log :=
  let state := current.state.withRotatedWal current.readPrefix.refines.1 census
  ⟨.ok state.session (state.census, state.files), state, state, current.reads,
    .installed rfl valid current.readPrefix.refines.2.1 current.readPrefix.refines.2.2 current.readPrefix.readsBounded⟩

private theorem NativeReadPosition.rotationFrame (current : NativeReadPosition history log)
    (census : DescriptorInventory) (valid : (current.state.withRotatedWal current.readPrefix.refines.1 census).Valid) :
    NativeRotationFrame current (current.afterRotation census valid) := by
  have last : current.state.writer.wal.active.last = history.length :=
    current.readPrefix.refines.1.retained.layout.activeEnd.trans (congrArg List.length current.readPrefix.refines.2.1)
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
  change current.state.writer.wal.rotated.active = _
  simp only [WalSegmentImage.rotated, last]
  rfl

/-- The former keeper and current marker in the reached directory.
The same measured bytes certify the former keeper after it becomes a seal. -/
structure NativeRotationKeeperMarker (before : SegmentedWriterState) (root : DeviceInode)
    (files : RotationCreateFiles) (keeper marker : DeviceInode) : Prop where
  keeperName : files.view.child root (renderWalSegmentName before.installed.activeFirst) = some keeper
  markerName : files.view.child root "WAL.commit" = some marker
  keeperCrash : files.crashNames (renderWalSegmentName before.installed.activeFirst) = [some keeper]
  markerCrash : files.crashNames "WAL.commit" = [some marker]
  keeperPayload : files.inodes.crashBytes (files.view.modelObject keeper) = [before.wal.active.bytes]
  markerPayload : ∃ bytes, before.wal.directory.active.walBoundary = some bytes ∧
    files.inodes.crashBytes (files.view.modelObject marker) = [bytes]

/-- The two barriers and cache retirement of a returned rotation, from
the reached ready session whose checked successor already existed. -/
structure NativeReadyExistingRotation (state : NativeReadyState) where
  opened : RotationExistingSuccessorOpen state.session.directory state.writer
  file : RotationExistingSuccessorFileSync opened
  directory : RotationExistingSuccessorDirectorySync file
  create : FilePath → EStateM IO.Error (CensusDirectoryCache × Files) Unit
  cache : opened.cache = state.cache
  census : opened.inventory = state.census
  owner : opened.owner = state.owner
  keeper : DeviceInode
  marker : DeviceInode
  priorFiles : NativeRotationKeeperMarker state.writer opened.root opened.files keeper marker
  keepDistinct : opened.files.view.modelObject keeper ≠ opened.inventory.inode opened.slot.description
  markerDistinct : opened.files.view.modelObject marker ≠ opened.inventory.inode opened.slot.description
  keeperSurvives : directory.settled.crashNames (renderWalSegmentName state.writer.installed.activeFirst) =
    opened.files.crashNames (renderWalSegmentName state.writer.installed.activeFirst)
  markerSurvives : directory.settled.crashNames "WAL.commit" = opened.files.crashNames "WAL.commit"
  reset : NativeRotationCacheReset state opened.cache directory.after

namespace NativeReadyExistingRotation

variable {state : NativeReadyState}

def run (report : NativeReadyExistingRotation state) :=
  runObservedRotationWithReset state.session.directory report.opened.lookup report.opened.readEmpty
    report.create report.file.group releaseRotationActive
    (state.session.phase, ⟨(state.cache, state.census, report.opened.files), state.writer.owners⟩)

def next (report : NativeReadyExistingRotation state) (valid : state.Valid) : NativeReadyState :=
  state.withRotatedWal valid (releaseRotationActive report.opened.cache report.directory.after).1

theorem returned (report : NativeReadyExistingRotation state) (valid : state.Valid) :
    let next := report.next valid
    report.run = .ok () (next.session.phase, ⟨(next.cache, next.census, report.directory.settled), next.writer.owners⟩) := by
  have ran := runObservedRotationWithReset_ready state.session.directory state.writer.installed
    ⟨(report.opened.cache, report.opened.inventory, report.opened.files), state.writer.owners⟩
    report.opened.lookup report.opened.readEmpty report.create report.file.group releaseRotationActive report.opened.nonempty
    report.opened.checked (report.directory.publishes report.create)
  unfold run next NativeReadyState.withRotatedWal
  rw [valid.phase, ← report.cache, ← report.census]
  exact ran

theorem validNext (report : NativeReadyExistingRotation state) (valid : state.Valid) :
    (report.next valid).Valid :=
  report.reset.validNext valid report.opened.nonempty

/-- The directory barrier is on the original cached slot and the return
has its original inode, while the prior active runtime slot is closed. -/
theorem custody (report : NativeReadyExistingRotation state) (valid : state.Valid) :
    let next := report.next valid
    report.directory.handle.2.1 = state.directorySlot ∧
    next.census.inode = state.census.inode ∧
    report.directory.settled.view.child report.opened.root "LOCK" = some report.opened.lock.child ∧
    report.directory.settled.view.modelObject report.opened.lock.child = next.census.inode state.owner.description ∧
    (∀ entry ∈ state.cache.active, entry.2.2.1 ∉ next.census.slots) := by
  obtain ⟨captured, known⟩ := valid.captured
  have same : report.directory.handle = (captured, state.directorySlot, 0) :=
    Option.some.inj (report.directory.cached.symm.trans ((congrArg Cache.directory report.cache).trans known))
  have inodes : (report.next valid).census.inode = state.census.inode := report.census ▸ rfl
  obtain ⟨_, lock, _, _, _⟩ := report.opened.lockCustody
  refine ⟨congrArg (fun handle : RotationSuccessorHandle => handle.2.1) same, inodes, ?_, ?_, ?_⟩
  · exact (congrArg (fun view => view.child report.opened.root "LOCK") report.directory.view).trans lock
  · refine (congrArg (fun view => view.modelObject report.opened.lock.child) report.directory.view).trans
      (report.opened.lockObject.trans ?_)
    rw [report.census, report.owner, inodes]
  · intro entry member
    have active : state.cache.active = some entry := member
    exact releaseRotationActive_closes _ _ ((congrArg Cache.active report.cache).trans active)

theorem keepsKeeperMarker (report : NativeReadyExistingRotation state) :
    NativeRotationKeeperMarker state.writer report.opened.root report.directory.settled report.keeper report.marker := by
  have keptBytes (object : DeviceInode)
      (distinct : report.opened.files.view.modelObject object ≠ report.opened.inventory.inode report.opened.slot.description) :
      report.directory.settled.inodes.crashBytes (report.directory.settled.view.modelObject object) =
        report.opened.files.inodes.crashBytes (report.opened.files.view.modelObject object) := by
    rw [report.directory.bytes, report.directory.view]
    exact report.file.effects.2.2.1 _ distinct
  obtain ⟨bytes, boundary, durable⟩ := report.priorFiles.markerPayload
  exact ⟨(congrArg (fun view => view.child report.opened.root (renderWalSegmentName state.writer.installed.activeFirst))
      report.directory.view).trans report.priorFiles.keeperName,
    (congrArg (fun view => view.child report.opened.root "WAL.commit") report.directory.view).trans report.priorFiles.markerName,
    report.keeperSurvives.trans report.priorFiles.keeperCrash, report.markerSurvives.trans report.priorFiles.markerCrash,
    (keptBytes _ report.keepDistinct).trans report.priorFiles.keeperPayload,
    ⟨bytes, boundary, (keptBytes _ report.markerDistinct).trans durable⟩⟩

end NativeReadyExistingRotation

/-- Preparing the new keeper preserves the installed table, the acknowledged
history, the selected checkpoint and the ledger. -/
structure NativeExistingRotationContinuation (current next : NativeReadPosition history log)
    (report : NativeReadyExistingRotation current.state) : Prop where
  reached : next.state = report.next current.readPrefix.refines.1
  returned : report.run = .ok () (next.state.session.phase,
    ⟨(next.state.cache, next.state.census, report.directory.settled), next.state.writer.owners⟩)
  frame : NativeRotationFrame current next
  successor : report.directory.settled.view.child report.opened.root
    (renderWalSegmentName next.state.writer.wal.active.first) = some report.opened.statChild.child
  successorCrash : report.directory.settled.crashNames (renderWalSegmentName next.state.writer.wal.active.first) =
    [some report.opened.statChild.child]
  successorObject : report.directory.settled.view.modelObject report.opened.statChild.child =
    next.state.census.inode report.opened.slot.description
  successorBytes : report.directory.settled.inodes.crashBytes
    (report.directory.settled.view.modelObject report.opened.statChild.child) = [next.state.writer.wal.active.bytes]
  keeperMarker :
    NativeRotationKeeperMarker current.state.writer report.opened.root report.directory.settled report.keeper report.marker
  directorySlot : report.directory.handle.2.1 = current.state.directorySlot
  lock : report.directory.settled.view.child report.opened.root "LOCK" = some report.opened.lock.child
  lockObject : report.directory.settled.view.modelObject report.opened.lock.child =
    next.state.census.inode current.state.owner.description
  temporaryClosed : next.state.census.references report.opened.slot.description = []
  closed : ∀ entry ∈ current.state.cache.active, entry.2.2.1 ∉ next.state.census.slots

theorem NativeReadPosition.rotatesExisting (current : NativeReadPosition history log)
    (report : NativeReadyExistingRotation current.state) :
    ∃ next, NativeExistingRotationContinuation current next report := by
  let valid := current.readPrefix.refines.1
  let state := report.next valid
  let next := current.afterRotation state.census (report.validNext valid)
  obtain ⟨successor, survivor, successorObject, bytes, _⟩ := report.directory.durableSuccessor
  obtain ⟨directory, _, lock, object, closed⟩ := report.custody valid
  have atEnd : state.writer.wal.active.first = current.state.writer.installed.walBytes / frameSize :=
    valid.retained.layout.activeEnd.trans valid.retained.rotationAtEnd.symm
  have temporary : state.census.references report.opened.slot.description = [] := by
    change ((report.file.after.1.afterDrops report.directory.drops).afterDrops _).references report.opened.slot.description = []
    rw [DescriptorInventory.references_afterDrops, DescriptorInventory.references_afterDrops, report.file.closesReadSlot.2.1]
    rfl
  exact ⟨next, rfl, report.returned valid, current.rotationFrame _ _, atEnd.symm ▸ successor,
    atEnd.symm ▸ survivor, successorObject, bytes, report.keepsKeeperMarker, directory, lock, object, temporary, closed⟩

/-- The actual exclusive create, pending-cache fsync, and directory
fsync for the usual healthy rotation with an absent successor. The
successor handle is temporary once the file barrier consumes its entry. -/
structure NativeReadyCreatedRotation (state : NativeReadyState) where
  lookup : FilePath → Except IO.Error IO.FS.Metadata
  parent : RotationCreateParent state.session.directory state.writer lookup state.census
  parentOwner : parent.owner = state.owner
  created : RotationRawSuccessor parent
  checked : checkActiveSegmentWith (m := EStateM IO.Error (CensusDirectoryCache × Files))
    state.session.directory state.writer.installed (fun path => liftExcept (lookup path))
    (state.cache, state.census, parent.files) = .ok () (state.cache, state.census, parent.files)
  pending : state.cache.consume (rotationSuccessorPath state.session.directory state.writer) = state.cache
  openExclusive : FilePath → EStateM IO.Error Files RotationSuccessorHandle
  beforeFile : List LockReferenceDrop
  openReturned : openExclusive (rotationSuccessorPath state.session.directory state.writer) (state.census, parent.files) =
    .ok created.handle (created.handle.1.afterDrops beforeFile, created.files)
  successorLive : created.raw ∈ (created.handle.1.afterDrops beforeFile).slots
  ownerAtFile : state.owner ∈ (created.handle.1.afterDrops beforeFile).slots
  fsync : RotationSuccessorHandle → EStateM IO.Error Files Unit
  fileDrops : List LockReferenceDrop
  fileReturned : fsync created.handle (created.handle.1.afterDrops beforeFile, created.files) =
    .ok () ((created.handle.1.afterDrops beforeFile).afterDrops (fileDrops ++ [created.raw.closeEvent]),
      (created.afterSync true).files)
  directoryHandle : RotationSuccessorHandle
  cached : state.cache.directory = some directoryHandle
  pathObject : FilePath → Option DeviceInode
  bound : pathObject state.session.directory.path = some parent.root
  capturedObject : parent.files.view.modelObject parent.root = directoryHandle.1.inode directoryHandle.2.1.description
  currentObject : parent.files.view.modelObject parent.root = state.census.inode directoryHandle.2.1.description
  directoryLive : directoryHandle.2.1 ∈
    ((created.handle.1.afterDrops beforeFile).afterDrops (fileDrops ++ [created.raw.closeEvent])).slots
  ownerAtDirectory : state.owner ∈
    ((created.handle.1.afterDrops beforeFile).afterDrops (fileDrops ++ [created.raw.closeEvent])).slots
  directoryDrops : List LockReferenceDrop
  settled : RotationCreateFiles
  directoryReturned : fsync directoryHandle
      ((created.handle.1.afterDrops beforeFile).afterDrops (fileDrops ++ [created.raw.closeEvent]),
        (created.afterSync true).files) =
    .ok () (((created.handle.1.afterDrops beforeFile).afterDrops (fileDrops ++ [created.raw.closeEvent])).afterDrops
      directoryDrops, settled)
  view : settled.view = created.files.view
  bytes : settled.inodes = (created.afterSync true).files.inodes
  successorSurvives : settled.crashNames
    (renderWalSegmentName (state.writer.installed.walBytes / frameSize)) = [some created.child.child]
  keeperSurvives : settled.crashNames (renderWalSegmentName state.writer.installed.activeFirst) =
    parent.files.crashNames (renderWalSegmentName state.writer.installed.activeFirst)
  markerSurvives : settled.crashNames "WAL.commit" = parent.files.crashNames "WAL.commit"
  reset : NativeRotationCacheReset state state.cache
    (((created.handle.1.afterDrops beforeFile).afterDrops (fileDrops ++ [created.raw.closeEvent])).afterDrops
      directoryDrops, settled)
  openRead : FilePath → EStateM IO.Error Files RotationSuccessorHandle

namespace NativeReadyCreatedRotation

variable {state : NativeReadyState}

private abbrev successorPath (state : NativeReadyState) :=
  rotationSuccessorPath state.session.directory state.writer

def readEmpty (report : NativeReadyCreatedRotation state) (path : FilePath) :
    EStateM IO.Error (CensusDirectoryCache × Files) (Option ByteArray) :=
  WalSegmentRotation.readEmptyWith (pure (report.lookup path)) path "WAL segment successor is not empty"

def create (report : NativeReadyCreatedRotation state) (path : FilePath) :
    EStateM IO.Error (CensusDirectoryCache × Files) Unit := fun (cache, files) =>
  match report.openExclusive path files with
  | .ok handle files => .ok () (cache.remember path handle, files)
  | .error cause files => .error cause (cache, files)

def group (report : NativeReadyCreatedRotation state) (path : FilePath) :=
  SyncPathGroup.run (sync state.session.directory.path report.openRead report.fsync) #[path]

abbrev opened (report : NativeReadyCreatedRotation state) : Files :=
  (report.created.handle.1.afterDrops report.beforeFile, report.created.files)

abbrev fileSynced (report : NativeReadyCreatedRotation state) : Files :=
  (report.opened.1.afterDrops (report.fileDrops ++ [report.created.raw.closeEvent]),
    (report.created.afterSync true).files)

abbrev directorySynced (report : NativeReadyCreatedRotation state) : Files :=
  (report.fileSynced.1.afterDrops report.directoryDrops, report.settled)

theorem readsAbsent (report : NativeReadyCreatedRotation state) :
    report.readEmpty (successorPath state) (state.cache, state.census, report.parent.files) =
      .ok none (state.cache, state.census, report.parent.files) := by
  obtain ⟨path, message, absent⟩ := report.parent.absent
  simp [readEmpty, WalSegmentRotation.readEmptyWith, optionalMetadataWith, successorPath,
    absent, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

theorem fileGroup (report : NativeReadyCreatedRotation state) :
    report.group (successorPath state)
      (state.cache.remember (successorPath state) report.created.handle, report.opened) =
      .ok () (state.cache, report.fileSynced) := by
  have separate : (successorPath state == state.session.directory.path) = false := by
    simp [successorPath, file_ne_directory]
  have consumed : (state.cache.remember (successorPath state) report.created.handle).consume (successorPath state) =
      state.cache.consume (successorPath state) := by
    simp [Cache.remember, pushPending, Cache.consume]
  unfold group
  rw [SyncPathGroup.run_single]
  have resolved :
      (state.cache.remember (successorPath state) report.created.handle).resolve state.session.directory.path
        (successorPath state) report.openRead report.opened =
        .ok report.created.handle (state.cache, report.opened) := by
    simp only [Cache.resolve, separate, Bool.false_eq_true, ↓reduceIte]
    rw [show ((state.cache.remember (successorPath state) report.created.handle).pending.find?
          (fun entry => entry.1 == successorPath state)) = some (successorPath state, report.created.handle) by
      simp [Cache.remember, pushPending]]
    rw [consumed, report.pending]
  simp [sync, resolved, report.fileReturned, withCache]

theorem directoryGroup (report : NativeReadyCreatedRotation state) :
    report.group state.session.directory.path (state.cache, report.fileSynced) =
      .ok () (state.cache, report.directorySynced) := by
  unfold group
  rw [SyncPathGroup.run_single]
  simp [sync, Cache.resolve, report.cached, report.directoryReturned, withCache]

theorem publishes (report : NativeReadyCreatedRotation state) :
    WalSegmentRotation.runAt state.session.directory (state.writer.installed.walBytes / frameSize)
      report.readEmpty report.create report.group (state.cache, state.census, report.parent.files) =
      .ok () (state.cache, report.directorySynced) := by
  have created : report.create (successorPath state) (state.cache, state.census, report.parent.files) =
    .ok () (state.cache.remember (successorPath state) report.created.handle, report.opened) := by
    simp [create, successorPath, report.openReturned]
  rw [WalSegmentRotation.runAt_fileEffects]
  simp [WalSegmentRotation.observeSuccessorWith, report.readsAbsent, created, report.fileGroup,
    report.directoryGroup, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

theorem closesSuccessorSlot (report : NativeReadyCreatedRotation state) :
    report.fileSynced.1 = state.census.afterDrops (report.beforeFile ++ report.fileDrops ++ [report.created.raw.closeEvent]) ∧
    report.directorySynced.1.references report.created.raw.description = [] := by
  have closed :
      report.fileSynced.1 =
        state.census.afterDrops (report.beforeFile ++ report.fileDrops ++ [report.created.raw.closeEvent]) := by
    change ((state.census.insert report.created.raw report.created.free).afterDrops report.beforeFile).afterDrops
      (report.fileDrops ++ [report.created.raw.closeEvent]) = _
    rw [DescriptorInventory.afterDrops_append, ← List.append_assoc]
    exact DescriptorInventory.insert_thenClose _ _ _ _
  refine ⟨closed, ?_⟩
  change (report.fileSynced.1.afterDrops report.directoryDrops).references report.created.raw.description = []
  rw [DescriptorInventory.references_afterDrops, closed, DescriptorInventory.references_afterDrops, report.created.fresh]
  rfl

def run (report : NativeReadyCreatedRotation state) :=
  runObservedRotationWithReset state.session.directory report.lookup report.readEmpty report.create report.group
    releaseRotationActive (state.session.phase, ⟨(state.cache, state.census, report.parent.files), state.writer.owners⟩)

def next (report : NativeReadyCreatedRotation state) (valid : state.Valid) : NativeReadyState :=
  state.withRotatedWal valid (releaseRotationActive state.cache report.directorySynced).1

theorem returned (report : NativeReadyCreatedRotation state) (valid : state.Valid) :
    let next := report.next valid
    report.run = .ok () (next.session.phase, ⟨(next.cache, next.census, report.settled), next.writer.owners⟩) := by
  unfold run next NativeReadyState.withRotatedWal
  rw [valid.phase]
  exact runObservedRotationWithReset_ready state.session.directory state.writer.installed
    ⟨(state.cache, state.census, report.parent.files), state.writer.owners⟩
    report.lookup report.readEmpty report.create report.group releaseRotationActive
    report.parent.nonempty report.checked report.publishes

theorem validNext (report : NativeReadyCreatedRotation state) (valid : state.Valid) :
    (report.next valid).Valid :=
  report.reset.validNext valid report.parent.nonempty

theorem durableSuccessor (report : NativeReadyCreatedRotation state) :
    let name := renderWalSegmentName (state.writer.installed.walBytes / frameSize)
    report.settled.view.child report.parent.root name = some report.created.child.child ∧
    report.settled.crashNames name = [some report.created.child.child] ∧
    report.settled.view.modelObject report.created.child.child = state.census.inode report.created.raw.description ∧
    report.settled.inodes.crashBytes (state.census.inode report.created.raw.description) = [ByteArray.empty] := by
  have bound := report.created.child.binds
  rw [report.created.child.atRoot, report.created.child.atName] at bound
  exact ⟨(congrArg (fun view => view.child report.parent.root
      (renderWalSegmentName (state.writer.installed.walBytes / frameSize))) report.view).trans bound, report.successorSurvives,
    (congrArg (fun view => view.modelObject report.created.child.child) report.view).trans report.created.inode,
    (congrArg (fun image => image.crashBytes (state.census.inode report.created.raw.description)) report.bytes).trans
      report.created.syncedBytes⟩

theorem custody (report : NativeReadyCreatedRotation state) (valid : state.Valid) :
    let next := report.next valid
    report.directoryHandle.2.1 = state.directorySlot ∧
    next.census.inode = state.census.inode ∧
    report.settled.view.child report.parent.root "LOCK" = some report.parent.lock.child ∧
    report.settled.view.modelObject report.parent.lock.child = next.census.inode state.owner.description ∧
    next.census.references report.created.raw.description = [] ∧
    (∀ entry ∈ state.cache.active, entry.2.2.1 ∉ next.census.slots) := by
  obtain ⟨captured, known⟩ := valid.captured
  have same : report.directoryHandle = (captured, state.directorySlot, 0) :=
    Option.some.inj (report.cached.symm.trans known)
  obtain ⟨_, bound, lockObject, _⟩ := (RotationRawCreateEffect.afterOpen report.created).keepsLock
  have lock : report.settled.view.child report.parent.root "LOCK" = some report.parent.lock.child :=
    (congrArg (fun view => view.child report.parent.root "LOCK") report.view).trans bound
  have object : report.settled.view.modelObject report.parent.lock.child = (report.next valid).census.inode state.owner.description :=
    (congrArg (fun view => view.modelObject report.parent.lock.child) report.view).trans
      (lockObject.trans (congrArg (fun slot : DescriptorSlot => state.census.inode slot.description) report.parentOwner))
  refine ⟨congrArg (fun handle : RotationSuccessorHandle => handle.2.1) same, rfl, lock, object, ?_, ?_⟩
  · unfold next NativeReadyState.withRotatedWal releaseRotationActive
    rw [DescriptorInventory.references_afterDrops, report.closesSuccessorSlot.2]
    rfl
  · intro entry member
    exact releaseRotationActive_closes _ _ member

theorem keepsKeeperMarker (report : NativeReadyCreatedRotation state) :
    NativeRotationKeeperMarker state.writer report.parent.root report.settled
      report.parent.keeper.child report.parent.marker.child := by
  obtain ⟨objects, keeper, marker, _, _, _, keeperBytes, boundary, markerBytes⟩ :=
    (RotationRawCreateEffect.afterOpen (report.created.afterSync true)).keepsKeeperMarker
  have objects := (congrArg DirectoryReadNamespace.modelObject report.view).trans objects
  let payload := (report.created.afterSync true).files.inodes.visible (report.parent.files.view.modelObject report.parent.marker.child)
  refine ⟨(congrArg (fun view => view.child report.parent.root (renderWalSegmentName state.writer.installed.activeFirst))
      report.view).trans keeper,
    (congrArg (fun view => view.child report.parent.root "WAL.commit") report.view).trans marker,
    report.keeperSurvives.trans report.parent.keeperNameCrash, report.markerSurvives.trans report.parent.markerNameCrash,
    ?_, ⟨payload, boundary, ?_⟩⟩
  · rw [report.bytes, objects]
    exact keeperBytes
  · rw [report.bytes, objects]
    exact markerBytes

end NativeReadyCreatedRotation

/-- The usual exclusive-create rotation reports the same client
transition, with the new inode and the exact post-release census. -/
structure NativeCreatedRotationContinuation (current next : NativeReadPosition history log)
    (report : NativeReadyCreatedRotation current.state) : Prop where
  reached : next.state = report.next current.readPrefix.refines.1
  returned : report.run = .ok () (next.state.session.phase,
    ⟨(next.state.cache, next.state.census, report.settled), next.state.writer.owners⟩)
  frame : NativeRotationFrame current next
  successor : report.settled.view.child report.parent.root
    (renderWalSegmentName next.state.writer.wal.active.first) = some report.created.child.child
  successorCrash : report.settled.crashNames (renderWalSegmentName next.state.writer.wal.active.first) =
    [some report.created.child.child]
  successorObject : report.settled.view.modelObject report.created.child.child =
    next.state.census.inode report.created.raw.description
  successorBytes : report.settled.inodes.crashBytes
    (report.settled.view.modelObject report.created.child.child) = [next.state.writer.wal.active.bytes]
  keeperMarker : NativeRotationKeeperMarker current.state.writer report.parent.root report.settled
    report.parent.keeper.child report.parent.marker.child
  directorySlot : report.directoryHandle.2.1 = current.state.directorySlot
  lock : report.settled.view.child report.parent.root "LOCK" = some report.parent.lock.child
  lockObject : report.settled.view.modelObject report.parent.lock.child =
    next.state.census.inode current.state.owner.description
  temporaryClosed : next.state.census.references report.created.raw.description = []
  activeClosed : ∀ entry ∈ current.state.cache.active, entry.2.2.1 ∉ next.state.census.slots

theorem NativeReadPosition.rotatesCreated (current : NativeReadPosition history log)
    (report : NativeReadyCreatedRotation current.state) :
    ∃ next, NativeCreatedRotationContinuation current next report := by
  let valid := current.readPrefix.refines.1
  let state := report.next valid
  let next := current.afterRotation state.census (report.validNext valid)
  obtain ⟨successor, settled, successorObject, bytes⟩ := report.durableSuccessor
  obtain ⟨directory, sameInodes, lock, object, temporary, active⟩ := report.custody valid
  have atEnd : state.writer.wal.active.first = current.state.writer.installed.walBytes / frameSize :=
    valid.retained.layout.activeEnd.trans valid.retained.rotationAtEnd.symm
  refine ⟨next, rfl, report.returned valid, current.rotationFrame _ _, atEnd.symm ▸ successor, atEnd.symm ▸ settled,
    successorObject.trans (congrFun sameInodes report.created.raw.description).symm, ?_, report.keepsKeeperMarker, directory, lock, object,
    temporary, active⟩
  rw [successorObject]
  exact bytes

/-- An empty keeper skips the guard, successor operations, and cache
retirement at the reached ready state. There is no new ledger entry. -/
theorem NativeReadPosition.rotatesEmpty (current : NativeReadPosition history log)
    (empty : current.state.writer.installed.walBytes / frameSize ≤ current.state.writer.installed.activeFirst)
    (files : RotationCreateFiles) (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    (read : FilePath → EStateM IO.Error (CensusDirectoryCache × Files) (Option ByteArray))
    (create sync : FilePath → EStateM IO.Error (CensusDirectoryCache × Files) Unit) :
    let before := (current.state.session.phase,
      ⟨(current.state.cache, current.state.census, files), current.state.writer.owners⟩)
    runObservedRotationWithReset current.state.session.directory lookup read create sync releaseRotationActive before =
      .ok () before := by
  intro before
  have phase := current.readPrefix.refines.1.phase
  dsimp only [before]
  rw [phase]
  exact runObservedRotationWithReset_empty _ _ _ lookup read create sync releaseRotationActive empty

end Alvoki.Storage.DiskSession
