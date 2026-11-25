import Alvoki.Storage.Disk.CachedWalChunkReports
import Alvoki.Storage.Disk.CheckedDirectoryRead
import Alvoki.Storage.Disk.DiskOpenAdmission

namespace Alvoki.Storage.DiskSession

open System Manifest SyncHandleRouting WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

/-- Native object identity in the owned namespace during one read-only open
prefix. An inode number alone can coincide on different devices. -/
structure DeviceInode where
  device : UInt64
  inode : UInt64

/-- Stable child bindings of the captured directory during the read-only
prefix. The observer supplies object identities and the complete names of
this directory, excluding the dot entries. -/
structure DirectoryReadNamespace where
  modelObject : DeviceInode → Nat
  names : DeviceInode → List String
  child : DeviceInode → String → Option DeviceInode
  namesExact : ∀ root name, name ∈ names root ↔ ∃ object, child root name = some object

/-- The private lock and cached directory slots survive all observed
reference drops from cache capture through the listing close. The drop
report uses the existing complete-inventory contract, including the
exclusion of an independent explicit unlock. -/
structure HeldDirectoryReadLifetime (initial : DescriptorInventory) (owner : DescriptorSlot) where
  namespaceView : DirectoryReadNamespace
  directorySlot : DescriptorSlot
  root : DeviceInode
  lock : DeviceInode
  identifiesDirectory : namespaceView.modelObject root = initial.inode directorySlot.description
  identifiesLock : namespaceView.modelObject lock = initial.inode owner.description
  drops : List LockReferenceDrop
  ownerRetained : owner ∈ (initial.afterDrops drops).slots
  directoryRetained : directorySlot ∈ (initial.afterDrops drops).slots
  lockEntry : namespaceView.child root "LOCK" = some lock

private theorem slotLiveAtPrefix {initial : DescriptorInventory} {slot : DescriptorSlot}
    {earlier rest : List LockReferenceDrop} (live : slot ∈ (initial.afterDrops (earlier ++ rest)).slots) :
    slot ∈ (initial.afterDrops earlier).slots := by
  obtain ⟨original, kept⟩ := List.mem_filter.mp live
  rw [List.all_eq_true] at kept
  exact List.mem_filter.mpr ⟨original, List.all_eq_true.mpr fun event occurred =>
    kept event (List.mem_append_left _ occurred)⟩

theorem HeldDirectoryReadLifetime.liveAtPrefix {initial owner} (lifetime : HeldDirectoryReadLifetime initial owner)
    {earlier rest : List LockReferenceDrop} (reached : lifetime.drops = earlier ++ rest) :
    owner ∈ (initial.afterDrops earlier).slots ∧ lifetime.directorySlot ∈ (initial.afterDrops earlier).slots :=
  ⟨slotLiveAtPrefix (reached ▸ lifetime.ownerRetained), slotLiveAtPrefix (reached ▸ lifetime.directoryRetained)⟩

def DescriptorSlot.closeEvent (slot : DescriptorSlot) : LockReferenceDrop :=
  .closed slot.reference.process slot.reference.fd

/-- The checked listing's `opendir` inserts a fresh private descriptor
after the preceding checkpoint reads. Its `readdir` reports use this same
stream, and successful `closedir` drops exactly its issuing slot. The
census tracks the originally held slots and this stream. Other temporary
file opens supply their own descriptor reports. -/
structure HeldDirectoryScan {initial owner} (lifetime : HeldDirectoryReadLifetime initial owner) where
  beforeOpen : List LockReferenceDrop
  stream : DescriptorSlot
  free : ∀ slot ∈ (initial.afterDrops beforeOpen).slots, slot.address ≠ stream.address
  fresh : (initial.afterDrops beforeOpen).references stream.description = []
  directoryObject : DeviceInode
  identifiesStream : lifetime.namespaceView.modelObject directoryObject = initial.inode stream.description
  duringScan : List LockReferenceDrop
  live : ∀ event ∈ duringScan, event.removes stream.reference = false
  drops : lifetime.drops = beforeOpen ++ duringScan ++ [stream.closeEvent]
  sameRoot : directoryObject = lifetime.root
  scan : OpenedDirectoryScan
  eof : scan.terminal = .ok ()
  closed : scan.closed = .ok ()
  complete : scan.visibleNames.Perm (lifetime.namespaceView.names directoryObject)

def HeldDirectoryScan.opened {initial owner} {lifetime : HeldDirectoryReadLifetime initial owner}
    (report : HeldDirectoryScan lifetime) : DescriptorInventory :=
  (initial.afterDrops report.beforeOpen).insert report.stream report.free

def HeldDirectoryScan.afterClose {initial owner} {lifetime : HeldDirectoryReadLifetime initial owner}
    (report : HeldDirectoryScan lifetime) : DescriptorInventory :=
  (report.opened.afterDrops report.duringScan).afterDrops [report.stream.closeEvent]

theorem DescriptorInventory.afterDrops_append (inventory : DescriptorInventory)
    (earlier later : List LockReferenceDrop) :
    (inventory.afterDrops earlier).afterDrops later = inventory.afterDrops (earlier ++ later) := by
  cases inventory
  simp [DescriptorInventory.afterDrops, List.all_append, List.filter_filter, Bool.and_comm]

theorem DescriptorInventory.insert_thenClose (beforeOpen : DescriptorInventory)
    (stream : DescriptorSlot) (free : ∀ slot ∈ beforeOpen.slots, slot.address ≠ stream.address)
    (duringScan : List LockReferenceDrop) :
    (beforeOpen.insert stream free).afterDrops (duringScan ++ [stream.closeEvent]) =
      beforeOpen.afterDrops (duringScan ++ [stream.closeEvent]) := by
  cases beforeOpen with
  | mk slots distinct inode =>
    simp [DescriptorInventory.insert, DescriptorInventory.afterDrops, DescriptorSlot.closeEvent,
      LockReferenceDrop.removes, List.all_append]

theorem HeldDirectoryScan.afterClose_eq {initial owner} {lifetime : HeldDirectoryReadLifetime initial owner}
    (report : HeldDirectoryScan lifetime) : report.afterClose = initial.afterDrops lifetime.drops := by
  rw [afterClose, DescriptorInventory.afterDrops_append report.opened, report.drops, List.append_assoc,
    ← DescriptorInventory.afterDrops_append initial report.beforeOpen]
  exact DescriptorInventory.insert_thenClose _ report.stream report.free report.duringScan

theorem DescriptorInventory.closeOtherSlot {inventory : DescriptorInventory}
    {slot temporary : DescriptorSlot} (present : slot ∈ inventory.slots)
    (free : ∀ existing ∈ inventory.slots, existing.address ≠ temporary.address) :
    temporary.closeEvent.removes slot.reference = false := by
  cases removed : temporary.closeEvent.removes slot.reference with
  | false => rfl
  | true =>
    exfalso
    apply free slot present
    simpa [DescriptorSlot.address, DescriptorSlot.closeEvent, LockReferenceDrop.removes,
      Bool.and_eq_true, beq_iff_eq, Prod.mk.injEq] using removed

/-- A held descriptor survives the checked scan when reported ambient
drops preserve it. The stream's own finalizer has a different address. -/
theorem HeldDirectoryScan.preservesSlot {initial owner} {lifetime : HeldDirectoryReadLifetime initial owner}
    (report : HeldDirectoryScan lifetime) {slot : DescriptorSlot} (present : slot ∈ initial.slots)
    (retained : ∀ event ∈ report.beforeOpen ++ report.duringScan, event.removes slot.reference = false) :
    slot ∈ report.afterClose.slots := by
  have atOpen : slot ∈ (initial.afterDrops report.beforeOpen).slots :=
    List.mem_filter.mpr ⟨present, List.all_eq_true.mpr fun event member => by
      simp [retained event (List.mem_append_left _ member)]⟩
  have finalizer := DescriptorInventory.closeOtherSlot atOpen report.free
  rw [report.afterClose_eq, report.drops]
  refine List.mem_filter.mpr ⟨present, List.all_eq_true.mpr ?_⟩
  intro event member
  rcases List.mem_append.mp member with ambient | closing
  · simp [retained event ambient]
  · simp [List.mem_singleton.mp closing, finalizer]

theorem HeldDirectoryScan.liveAtRead {initial owner} {lifetime : HeldDirectoryReadLifetime initial owner}
    (report : HeldDirectoryScan lifetime) {earlier rest : List LockReferenceDrop}
    (readAt : report.duringScan = earlier ++ rest) :
    let atRead := report.opened.afterDrops earlier
    report.stream ∈ atRead.slots ∧ owner ∈ atRead.slots ∧ lifetime.directorySlot ∈ atRead.slots := by
  have drops : lifetime.drops = (report.beforeOpen ++ earlier) ++ (rest ++ [report.stream.closeEvent]) := by
    rw [report.drops, readAt]
    simp only [List.append_assoc]
  obtain ⟨lock, directory⟩ := lifetime.liveAtPrefix drops
  rw [← DescriptorInventory.afterDrops_append] at lock directory
  have insertKeeps {slot : DescriptorSlot}
      (kept : slot ∈ ((initial.afterDrops report.beforeOpen).afterDrops earlier).slots) :
      slot ∈ (report.opened.afterDrops earlier).slots := by
    obtain ⟨existing, survived⟩ := List.mem_filter.mp kept
    exact List.mem_filter.mpr ⟨List.mem_cons_of_mem _ existing, survived⟩
  refine ⟨List.mem_filter.mpr ⟨List.mem_cons_self, List.all_eq_true.mpr ?_⟩,
    insertKeeps lock, insertKeeps directory⟩
  intro event occurred
  have inScan : event ∈ report.duringScan := readAt ▸ List.mem_append_left _ occurred
  simp [report.live event inScan]

theorem HeldDirectoryScan.closedDescription {initial owner} {lifetime : HeldDirectoryReadLifetime initial owner}
    (report : HeldDirectoryScan lifetime) : report.afterClose.references report.stream.description = [] := by
  rw [report.afterClose_eq, report.drops, List.append_assoc, ← DescriptorInventory.afterDrops_append,
    DescriptorInventory.references_afterDrops, report.fresh]
  rfl

/-- Exact descriptor custody while issuing readdir and after closedir. -/
structure HeldDirectoryScan.Custody {initial owner} {lifetime : HeldDirectoryReadLifetime initial owner}
    (report : HeldDirectoryScan lifetime) : Prop where
  liveDuring : ∀ earlier rest, report.duringScan = earlier ++ rest →
    let atRead := report.opened.afterDrops earlier
    report.stream ∈ atRead.slots ∧ owner ∈ atRead.slots ∧ lifetime.directorySlot ∈ atRead.slots
  reached : report.afterClose = initial.afterDrops lifetime.drops
  streamClosed : report.afterClose.references report.stream.description = []
  lockRetained : owner ∈ report.afterClose.slots
  cacheRetained : lifetime.directorySlot ∈ report.afterClose.slots

theorem HeldDirectoryScan.custody {initial owner} {lifetime : HeldDirectoryReadLifetime initial owner}
    (report : HeldDirectoryScan lifetime) : report.Custody :=
  ⟨fun _ _ => report.liveAtRead, report.afterClose_eq, report.closedDescription,
    report.afterClose_eq ▸ lifetime.ownerRetained, report.afterClose_eq ▸ lifetime.directoryRetained⟩

theorem HeldDirectoryScan.sameDirectoryObject {initial owner} {lifetime : HeldDirectoryReadLifetime initial owner}
    (report : HeldDirectoryScan lifetime) :
    report.opened.inode report.stream.description = initial.inode lifetime.directorySlot.description := by
  change initial.inode report.stream.description = initial.inode lifetime.directorySlot.description
  rw [← report.identifiesStream, report.sameRoot, lifetime.identifiesDirectory]

/-- Native resolution of an absolute child path at one operation. Stat
and open resolve the parent independently in the current adapter. -/
structure RunChildLookup (root : DeviceInode) (name : String) (view : DirectoryReadNamespace) where
  parent : DeviceInode
  basename : String
  child : DeviceInode
  atRoot : parent = root
  atName : basename = name
  binds : view.child parent basename = some child

theorem RunChildLookup.child_eq {root name view} (lookup : RunChildLookup root name view)
    {object : DeviceInode} (bound : view.child root name = some object) : lookup.child = object := by
  have actual := lookup.binds
  rw [lookup.atRoot, lookup.atName] at actual
  exact Option.some.inj (actual.symm.trans bound)

/-- The per-run stat and open results and their actual path resolutions.
The observed reads of the opened description use the existing exact
position, contents and availability reports. -/
structure RunChunkPathReport (reads : CheckpointRunChunkReads) (path : FilePath) (name : String)
    (root : DeviceInode) (view : DirectoryReadNamespace) where
  metadata : IO.FS.Metadata
  statObject : Nat
  inventory : DescriptorInventory
  slot : DescriptorSlot
  statLookup : RunChildLookup root name view
  openLookup : RunChildLookup root name view
  stat : reads.stat path = .ok (metadata, statObject)
  identifiedStat : view.modelObject statLookup.child = statObject
  opened : reads.openRead path = .ok (inventory, slot, 0)
  identifiedOpen : view.modelObject openLookup.child = inventory.inode slot.description
  live : slot ∈ inventory.slots
  regular : metadata.type = .file
  extent : ∀ bytes, reads.objectBytes statObject = some bytes → metadata.byteSize.toNat = bytes.size
  observes : ∀ source, reads.objectBytes (inventory.inode slot.description) = some source →
    PrefixChunkObserves source (reads.readChunk slot.description)
  healthy : ∀ source, reads.objectBytes (inventory.inode slot.description) = some source →
    PrefixChunksAvailable source (reads.readChunk slot.description)

def RunChunkPathReport.observesFile {reads path name root view}
    (report : RunChunkPathReport reads path name root view) {object : DeviceInode} {bytes : ByteArray}
    (bound : view.child root name = some object)
    (contents : reads.objectBytes (view.modelObject object) = some bytes) : reads.ObservesFile path bytes := by
  have statObject : view.modelObject object = report.statObject :=
    (congrArg view.modelObject (report.statLookup.child_eq bound)).symm.trans report.identifiedStat
  have openedObject : view.modelObject object = report.inventory.inode report.slot.description :=
    (congrArg view.modelObject (report.openLookup.child_eq bound)).symm.trans report.identifiedOpen
  have statContents : reads.objectBytes report.statObject = some bytes := statObject ▸ contents
  exact ⟨report.metadata, report.statObject, report.inventory, report.slot,
    report.stat, report.regular, report.extent bytes statContents, report.opened, report.live,
    openedObject.symm.trans statObject, statContents, report.observes, report.healthy⟩

/-- Pair the primitive reports with the actual callbacks of one marked open.
The adapter opens the cache first, acquires the checkpoint runs, then lists
the directory on its separate stream. The directory remains under engine
control throughout. Its identity and the child resolutions are observations
of the actual calls. Their returned Lean values alone do not expose them. -/
structure HeldDirectoryMarkedRetryReports {directory : DiskDirectory}
    {before : LockedFileState FileImage} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout before.image history}
    (operations : MarkedRetryChunkOperations (Cache (DescriptorInventory × DescriptorSlot × Nat)) directory layout)
    (published : CheckpointPublication.Image) where
  lifetime : HeldDirectoryReadLifetime operations.descriptors operations.slot
  captured : operations.cache = ⟨some (operations.descriptors, lifetime.directorySlot, 0), none, []⟩
  listing : HeldDirectoryScan lifetime
  listed : operations.reported.list directory.path =
    (CheckedDirectoryReadReport.scanned listing.scan).result directory.path
  runs : ∀ bytes manifest, before.image.directory.active.manifest = some bytes →
    IntegrityCheckpoint.decode bytes = .ok manifest → ∀ index, index < manifest.header.runCount.toNat →
    RunChunkPathReport operations.reads (directory.file (.run manifest.header.generation index))
      (renderRunFileName manifest.header.generation index) lifetime.root lifetime.namespaceView
  publishedBytes : ∀ bytes manifest, before.image.directory.active.manifest = some bytes →
    IntegrityCheckpoint.decode bytes = .ok manifest → ∀ index, index < manifest.header.runCount.toNat → ∀ payload,
    published.durable manifest.header.generation index = some payload →
    ∃ object, lifetime.namespaceView.child lifetime.root (renderRunFileName manifest.header.generation index) =
      some object ∧ operations.reads.objectBytes (lifetime.namespaceView.modelObject object) = some payload

namespace HeldDirectoryMarkedRetryReports

variable {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout before.image history}
  {operations : MarkedRetryChunkOperations (Cache (DescriptorInventory × DescriptorSlot × Nat)) directory layout}
  {published : CheckpointPublication.Image}

theorem capturedDirectory (report : HeldDirectoryMarkedRetryReports operations published) :
    operations.cache.directory = some (operations.descriptors, report.lifetime.directorySlot, 0) := by
  rw [report.captured]

theorem initializedCache (report : HeldDirectoryMarkedRetryReports operations published) :
    operations.openFiles before.image =
      .ok ⟨some (operations.descriptors, report.lifetime.directorySlot, 0), none, []⟩ before.image := by
  rw [operations.initialized, report.captured]

theorem checkedListing (report : HeldDirectoryMarkedRetryReports operations published) :
    operations.reported.entries = report.listing.scan.entries directory.path ∧
    operations.reported.inventory.names.Perm (report.lifetime.namespaceView.names report.lifetime.root) := by
  obtain ⟨listed, names⟩ := CheckedDirectoryReadReport.scan_complete directory.path
    report.listing.eof report.listing.closed report.listing.complete
  have entries : operations.reported.entries = report.listing.scan.entries directory.path :=
    Except.ok.inj (operations.reported.listed.symm.trans (report.listed.trans listed))
  refine ⟨entries, ?_⟩
  rw [← operations.reported.names, entries]
  simpa only [report.listing.sameRoot] using names

theorem lockedEntry (report : HeldDirectoryMarkedRetryReports operations published) :
    ∃ object, report.lifetime.namespaceView.child report.lifetime.root "LOCK" = some object ∧
      operations.bindings (directory.file .lock) = some (report.lifetime.namespaceView.modelObject object) := by
  refine ⟨report.lifetime.lock, report.lifetime.lockEntry, ?_⟩
  rw [report.lifetime.identifiesLock, operations.lockObject]

theorem chunkReads (report : HeldDirectoryMarkedRetryReports operations published) :
    operations.reads.ObservesSelected directory before.image.directory.active.manifest published.durable := by
  intro bytes manifest visible decoded index within payload stored
  obtain ⟨object, bound, contents⟩ := report.publishedBytes bytes manifest visible decoded index within payload stored
  exact ⟨(report.runs bytes manifest visible decoded index within).observesFile bound contents⟩

def toChunkReports (report : HeldDirectoryMarkedRetryReports operations published)
    (settles : operations.sync operations.cache #[directory.path] before.image = .ok () before.image.syncDirectory)
    (metadataReads : operations.MarkedMetadata) (healthy : operations.HealthyFinish) :
    MarkedRetryChunkReports (Cache (DescriptorInventory × DescriptorSlot × Nat)) directory layout published where
  toMarkedRetryChunkOperations := operations
  metadataReads := metadataReads
  settles := settles
  healthy := healthy
  chunks := report.chunkReads

/-- The selected checkpoint files occur in the exact WAL listing from the
same directory. The later listing corroborates the earlier run resolutions. -/
theorem selectedRunListed (report : HeldDirectoryMarkedRetryReports operations published)
    {bytes manifest index payload} (visible : before.image.directory.active.manifest = some bytes)
    (decoded : IntegrityCheckpoint.decode bytes = .ok manifest) (within : index < manifest.header.runCount.toNat)
    (stored : published.durable manifest.header.generation index = some payload) :
    renderRunFileName manifest.header.generation index ∈ operations.reported.inventory.names := by
  obtain ⟨object, bound, _⟩ := report.publishedBytes bytes manifest visible decoded index within payload stored
  exact report.checkedListing.2.mem_iff.mpr ((report.lifetime.namespaceView.namesExact _ _).mpr ⟨object, bound⟩)

/-- Continue the same descriptor history past closedir to the first
directory barrier. A local observation still supplies the effect-time
binding of the canonical path and the returned syscall effect. -/
def directoryBarrier (report : HeldDirectoryMarkedRetryReports operations published)
    (afterListing : List LockReferenceDrop)
    (retained : report.lifetime.directorySlot ∈ (report.listing.afterClose.afterDrops afterListing).slots)
    (bindings : FilePath → Option Nat)
    (bound : bindings directory.path = some (report.lifetime.namespaceView.modelObject report.lifetime.root))
    (outcome : DelayedDirectorySyncOutcome) : DelayedDirectorySync directory :=
  operations.descriptors.delayedDirectorySync (report.lifetime.drops ++ afterListing) directory
    report.lifetime.directorySlot.description report.lifetime.directorySlot.reference
    (by
      rw [← DescriptorInventory.afterDrops_append, ← report.listing.afterClose_eq]
      exact (report.listing.afterClose.afterDrops afterListing).mem_references.mpr ⟨_, retained, rfl, rfl⟩)
    bindings (by rwa [report.lifetime.identifiesDirectory] at bound) outcome

/-- The keeper read may add a pending handle, but the shared sync selector
still sends the captured directory handle to the first barrier. A reported
failure carries the cache and the reached directory effect. -/
theorem keeperRead_syncListedDirectory (report : HeldDirectoryMarkedRetryReports operations published)
    (seen : operations.reads.ObservesFile (directory.file (.walSegment layout.keeper.first))
      (layout.keeper.bytes ++ layout.tail)) (fits : layout.keeper.bytes.size < USize.size)
    (afterListing : List LockReferenceDrop)
    (retained : report.lifetime.directorySlot ∈ (report.listing.afterClose.afterDrops afterListing).slots)
    (bindings : FilePath → Option Nat)
    (bound : bindings directory.path = some (report.lifetime.namespaceView.modelObject report.lifetime.root))
    (outcome : DelayedDirectorySyncOutcome) (initial : LockedFileState FileImage)
    (openRead : FilePath → EStateM IO.Error (LockedFileState FileImage) (DescriptorInventory × DescriptorSlot × Nat))
    (fsync : (DescriptorInventory × DescriptorSlot × Nat) → EStateM IO.Error (LockedFileState FileImage) Unit)
    (effect : fsync (operations.descriptors, report.lifetime.directorySlot, 0) initial =
      (report.directoryBarrier afterListing retained bindings bound outcome).run initial) :
    let path := directory.file (.walSegment layout.keeper.first)
    let reached := operations.cache.captureKeeper path (seen.inventory, seen.slot, 0)
      layout.keeper.bytes.size seen.metadata.byteSize.toNat
    readWalKeeperWithChunks operations.reads path layout.keeper.bytes.size seen.metadata.byteSize.toNat
      (operations.cache, initial) = .ok layout.keeper.bytes (reached, initial) ∧
    sync directory.path openRead fsync directory.path (reached, initial) =
      withCache reached ((report.directoryBarrier afterListing retained bindings bound outcome).run initial) := by
  intro path reached
  refine ⟨readWalKeeperWithChunks_exact seen fits operations.cache initial, ?_⟩
  have directoryHandle : reached.directory = some (operations.descriptors, report.lifetime.directorySlot, 0) := by
    simp only [reached, Cache.captureKeeper]
    split <;> exact report.capturedDirectory
  simp [SyncHandleRouting.sync, Cache.resolve, directoryHandle, effect]

/-- The admitted marked open now takes its selected checkpoint reports from
the same observed directory lifetime as the checked listing. -/
theorem installs {input : FilePath} (report : HeldDirectoryMarkedRetryReports operations published)
    (settles : operations.sync operations.cache #[directory.path] before.image = .ok () before.image.syncDirectory)
    (metadataReads : operations.MarkedMetadata) (healthy : operations.HealthyFinish)
    (admission : OpenAdmissionReports input directory operations.slot)
    (keeperValid : before.image.keeper.Valid layout.target.Accepts)
    (laterValid : before.image.later.Beyond layout.range.through)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      before.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history) :
    operations.openFiles before.image =
      .ok ⟨some (operations.descriptors, report.lifetime.directorySlot, 0), none, []⟩ before.image ∧
    report.listing.Custody ∧
    operations.reported.entries = report.listing.scan.entries directory.path ∧
    operations.reported.inventory.names.Perm (report.lifetime.namespaceView.names report.lifetime.root) ∧
    CachedRetryInstalled (before := before) operations.reported operations.descriptors operations.slot operations.bindings
      published operations.liveRefs ((report.toChunkReports settles metadataReads healthy).runWithAdmission admission) :=
  ⟨report.initializedCache, report.listing.custody, report.checkedListing.1, report.checkedListing.2,
    runOpenWithAdmission_markedRetryFromChunks (report.toChunkReports settles metadataReads healthy) admission keeperValid laterValid
      following accepted ordered⟩

end HeldDirectoryMarkedRetryReports
end Alvoki.Storage.DiskSession
