import Alvoki.Storage.Disk.LockCensusOpenAdmission
import Alvoki.Storage.Disk.Proofs.Recovery.HeldMetadataReadObservations
import Alvoki.Storage.Disk.Proofs.Recovery.HeldWalPayloadObservations
import Alvoki.Storage.Disk.WalSegmentCachedRetryCompletion

namespace Alvoki.Storage.DiskSession

open System Manifest SyncHandleRouting WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}

namespace CensusOpenAdmissionReports

/-- Read the native flat-WAL and marker guards before choosing the reached
marked opener or markerless bootstrap. Both use the same held admission. -/
def recoverWithMarked (admission : CensusOpenAdmissionReports input directory inventory retry)
    (resolved : DiskDirectory) (marked bootstrap : EStateM IO.Error CensusOpenState Reopened) :
    EStateM IO.Error CensusOpenState Reopened :=
  recoverSegmentedWalWith
    (rejectFlatWalWith resolved (optionalMetadataWith (admission.lookup (resolved.file .wal))))
    (optionalMetadataWith (admission.lookup (resolved.file .walBoundary))) marked bootstrap

/-- The reached guard and marker probe select the worker before either
worker has returned. Both choices start in the same held state. -/
theorem recoverWithMarked_selects (admission : CensusOpenAdmissionReports input directory inventory retry)
    {marked bootstrap : EStateM IO.Error CensusOpenState Reopened} {marker : Option IO.FS.Metadata}
    (flat : optionalMetadataWith (admission.lookup (directory.file .wal)) (admission.reached, admission.held) =
      .ok none (admission.reached, admission.held))
    (found : optionalMetadataWith (admission.lookup (directory.file .walBoundary)) (admission.reached, admission.held) =
      .ok marker (admission.reached, admission.held)) :
    admission.recoverWithMarked directory marked bootstrap (admission.reached, admission.held) =
      (if marker.isSome then marked else bootstrap) (admission.reached, admission.held) := by
  simp only [recoverWithMarked, recoverSegmentedWalWith, rejectFlatWalWith, Bind.bind, EStateM.bind,
    flat, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Pure.pure, EStateM.pure, found]

/-- The original cache capture supplies the directory identity. The read
report supplies the canonical lock child and the intervening slot drops. -/
def readLifetime (admission : CensusOpenAdmissionReports input directory inventory retry)
    (lock : DeviceInode) (bound : admission.view.child admission.root "LOCK" = some lock)
    (identified : admission.view.modelObject lock = admission.reached.inode admission.owner.description)
    (drops : List LockReferenceDrop)
    (ownerRetained : admission.owner ∈ (admission.reached.afterDrops drops).slots)
    (directoryRetained : admission.cached ∈ (admission.reached.afterDrops drops).slots) :
    HeldDirectoryReadLifetime admission.reached admission.owner where
  namespaceView := admission.view
  directorySlot := admission.cached
  root := admission.root
  lock := lock
  identifiesDirectory := admission.opened.captures.2.2.2.2.1
  identifiesLock := identified
  drops := drops
  ownerRetained := ownerRetained
  directoryRetained := directoryRetained
  lockEntry := bound

end CensusOpenAdmissionReports

/-- The read-side reports start at the census produced by the actual
append-open, acquisition and cache initialization. The stream and every
selected stat and open resolve in that capture's same canonical namespace. -/
structure CapturedMarkedReadReports (admission : CensusOpenAdmissionReports input directory inventory retry)
    {history : List WAL.Write} (layout : CanonicalKeeperLayout retry.image history)
    (published : CheckpointPublication.Image) where
  lock : DeviceInode
  lockEntry : admission.view.child admission.root "LOCK" = some lock
  identifiesLock : admission.view.modelObject lock = admission.reached.inode admission.owner.description
  bindings : FilePath → Option Nat
  canonicalDirectory : bindings directory.path = some (admission.view.modelObject admission.root)
  canonicalLock : bindings (directory.file .lock) = some (admission.view.modelObject lock)
  drops : List LockReferenceDrop
  ownerRetained : admission.owner ∈ (admission.reached.afterDrops drops).slots
  directoryRetained : admission.cached ∈ (admission.reached.afterDrops drops).slots
  listing : HeldDirectoryScan
    (admission.readLifetime lock lockEntry identifiesLock drops ownerRetained directoryRetained)
  catalog : CachedRetryReadInventory directory layout
  listed : catalog.list directory.path = (CheckedDirectoryReadReport.scanned listing.scan).result directory.path
  reads : CheckpointRunChunkReads
  stat : ∀ path, catalog.inventory.reports.lstat path = (reads.stat path).map Prod.fst
  metadata : DirectoryMetadataReadReports directory admission.view admission.root reads
    catalog.inventory.reports.readOptional retry.image.directory.active
  runs : ∀ bytes manifest, retry.image.directory.active.manifest = some bytes →
    IntegrityCheckpoint.decode bytes = .ok manifest → ∀ index, index < manifest.header.runCount.toNat →
    ∀ payload, published.durable manifest.header.generation index = some payload →
    ∃ object,
      admission.view.child admission.root (renderRunFileName manifest.header.generation index) = some object ∧
      reads.objectBytes (admission.view.modelObject object) = some payload ∧
      Nonempty (RunChunkPathReport reads (directory.file (.run manifest.header.generation index))
        (renderRunFileName manifest.header.generation index) admission.root admission.view)
  wal : HeldWalPayloadReports directory layout reads admission.view admission.root

namespace CapturedMarkedReadReports

variable {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {published : CheckpointPublication.Image}

def lifetime (report : CapturedMarkedReadReports admission layout published) :
    HeldDirectoryReadLifetime admission.reached admission.owner :=
  admission.readLifetime report.lock report.lockEntry report.identifiesLock report.drops report.ownerRetained
    report.directoryRetained

/-- The locked catalog uses the owner installed by this very admission.
Only the entries and metadata are taken from the catalog report. -/
def inventoryWithOwner (report : CapturedMarkedReadReports admission layout published) :
    CachedRetryReadInventory directory layout :=
  { report.catalog with
    inventory :=
      { report.catalog.inventory with
        owners := admission.held.owners
        descriptor := admission.owner.description
        held := admission.opened.held } }

def walReads (report : CapturedMarkedReadReports admission layout published) :
    CachedRetryReadReports directory layout :=
  report.wal.toCachedReads report.inventoryWithOwner report.stat

theorem sameObjects (report : CapturedMarkedReadReports admission layout published) :
    report.bindings directory.path = some (admission.reached.inode admission.cached.description) ∧
    report.bindings (directory.file .lock) = some (admission.reached.inode admission.owner.description) ∧
    report.catalog.inventory.names.Perm (admission.view.names admission.root) ∧ report.listing.Custody := by
  obtain ⟨returned, names⟩ := CheckedDirectoryReadReport.scan_complete directory.path
    report.listing.eof report.listing.closed report.listing.complete
  have listed := Except.ok.inj (report.catalog.listed.symm.trans (report.listed.trans returned))
  refine ⟨?_, ?_, ?_, report.listing.custody⟩
  · exact report.canonicalDirectory.trans (congrArg some report.lifetime.identifiesDirectory)
  · rw [report.canonicalLock, report.identifiesLock]
  · have root : report.listing.directoryObject = admission.root := report.listing.sameRoot
    rw [← report.catalog.names, listed, ← root]
    exact names

theorem chunkReads (report : CapturedMarkedReadReports admission layout published) :
    report.reads.ObservesSelected directory retry.image.directory.active.manifest published.durable := by
  intro bytes manifest visible decoded index within payload stored
  obtain ⟨_, bound, contents, ⟨call⟩⟩ := report.runs bytes manifest visible decoded index within payload stored
  exact ⟨call.observesFile bound contents⟩

/-- The read-only worker uses the same selected run, seal and keeper
callbacks as the native cached preparation. It leaves its input census
and files unchanged in this projection, before repair. -/
theorem prepares (report : CapturedMarkedReadReports admission layout published)
    (laterValid : retry.image.later.Beyond layout.range.through)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history) :
    ∃ opened checkpoint,
      report.walReads.prepare report.reads.readPrefix (admission.reached, admission.held) =
        .ok (layout.boundedPlan, opened, layout.plan.keeperBytes.size) (admission.reached, admission.held) ∧
      SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint ∧
      recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode history) = .ok opened.table := by
  obtain ⟨watermark, _, _, count, _, _, absolute⟩ := DirectoryPublication.Bindings.walRange_accounting layout.decoded
  have byteCount : (WAL.encode history).size = count.toNat := by
    rw [absolute, layout.through, WAL.encode_size, Nat.mul_comm]
  obtain ⟨checkpoint, _, _, selected, _, _, _, _, _, _⟩ :=
    selectedCheckpoint_replays watermark accepted (byteCount ▸ count.toNat_lt_size) ordered
  let sizes := SizedCheckpointRunReports.ofChunkReads (checkpoint := checkpoint) selected report.reads
    report.stat report.chunkReads
  obtain ⟨opened, selected, _, prepared, exactCheckpoint, replay, _⟩ :=
    report.walReads.prepares (admission.reached, admission.held) laterValid following accepted ordered sizes
      (report.metadata.manifestRead layout.decoded) (report.metadata.markerRead layout.decoded)
  exact ⟨opened, selected, prepared, exactCheckpoint, replay⟩

/-- Project the held route checks and the cached marked worker through its
read-only preparation. The continuation represents the still-unknown
repair and installation, and takes the original cache argument. -/
def recoverThroughReads (report : CapturedMarkedReadReports admission layout published)
    (finish : DiskDirectory → DescriptorSlot → CensusDirectoryCache → Plan × Reopened × Nat →
      EStateM IO.Error CensusOpenState Reopened)
    (bootstrap : DiskDirectory → CensusDirectoryCache → EStateM IO.Error CensusOpenState Reopened)
    (resolved : DiskDirectory) (owner : DescriptorSlot) (cache : CensusDirectoryCache) :
    EStateM IO.Error CensusOpenState Reopened :=
  admission.recoverWithMarked resolved
    (report.walReads.prepare report.reads.readPrefix >>= finish resolved owner cache)
    (bootstrap resolved cache)

/-- The held lookups and selected read result determine which continuation
the shared recovery schedule calls. -/
theorem recoverThroughReads_prepared (report : CapturedMarkedReadReports admission layout published)
    (flat : optionalMetadataWith (admission.lookup (directory.file .wal)) (admission.reached, admission.held) =
      .ok none (admission.reached, admission.held))
    {metadata : IO.FS.Metadata}
    (marker : admission.lookup (directory.file .walBoundary) (admission.reached, admission.held) =
      .ok (.ok metadata) (admission.reached, admission.held))
    {prepared : Plan × Reopened × Nat}
    (read : report.walReads.prepare report.reads.readPrefix (admission.reached, admission.held) =
      .ok prepared (admission.reached, admission.held))
    (finish : DiskDirectory → DescriptorSlot → CensusDirectoryCache → Plan × Reopened × Nat →
      EStateM IO.Error CensusOpenState Reopened)
    (bootstrap : DiskDirectory → CensusDirectoryCache → EStateM IO.Error CensusOpenState Reopened) :
    report.recoverThroughReads finish bootstrap directory admission.owner admission.cache
      (admission.reached, admission.held) =
    finish directory admission.owner admission.cache prepared (admission.reached, admission.held) := by
  have selectedRoute : optionalMetadataWith (admission.lookup (directory.file .walBoundary))
      (admission.reached, admission.held) = .ok (some metadata) (admission.reached, admission.held) := by
    simp only [optionalMetadataWith, Bind.bind, EStateM.bind, marker, Pure.pure, EStateM.pure]
  simp only [recoverThroughReads, admission.recoverWithMarked_selects flat selectedRoute,
    Option.isSome_some, ↓reduceIte, Bind.bind, EStateM.bind, read]

/-- The admitted open reaches the continuation for the selected read plan
using the lock, cache, census and namespace from that very admission.
No report of the repair or returned table is needed to reach this point. -/
theorem reachesMarkedPreparation (report : CapturedMarkedReadReports admission layout published)
    {description keeper : Nat} {initial : DescriptorInventory} {origin source : LockedFileState FileImage}
    (trace : LockCensusTrace directory description initial source inventory retry)
    (earlier : ReportedReopenPrefix directory keeper origin source)
    (last : inventory.references description = [])
    (distinct : admission.owner.description ≠ description)
    (distinctCached : admission.cached.description ≠ description)
    (lockObject : inventory.inode admission.owner.description = initial.inode description)
    (flat : optionalMetadataWith (admission.lookup (directory.file .wal)) (admission.reached, admission.held) =
      .ok none (admission.reached, admission.held))
    {metadata : IO.FS.Metadata}
    (marker : admission.lookup (directory.file .walBoundary) (admission.reached, admission.held) =
      .ok (.ok metadata) (admission.reached, admission.held))
    (laterValid : retry.image.later.Beyond layout.range.through)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (finish : DiskDirectory → DescriptorSlot → CensusDirectoryCache → Plan × Reopened × Nat →
      EStateM IO.Error CensusOpenState Reopened)
    (bootstrap : DiskDirectory → CensusDirectoryCache → EStateM IO.Error CensusOpenState Reopened) :
    ReportedReopenPrefix directory keeper origin retry ∧
    report.bindings directory.path = some (admission.reached.inode admission.cached.description) ∧
    report.bindings (directory.file .lock) = some (initial.inode description) ∧
    report.listing.Custody ∧
    ∃ opened checkpoint,
      SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint ∧
      recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode history) = .ok opened.table ∧
      admission.run (report.recoverThroughReads finish bootstrap) =
        (tryCatchThe IO.Error (finish directory admission.owner admission.cache
          (layout.boundedPlan, opened, layout.plan.keeperBytes.size)) fun cause => do
            admission.unlock admission.owner ()
            throw cause) (admission.reached, admission.held) := by
  obtain ⟨prefixReached, _, _, _, _, oldObject, _, reached⟩ :=
    trace.capturesAfterAdmission earlier last admission distinct distinctCached lockObject
      (report.recoverThroughReads finish bootstrap)
  obtain ⟨opened, checkpoint, prepared, selected, replay⟩ := report.prepares laterValid following accepted ordered
  obtain ⟨sameRoot, sameLock, _, custody⟩ := report.sameObjects
  refine ⟨prefixReached, sameRoot, sameLock.trans (congrArg some oldObject), custody,
    ⟨opened, checkpoint, selected, replay, ?_⟩⟩
  rw [reached]
  simp only [tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch,
    report.recoverThroughReads_prepared flat marker prepared]

end CapturedMarkedReadReports

end Alvoki.Storage.DiskSession
