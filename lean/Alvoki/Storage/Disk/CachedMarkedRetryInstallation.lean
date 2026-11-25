import Alvoki.Storage.Disk.CachedRetryInstallation
import Alvoki.Storage.Disk.CheckpointRunChunkReports
import Alvoki.Storage.Disk.SegmentedBootstrapCompletion

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open WAL (frameSize)
open WAL.Boundary (CheckpointRepresentsPrefix)

/-- The reached callbacks of a held marked reopen. The individual checkpoint
open observations are supplied separately. -/
structure MarkedRetryChunkOperations (files : Type) (directory : DiskDirectory)
    {before : LockedFileState FileImage} {history : List WAL.Write}
    (layout : CanonicalKeeperLayout before.image history) where
  reported : CachedRetryReadReports directory layout
  descriptors : DescriptorInventory
  slot : DescriptorSlot
  live : slot ∈ descriptors.slots
  bindings : FilePath → Option Nat
  lockObject : bindings (directory.file .lock) = some (descriptors.inode slot.description)
  flock : DescriptorSlot → Except IO.Error Bool
  acquired : flock slot = .ok true
  acquisition : TryLockObserves before.owners directory (flock slot)
  inventoryDescription : reported.inventory.descriptor = slot.description
  inventoryOwners : reported.inventory.owners = before.owners.set (directory.file .lock) (some slot.description)
  nextRef : Nat
  liveRefs : List Nat
  fresh : ∀ ref ∈ liveRefs, ref < nextRef
  unlock : UnlockReport
  openFiles : EStateM IO.Error FileImage files
  lookup : FilePath → EStateM IO.Error FileImage (Except IO.Error IO.FS.Metadata)
  bootstrap : files → EStateM IO.Error FileImage Reopened
  cache : files
  initialized : openFiles before.image = .ok cache before.image
  flatName : String
  flatMessage : String
  flatAbsent : lookup (directory.file .wal) before.image =
    .ok (.error (.noFileOrDirectory flatName 2 flatMessage)) before.image
  markerMetadata : IO.FS.Metadata
  markedPath : lookup (directory.file .walBoundary) before.image = .ok (.ok markerMetadata) before.image
  reads : CheckpointRunChunkReads
  metadata : ∀ path, reported.inventory.reports.lstat path = (reads.stat path).map Prod.fst
  manifestRead : reported.inventory.reports.readOptional (directory.file .manifest) =
    .ok before.image.directory.active.manifest
  markerRead : reported.inventory.reports.readOptional (directory.file .walBoundary) =
    .ok before.image.directory.active.walBoundary
  readKeeper : files → FilePath → Nat → Nat → Except IO.Error ByteArray
  keeperReads : readKeeper cache = reported.readKeeper
  removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit)
  write : files → FilePath → ByteArray → EStateM IO.Error FileImage Unit
  sync : files → Array FilePath → EStateM IO.Error FileImage Unit
  renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit

namespace MarkedRetryChunkOperations

variable {files : Type} {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout before.image history}

/-- The later effects needed only for a completed open. -/
abbrev HealthyFinish (observed : MarkedRetryChunkOperations files directory layout) : Prop :=
  ∀ action prior next,
    ReachesAction layout.target before.image.syncDirectory layout.plan.finishActions action prior →
    prior.effect layout.target action = some next →
    performPaths directory layout.plan observed.removeFile throw (observed.write observed.cache)
      (observed.sync observed.cache) observed.renameFile action prior = .ok () next

def markedAt (observed : MarkedRetryChunkOperations files directory layout)
    (resolved : DiskDirectory) (cache : files) :
    EStateM IO.Error FileImage Reopened :=
  reopenMarkedBoundedWithCachedExtents resolved
    (fun path => liftExcept (observed.reported.inventory.reports.readOptional path))
    (fun path => liftExcept (checkpointRunSizeReport observed.reported.inventory.reports path))
    (fun path count => liftExcept (observed.reads.readPrefix path count))
    (fun path => liftExcept (observed.reported.list path))
    (fun path => liftExcept (.ok (observed.reported.inventory.reports.lstat path) : Except IO.Error _))
    (fun path size => liftExcept (observed.reported.readSeal path size))
    (fun path size physical => liftExcept (observed.readKeeper cache path size physical))
    observed.removeFile (observed.write cache) (observed.sync cache) observed.renameFile

def recoverAt (observed : MarkedRetryChunkOperations files directory layout) (resolved : DiskDirectory) :
    EStateM IO.Error FileImage Reopened := do
  let cache ← observed.openFiles
  recoverSegmentedWalWith
    (rejectFlatWalWith resolved (optionalMetadataWith (observed.lookup (resolved.file .wal))))
    (optionalMetadataWith (observed.lookup (resolved.file .walBoundary)))
    (observed.markedAt resolved cache) (observed.bootstrap cache)

def runAt (observed : MarkedRetryChunkOperations files directory layout) (resolved : DiskDirectory)
    (slot : DescriptorSlot) : EStateM IO.Error (LockedFileState FileImage) SegmentedSession :=
  runOpenWithInstallation resolved slot.description observed.nextRef (observed.flock slot)
    observed.unlock (observed.recoverAt resolved)

def run (observed : MarkedRetryChunkOperations files directory layout) :
    EStateM.Result IO.Error (LockedFileState FileImage) SegmentedSession :=
  observed.runAt directory observed.slot before

/-- A successfully acquired, initialized open with observed marker metadata
uses the same marked worker regardless of the outcome of recovery. -/
theorem run_selectsMarked (observed : MarkedRetryChunkOperations files directory layout) :
    observed.run = runOpenWithInstallation directory observed.slot.description observed.nextRef (.ok true)
      observed.unlock (observed.markedAt directory observed.cache) before := by
  have checkedMarker : optionalMetadataWith (observed.lookup (directory.file .walBoundary)) before.image =
      .ok (some observed.markerMetadata) before.image := by
    simp only [optionalMetadataWith, Bind.bind, EStateM.bind, observed.markedPath, Pure.pure, EStateM.pure]
  have branch := runOpenWithInstallation_recoveryBranch directory observed.slot.description observed.nextRef before
    observed.unlock observed.openFiles observed.lookup (observed.markedAt directory) observed.bootstrap observed.cache
    observed.initialized observed.flatName observed.flatMessage observed.flatAbsent (some observed.markerMetadata) checkedMarker
  rw [run, runAt, recoverAt, observed.acquired, branch]
  rfl

end MarkedRetryChunkOperations

/-- The observed callbacks and selected run read contracts of one held reopen. -/
structure MarkedRetryChunkReports (files : Type) (directory : DiskDirectory)
    {before : LockedFileState FileImage} {history : List WAL.Write}
    (layout : CanonicalKeeperLayout before.image history) (published : CheckpointPublication.Image)
    extends MarkedRetryChunkOperations files directory layout where
  chunks : reads.ObservesSelected directory before.image.directory.active.manifest published.durable
  settles : sync cache #[directory.path] before.image = .ok () before.image.syncDirectory
  healthy : toMarkedRetryChunkOperations.HealthyFinish

namespace MarkedRetryChunkReports

variable {files : Type} {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout before.image history} {published : CheckpointPublication.Image}

/-- The selected canonical descriptors after the first start above the
checkpoint watermark. This property depends only on the WAL read reports. -/
theorem selectedAfterWatermark (observed : MarkedRetryChunkReports files directory layout published)
    {offsets : List Nat} {selected : List WalSegment}
    (chosen : selectWalSegmentReads offsets layout.range.watermark = some (layout.first, selected.map WalSegment.first))
    (descriptors : layout.sealed ++ [layout.keeper] = selected) :
    ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start :=
  observed.reported.selectedAfterWatermark chosen descriptors

abbrev run (observed : MarkedRetryChunkReports files directory layout published) :=
  observed.toMarkedRetryChunkOperations.run

end MarkedRetryChunkReports

/-- After the observed cache setup and metadata branch, install the table
from the reached marked worker. Checkpoint sizes and bytes come from the
selected runs' per-open chunk observations. -/
theorem runOpenWithInstallation_markedRetryFromChunks {files : Type}
    {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout before.image history} {published : CheckpointPublication.Image}
    (observed : MarkedRetryChunkReports files directory layout published)
    (keeperValid : before.image.keeper.Valid layout.target.Accepts)
    (laterValid : before.image.later.Beyond layout.range.through)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      before.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history) :
    CachedRetryInstalled (before := before) observed.reported observed.descriptors observed.slot observed.bindings
      published observed.liveRefs observed.run := by
  obtain ⟨watermark, _, _, count, _, _, absolute⟩ := DirectoryPublication.Bindings.walRange_accounting layout.decoded
  have byteCount : (WAL.encode history).size = count.toNat := by
    rw [absolute, layout.through, WAL.encode_size, Nat.mul_comm]
  obtain ⟨checkpoint, _, _, selected, _, _, _, _, _, _⟩ :=
    selectedCheckpoint_replays watermark accepted (byteCount ▸ count.toNat_lt_size) ordered
  let sizes := SizedCheckpointRunReports.ofChunkReads (checkpoint := checkpoint) selected observed.reads
    observed.metadata observed.chunks
  have sameWorker : observed.toMarkedRetryChunkOperations.markedAt directory observed.cache =
      cachedRetryRecovery observed.reported sizes.readPrefix observed.removeFile (observed.write observed.cache)
        (observed.sync observed.cache) observed.renameFile := by
    simp only [MarkedRetryChunkOperations.markedAt, observed.keeperReads, cachedRetryRecovery, sizes,
      SizedCheckpointRunReports.ofChunkReads]
  unfold MarkedRetryChunkReports.run
  rw [observed.toMarkedRetryChunkOperations.run_selectsMarked, sameWorker]
  have completed := runOpenWithInstallation_cachedRetryCompletes observed.reported observed.descriptors observed.slot
    observed.live observed.bindings observed.lockObject observed.flock observed.acquired observed.acquisition
    observed.inventoryDescription observed.inventoryOwners observed.nextRef observed.liveRefs observed.fresh
    observed.unlock keeperValid laterValid following accepted ordered sizes observed.manifestRead observed.markerRead
    observed.removeFile (observed.write observed.cache) (observed.sync observed.cache) observed.renameFile
    observed.settles observed.healthy
  simpa only [observed.acquired] using completed

end Alvoki.Storage.DiskSession
