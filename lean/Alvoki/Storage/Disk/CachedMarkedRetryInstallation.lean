import Alvoki.Storage.Disk.CachedRetryInstallation
import Alvoki.Storage.Disk.CheckpointRunChunkReports
import Alvoki.Storage.Disk.SegmentedBootstrapCompletion

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open WAL (frameSize)
open WAL.Boundary (CheckpointRepresentsPrefix)

/-- A healthy marked retry completes from the shared locked dispatcher.
The reached cache supplies the keeper read report and the repair effects.
The checkpoint loader obtains exact sizes and bytes from the selected
runs' per-open chunk observations. -/
theorem runOpenWithInstallation_markedRetryFromChunks {files : Type}
    {directory : DiskDirectory} {before : LockedFileState FileImage} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout before.image history} (reported : CachedRetryReadReports directory layout)
    (descriptors : DescriptorInventory) (slot : DescriptorSlot) (live : slot ∈ descriptors.slots)
    (bindings : FilePath → Option Nat)
    (lockObject : bindings (directory.file .lock) = some (descriptors.inode slot.description))
    (flock : DescriptorSlot → Except IO.Error Bool) (acquired : flock slot = .ok true)
    (acquisition : TryLockObserves before.owners directory (flock slot))
    (inventoryDescription : reported.inventory.descriptor = slot.description)
    (inventoryOwners : reported.inventory.owners = before.owners.set (directory.file .lock) (some slot.description))
    (nextRef : Nat) (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < nextRef) (unlock : UnlockReport)
    (openFiles : EStateM IO.Error FileImage files)
    (lookup : FilePath → EStateM IO.Error FileImage (Except IO.Error IO.FS.Metadata))
    (bootstrap : files → EStateM IO.Error FileImage Reopened)
    (cache : files) (initialized : openFiles before.image = .ok cache before.image)
    (flatName flatMessage : String)
    (flatAbsent : lookup (directory.file .wal) before.image =
      .ok (.error (.noFileOrDirectory flatName 2 flatMessage)) before.image)
    (markerMetadata : IO.FS.Metadata)
    (markedPath : lookup (directory.file .walBoundary) before.image = .ok (.ok markerMetadata) before.image)
    (keeperValid : before.image.keeper.Valid layout.target.Accepts)
    (laterValid : before.image.later.Beyond layout.range.through)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    {published : CheckpointPublication.Image}
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      before.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (reads : CheckpointRunChunkReads)
    (metadata : ∀ path, reported.inventory.reports.lstat path = (reads.stat path).map Prod.fst)
    (chunks : reads.ObservesSelected directory before.image.directory.active.manifest published.durable)
    (manifestRead : reported.inventory.reports.readOptional (directory.file .manifest) =
      .ok before.image.directory.active.manifest)
    (markerRead : reported.inventory.reports.readOptional (directory.file .walBoundary) =
      .ok before.image.directory.active.walBoundary)
    (readKeeper : files → FilePath → Nat → Nat → Except IO.Error ByteArray)
    (keeperReads : readKeeper cache = reported.readKeeper)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : files → FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : files → Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit)
    (settles : sync cache #[directory.path] before.image = .ok () before.image.syncDirectory)
    (healthy : ∀ action prior next,
      ReachesAction layout.target before.image.syncDirectory layout.plan.finishActions action prior →
      prior.effect layout.target action = some next →
      performPaths directory layout.plan removeFile throw (write cache) (sync cache) renameFile action prior = .ok () next) :
    let marked := fun files => reopenMarkedBoundedWithCachedExtents directory
      (fun path => liftExcept (reported.inventory.reports.readOptional path))
      (fun path => liftExcept (checkpointRunSizeReport reported.inventory.reports path))
      (fun path count => liftExcept (reads.readPrefix path count))
      (fun path => liftExcept (reported.list path))
      (fun path => liftExcept (.ok (reported.inventory.reports.lstat path) : Except IO.Error _))
      (fun path size => liftExcept (reported.readSeal path size))
      (fun path size physical => liftExcept (readKeeper files path size physical))
      removeFile (write files) (sync files) renameFile
    let recover := do
      let files ← openFiles
      recoverSegmentedWalWith (rejectFlatWalWith directory (optionalMetadataWith (lookup (directory.file .wal))))
        (optionalMetadataWith (lookup (directory.file .walBoundary))) (marked files) (bootstrap files)
    CachedRetryInstalled (before := before) reported descriptors slot bindings published liveRefs
      (runOpenWithInstallation directory slot.description nextRef (flock slot) unlock recover before) := by
  intro marked recover
  obtain ⟨watermark, _, _, count, _, _, absolute⟩ := DirectoryPublication.Bindings.walRange_accounting layout.decoded
  have byteCount : (WAL.encode history).size = count.toNat := by
    rw [absolute, layout.through, WAL.encode_size, Nat.mul_comm]
  obtain ⟨checkpoint, _, _, selected, _, _, _, _, _, _⟩ :=
    selectedCheckpoint_replays watermark accepted (byteCount ▸ count.toNat_lt_size) ordered
  let sizes := SizedCheckpointRunReports.ofChunkReads (checkpoint := checkpoint) selected reads metadata chunks
  have checkedMarker : optionalMetadataWith (lookup (directory.file .walBoundary)) before.image =
      .ok (some markerMetadata) before.image := by
    simp only [optionalMetadataWith, Bind.bind, EStateM.bind, markedPath, Pure.pure, EStateM.pure]
  have branch := runOpenWithInstallation_recoveryBranch directory slot.description nextRef before unlock
    openFiles lookup marked bootstrap cache initialized flatName flatMessage flatAbsent (some markerMetadata) checkedMarker
  have sameWorker : marked cache = cachedRetryRecovery reported sizes.readPrefix removeFile (write cache)
      (sync cache) renameFile := by
    simp only [marked, keeperReads, cachedRetryRecovery, sizes, SizedCheckpointRunReports.ofChunkReads]
  rw [acquired, branch]
  simp only [Option.isSome_some, ↓reduceIte, sameWorker]
  have completed := runOpenWithInstallation_cachedRetryCompletes reported descriptors slot live bindings lockObject
    flock acquired acquisition inventoryDescription inventoryOwners nextRef liveRefs fresh unlock keeperValid laterValid
    following accepted ordered sizes manifestRead markerRead removeFile (write cache) (sync cache) renameFile settles healthy
  simpa only [acquired] using completed

end Alvoki.Storage.DiskSession
