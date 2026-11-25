import Alvoki.Storage.Disk.NativeOpenEarlyError

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}

/-- One checked directory stream at the reached census. The error is
reported by readdir, and the observed closedir drops the stream's slot. -/
structure NativeReaddirFailure (entry : DescriptorInventory) (view : DirectoryReadNamespace)
    (root : DeviceInode) (path : FilePath) where
  stream : DescriptorSlot
  free : ∀ slot ∈ entry.slots, slot.address ≠ stream.address
  fresh : entry.references stream.description = []
  rootObject : entry.inode stream.description = view.modelObject root
  openDir : FilePath → EStateM IO.Error DescriptorInventory DescriptorSlot
  opened : openDir path entry = .ok stream (entry.insert stream free)
  scan : OpenedDirectoryScan
  cause : IO.Error
  failed : scan.terminal = .error cause
  closeDir : DescriptorSlot → EStateM IO.Error DescriptorInventory Unit
  closeReturned : scan.closed = .ok ()
  closed : closeDir stream (entry.insert stream free) = .ok () ((entry.insert stream free).afterDrops [stream.closeEvent])

namespace NativeReaddirFailure

variable {entry : DescriptorInventory} {view : DirectoryReadNamespace} {root : DeviceInode} {path : FilePath}

theorem releases (seen : NativeReaddirFailure entry view root path) :
    seen.closeDir seen.stream (entry.insert seen.stream seen.free) = .ok () entry ∧
    ((entry.insert seen.stream seen.free).afterDrops [seen.stream.closeEvent]).references seen.stream.description = [] := by
  have close := DescriptorInventory.insert_thenClose entry seen.stream seen.free []
  have kept : entry.afterDrops [seen.stream.closeEvent] = entry := by
    cases entry with
    | mk slots distinct inode =>
      simp only [DescriptorInventory.afterDrops, DescriptorInventory.mk.injEq, and_true]
      apply List.filter_eq_self.mpr
      intro slot member
      by_cases process : slot.reference.process = seen.stream.reference.process
      · have different : slot.reference.fd ≠ seen.stream.reference.fd := fun same =>
          seen.free slot member (Prod.ext process same)
        simp [DescriptorSlot.closeEvent, LockReferenceDrop.removes, process, different]
      · simp [DescriptorSlot.closeEvent, LockReferenceDrop.removes, process]
  have same : (entry.insert seen.stream seen.free).afterDrops [seen.stream.closeEvent] = entry := close.trans kept
  exact ⟨seen.closed.trans (congrArg (EStateM.Result.ok ()) same), same.symm ▸ seen.fresh⟩

end NativeReaddirFailure

/-- The reached marked open reads the checkpoint and marker successfully
before its checked listing reports a readdir error. Each observation uses
the files held by this same admitted open. -/
structure NativeMarkedListingError (admission : CensusOpenAdmissionReports input directory inventory retry) where
  flat : optionalMetadataWith (admission.lookup (directory.file .wal)) (admission.reached, admission.held) =
    .ok none (admission.reached, admission.held)
  routeMetadata : IO.FS.Metadata
  route : optionalMetadataWith (admission.lookup (directory.file .walBoundary)) (admission.reached, admission.held) =
    .ok (some routeMetadata) (admission.reached, admission.held)
  readOptional : FilePath → EStateM IO.Error CensusOpenState (Option ByteArray)
  readRunSize : FilePath → EStateM IO.Error CensusOpenState Nat
  readRunPrefix : FilePath → Nat → EStateM IO.Error CensusOpenState ByteArray
  checkpoint : Option (PackedTable × UInt64)
  atMarker : DescriptorInventory
  loaded : readIntegrityCheckpointSized directory (readOptional (directory.file .manifest)) readRunSize readRunPrefix
    (admission.reached, admission.held) = .ok checkpoint (atMarker, admission.held)
  marker : ByteArray
  atListing : DescriptorInventory
  markerRead : readOptional (directory.file .walBoundary) (atMarker, admission.held) = .ok (some marker) (atListing, admission.held)
  through : UInt64
  decoded : WAL.Boundary.decode marker = .ok through
  checked : through.toNat % WAL.frameSize = 0 ∧ (checkpoint.getD (.empty, 0)).1.committed.toNat ≤ through.toNat / WAL.frameSize
  listing : NativeReaddirFailure atListing admission.view admission.root directory.path
  list : FilePath → EStateM IO.Error CensusOpenState (Array IO.FS.DirEntry)
  listed : list directory.path (atListing, admission.held) =
    (liftExcept ((CheckedDirectoryReadReport.scanned listing.scan).result directory.path) : EStateM IO.Error CensusOpenState _)
      (atListing, admission.held)
  rootObject : atListing.inode admission.cached.description = admission.view.modelObject admission.root
  lock : DeviceInode
  lockEntry : admission.view.child admission.root "LOCK" = some lock
  lockObject : atListing.inode admission.owner.description = admission.view.modelObject lock
  cleanup : NativeOpenErrorUnlock admission atListing

namespace NativeMarkedListingError

variable {admission : CensusOpenAdmissionReports input directory inventory retry}

/-- Later file operations are parameters to the production worker. The
read-error theorem holds independently of any of their outcomes. -/
structure Remainder where
  lstat : FilePath → EStateM IO.Error CensusOpenState (Except IO.Error IO.FS.Metadata)
  readSeal : FilePath → Nat → EStateM IO.Error CensusOpenState ByteArray
  readKeeper : FilePath → Nat → Nat → EStateM IO.Error CensusOpenState ByteArray
  remove : FilePath → EStateM IO.Error CensusOpenState (Except IO.Error Unit)
  stage : FilePath → ByteArray → EStateM IO.Error CensusOpenState Unit
  sync : Array FilePath → EStateM IO.Error CensusOpenState Unit
  rename : FilePath → FilePath → EStateM IO.Error CensusOpenState Unit

def marked (seen : NativeMarkedListingError admission) (rest : Remainder) (path : DiskDirectory) :
    EStateM IO.Error CensusOpenState Reopened :=
  reopenMarkedBoundedWithCachedExtents path seen.readOptional seen.readRunSize seen.readRunPrefix seen.list
    rest.lstat rest.readSeal rest.readKeeper rest.remove rest.stage rest.sync rest.rename

theorem stopsAtListing (seen : NativeMarkedListingError admission) (rest : Remainder)
    (bootstrap : EStateM IO.Error CensusOpenState Reopened) :
    admission.recoverWithMarked directory (seen.marked rest directory) bootstrap (admission.reached, admission.held) =
      .error seen.listing.cause (seen.atListing, admission.held) := by
  have failed : seen.list directory.path (seen.atListing, admission.held) =
      .error seen.listing.cause (seen.atListing, admission.held) := by
    rw [seen.listed, CheckedDirectoryReadReport.scan_readError directory.path seen.listing.failed]
    rfl
  rw [admission.recoverWithMarked_selects seen.flat seen.route]
  simp only [Option.isSome_some, ↓reduceIte, marked, reopenMarkedBoundedWithCachedExtents, prepareBoundedMarkedFromReaders,
    readSelectedWithCachedExtents, Bind.bind, EStateM.bind, seen.loaded, seen.markerRead, seen.decoded, seen.checked, true_and,
    liftExcept, Except.mapError, Pure.pure, EStateM.pure, failed]

def recover (seen : NativeMarkedListingError admission) (rest : Remainder)
    (bootstrap : DiskDirectory → CensusDirectoryCache → EStateM IO.Error CensusOpenState Reopened)
    (install : DiskDirectory → DescriptorSlot → CensusDirectoryCache → Reopened → EStateM IO.Error CensusOpenState SegmentedSession)
    (path : DiskDirectory) (owner : DescriptorSlot) (cache : CensusDirectoryCache) : EStateM IO.Error CensusOpenState SegmentedSession :=
  admission.recoverWithMarked path (seen.marked rest path) (bootstrap path cache) >>= install path owner cache

/-- The listing's error propagates before any extent, WAL read, repair or
installation. Unlock uses the reached census after the same stream drops. -/
theorem returns (seen : NativeMarkedListingError admission) (rest : Remainder)
    (bootstrap : DiskDirectory → CensusDirectoryCache → EStateM IO.Error CensusOpenState Reopened)
    (install : DiskDirectory → DescriptorSlot → CensusDirectoryCache → Reopened → EStateM IO.Error CensusOpenState SegmentedSession) :
    admission.run (seen.recover rest bootstrap install) =
        .error (seen.cleanup.diagnostic seen.listing.cause) (seen.atListing, seen.cleanup.files) ∧
      seen.listing.closeDir seen.listing.stream (seen.atListing.insert seen.listing.stream seen.listing.free) = .ok () seen.atListing ∧
      seen.atListing.inode seen.listing.stream.description = seen.atListing.inode admission.cached.description ∧
      admission.view.child admission.root "LOCK" = some seen.lock ∧
      seen.atListing.inode admission.owner.description = admission.view.modelObject seen.lock ∧
      admission.owner ∈ seen.atListing.slots ∧ admission.cached ∈ seen.atListing.slots ∧ seen.cleanup.files.image = retry.image ∧
      (TryLockObserves seen.cleanup.files.owners directory (.ok true) ↔ seen.cleanup.result = .ok ()) := by
  refine ⟨seen.cleanup.returns _ ?_, seen.listing.releases.1, seen.listing.rootObject.trans seen.rootObject.symm,
    seen.lockEntry, seen.lockObject, seen.cleanup.ownerLive, seen.cleanup.cachedLive, seen.cleanup.keepsFiles, seen.cleanup.admits⟩
  simp only [recover, Bind.bind, EStateM.bind, seen.stopsAtListing]

end NativeMarkedListingError

end Alvoki.Storage.DiskSession
