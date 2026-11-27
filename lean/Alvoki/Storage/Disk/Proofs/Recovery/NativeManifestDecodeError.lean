import Alvoki.Storage.Disk.Proofs.Session.CapturedCheckpointReadCensus
import Alvoki.Storage.Disk.Proofs.Recovery.NativeOpenEarlyError

namespace Alvoki.Storage.DiskSession

open System Manifest WalSegmentRepair

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}

/-- A marked admission reaches the manifest reader under the acquired
lock. The selected malformed bytes come from the canonical inode's
no-follow stat and actual open. The temporary read is closed before the
manifest decoder yields its error. -/
structure NativeManifestDecodeError (admission : CensusOpenAdmissionReports input directory inventory retry) where
  flat : optionalMetadataWith (admission.lookup (directory.file .wal)) (admission.reached, admission.held) =
    .ok none (admission.reached, admission.held)
  marker : IO.FS.Metadata
  route : admission.lookup (directory.file .walBoundary) (admission.reached, admission.held) =
    .ok (.ok marker) (admission.reached, admission.held)
  reads : CheckpointRunChunkReads
  bytes : ByteArray
  selected : retry.image.directory.active.manifest = some bytes
  manifest : HeldMetadataFile reads (directory.file .manifest) "MANIFEST" admission.view admission.root bytes
  fits : IntegrityCheckpoint.acquisitionSize bytes < USize.size
  release : FilePath → List LockReferenceDrop
  custody : TemporaryPrefixCustody manifest.calls admission.reached (release (directory.file .manifest))
  cause : String
  invalid : IntegrityCheckpoint.decode bytes = .error cause
  lock : DeviceInode
  lockEntry : admission.view.child admission.root "LOCK" = some lock
  lockObject : admission.view.modelObject lock = admission.reached.inode admission.owner.description

namespace NativeManifestDecodeError

def afterRead (fault : NativeManifestDecodeError admission) : DescriptorInventory :=
  admission.reached.afterDrops (fault.custody.beforeOpen ++ fault.release (directory.file .manifest))

def readOptional (fault : NativeManifestDecodeError admission) (resolved : DiskDirectory) (path : FilePath) :
    EStateM IO.Error CensusOpenState (Option ByteArray) := fun before =>
  match readTemporaryMetadata fault.reads resolved fault.release path (admission.cache, before) with
  | .ok bytes (_, reached) => .ok bytes reached
  | .error cause (_, reached) => .error cause reached

/-- Read the exact bounded prefix from the selected manifest. Both native
path resolutions identify its inode, and the temporary reference is gone
at the decoder's reached census. -/
theorem readsManifest (fault : NativeManifestDecodeError admission) :
    let file := fault.manifest.calls
    fault.readOptional directory (directory.file .manifest) (admission.reached, admission.held) =
      .ok (some (fault.bytes.extract 0 (IntegrityCheckpoint.acquisitionSize fault.bytes)))
        (fault.afterRead, admission.held) ∧
    file.openLookup.child = file.statLookup.child ∧
    file.inventory.inode file.slot.description = admission.view.modelObject fault.manifest.object ∧
    (∀ earlier rest, fault.custody.beforeClose = earlier ++ rest →
      file.slot ∈ (file.inventory.afterDrops earlier).slots) ∧
    fault.afterRead.references file.slot.description = [] := by
  have acquired := fault.custody.readMetadata (fault.manifest.manifestPrefix fault.fits) admission.cache admission.held
  have bound := fault.manifest.bound
  let file := fault.manifest.calls
  have identity := (congrArg admission.view.modelObject (file.openLookup.child_eq bound)).symm.trans file.identifiedOpen
  refine ⟨?_, (file.openLookup.child_eq bound).trans (file.statLookup.child_eq bound).symm,
    identity.symm, fun _ _ ordered => fault.custody.liveAtRead ordered, ?_⟩
  · simp only [readOptional, acquired, afterRead]
  · rw [afterRead, ← fault.custody.closes.1]
    exact fault.custody.closes.2

/-- Acquiring a bounded prefix preserves the decoder's exact diagnostic.
The failure occurs before selecting any generation or run operations. -/
theorem rejects (fault : NativeManifestDecodeError admission)
    (readSize : FilePath → EStateM IO.Error CensusOpenState Nat)
    (readPrefix : FilePath → Nat → EStateM IO.Error CensusOpenState ByteArray) :
    readIntegrityCheckpointSized directory (fault.readOptional directory (directory.file .manifest)) readSize readPrefix
      (admission.reached, admission.held) = .error (IO.userError fault.cause) (fault.afterRead, admission.held) := by
  simp only [readIntegrityCheckpointSized, Bind.bind, EStateM.bind, fault.readsManifest.1,
    IntegrityCheckpoint.decode_acquisitionPrefix, fault.invalid, Except.mapError, liftExcept,
    throw, throwThe, MonadExceptOf.throw, EStateM.throw]

def recover (fault : NativeManifestDecodeError admission)
    (readSize : FilePath → EStateM IO.Error CensusOpenState Nat)
    (readPrefix : FilePath → Nat → EStateM IO.Error CensusOpenState ByteArray) (tail : RejectedMarkerTail)
    (bootstrap : DiskDirectory → CensusDirectoryCache → EStateM IO.Error CensusOpenState Reopened)
    (install : DiskDirectory → DescriptorSlot → CensusDirectoryCache → Reopened →
      EStateM IO.Error CensusOpenState SegmentedSession) :=
  admission.recoverMarkedWithReads fault.readOptional readSize readPrefix tail bootstrap install

theorem stopsBeforeWal (fault : NativeManifestDecodeError admission) (readSize readPrefix tail bootstrap install) :
    fault.recover readSize readPrefix tail bootstrap install directory admission.owner admission.cache
      (admission.reached, admission.held) = .error (IO.userError fault.cause) (fault.afterRead, admission.held) := by
  have selected : optionalMetadataWith (admission.lookup (directory.file .walBoundary))
      (admission.reached, admission.held) = .ok (some fault.marker) (admission.reached, admission.held) := by
    simp only [optionalMetadataWith, Bind.bind, EStateM.bind, fault.route, Pure.pure, EStateM.pure]
  simp only [recover, CensusOpenAdmissionReports.recoverMarkedWithReads, recoverSegmentedWalWith,
    rejectFlatWalWith, reopenMarkedBoundedWithCachedExtents, prepareBoundedMarkedFromReaders,
    Bind.bind, EStateM.bind, fault.flat, selected, Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
    ↓reduceIte, Pure.pure, EStateM.pure, fault.rejects]

/-- The original opener returns without a session or repair. The local
unlock at the reached manifest close determines the surfaced diagnostic
and whether the same physical lock is available. Its failed-unlock case
can continue through `NativeOpenErrorUnlock.admitsAfterFailedUnlock`. -/
theorem returns (fault : NativeManifestDecodeError admission)
    (cleanup : NativeOpenErrorUnlock admission fault.afterRead) (readSize readPrefix tail bootstrap install) :
    admission.run (fault.recover readSize readPrefix tail bootstrap install) =
      .error (cleanup.diagnostic (IO.userError fault.cause)) (fault.afterRead, cleanup.files) ∧
    cleanup.files.image = retry.image ∧
    cleanup.files.image.directory.active.manifest = some fault.bytes ∧
    fault.afterRead.references fault.manifest.calls.slot.description = [] ∧
    admission.owner ∈ fault.afterRead.slots ∧ admission.cached ∈ fault.afterRead.slots ∧
    admission.view.modelObject admission.root = fault.afterRead.inode admission.cached.description ∧
    admission.view.child admission.root "LOCK" = some fault.lock ∧
    admission.view.modelObject fault.lock = fault.afterRead.inode admission.owner.description ∧
    (TryLockObserves cleanup.files.owners directory (.ok true) ↔ cleanup.result = .ok ()) := by
  exact ⟨cleanup.returns _ (fault.stopsBeforeWal readSize readPrefix tail bootstrap install), cleanup.keepsFiles,
    (congrArg (fun image => image.directory.active.manifest) cleanup.keepsFiles).trans fault.selected,
    fault.readsManifest.2.2.2.2, cleanup.ownerLive, cleanup.cachedLive,
    admission.opened.captures.2.2.2.2.1, fault.lockEntry, fault.lockObject, cleanup.admits⟩

end NativeManifestDecodeError

end Alvoki.Storage.DiskSession
