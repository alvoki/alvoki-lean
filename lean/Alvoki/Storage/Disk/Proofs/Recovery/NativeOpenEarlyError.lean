import Alvoki.Storage.Disk.Proofs.Recovery.FailedMarkerReadCensus
import Alvoki.Storage.Disk.Proofs.Session.CapturedMarkedReads

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}

/-- The cleanup of a read-only failure uses the acquired owner slot at
the reached census. A failed local flock unlock has no release effect.
Later handle drops are reported separately. -/
structure NativeOpenErrorUnlock (admission : CensusOpenAdmissionReports input directory inventory retry)
    (census : DescriptorInventory) where
  ownerLive : admission.owner ∈ census.slots
  cachedLive : admission.cached ∈ census.slots
  result : Except IO.Error Unit
  observed : admission.unlock admission.owner () (census, admission.held) = match result with
    | .ok () => .ok () (census, { admission.held with owners := admission.held.owners.set (directory.file .lock) none })
    | .error cause => .error cause (census, admission.held)

namespace NativeOpenErrorUnlock

variable {census : DescriptorInventory}

def files (cleanup : NativeOpenErrorUnlock admission census) : LockedFileState FileImage :=
  match cleanup.result with
  | .ok () => { admission.held with owners := admission.held.owners.set (directory.file .lock) none }
  | .error _ => admission.held

def diagnostic (cleanup : NativeOpenErrorUnlock admission census) (readError : IO.Error) : IO.Error :=
  match cleanup.result with
  | .ok () => readError
  | .error cause => cause

theorem returns (cleanup : NativeOpenErrorUnlock admission census)
    (recover : DiskDirectory → DescriptorSlot → CensusDirectoryCache → EStateM IO.Error CensusOpenState SegmentedSession)
    {readError : IO.Error}
    (failed : recover directory admission.owner admission.cache (admission.reached, admission.held) =
      .error readError (census, admission.held)) :
    admission.run recover = .error (cleanup.diagnostic readError) (census, cleanup.files) := by
  rw [admission.run_reachesReadCleanup recover failed, cleanup.observed]
  cases reported : cleanup.result with
  | ok value =>
    cases value
    simp only [reported, diagnostic, files]
  | error cause =>
    simp only [reported, diagnostic, files]

theorem keepsFiles (cleanup : NativeOpenErrorUnlock admission census) : cleanup.files.image = retry.image := by
  cases reported : cleanup.result <;> simp [files, reported, CensusOpenAdmissionReports.held]

theorem admits (cleanup : NativeOpenErrorUnlock admission census) :
    TryLockObserves cleanup.files.owners directory (.ok true) ↔ cleanup.result = .ok () := by
  cases reported : cleanup.result <;>
    simp [files, reported, TryLockObserves, CensusOpenAdmissionReports.held, LockOwners.set]

/-- A new acquisition after failed unlock uses the reported drop trace
for this same acquired description. Its files and diagnostic are fixed
before the finalizers or later process events. -/
theorem admitsAfterFailedUnlock (cleanup : NativeOpenErrorUnlock admission census) {cause : IO.Error}
    (failed : cleanup.result = .error cause) {finalCensus : DescriptorInventory} {final : LockedFileState FileImage}
    (trace : LockCensusTrace directory admission.owner.description census cleanup.files finalCensus final) :
    cleanup.files.owners.Owns directory admission.owner.description ∧ final.image = retry.image ∧
    (TryLockObserves final.owners directory (.ok true) ↔ finalCensus.references admission.owner.description = []) := by
  have same : cleanup.files = admission.held := by simp [files, failed]
  refine ⟨same.symm ▸ admission.opened.held, ?_, trace.freshFlockAllowed⟩
  have image := congrArg LockedFileState.image trace.reached.2.2
  split at image <;> exact image.trans cleanup.keepsFiles

end NativeOpenErrorUnlock

/-- The no-follow marker probe fails after lock acquisition and directory
cache capture. Only true ENOENT selects the bootstrap path. -/
structure NativeMarkerRouteError (admission : CensusOpenAdmissionReports input directory inventory retry) where
  flat : optionalMetadataWith (admission.lookup (directory.file .wal)) (admission.reached, admission.held) =
    .ok none (admission.reached, admission.held)
  lock : DeviceInode
  lockEntry : admission.view.child admission.root "LOCK" = some lock
  lockInode : admission.view.modelObject lock = admission.reached.inode admission.owner.description
  cause : IO.Error
  lookup : admission.lookup (directory.file .walBoundary) (admission.reached, admission.held) =
    .ok (.error cause) (admission.reached, admission.held)
  notMissing : ∀ path message, cause ≠ .noFileOrDirectory path 2 message
  cleanup : NativeOpenErrorUnlock admission admission.reached

namespace NativeMarkerRouteError

private theorem optionalLookupError (lookup : EStateM IO.Error CensusOpenState (Except IO.Error IO.FS.Metadata))
    (before : CensusOpenState) {cause : IO.Error} (reported : lookup before = .ok (.error cause) before)
    (notMissing : ∀ path message, cause ≠ .noFileOrDirectory path 2 message) :
    optionalMetadataWith lookup before = .error cause before := by
  simp only [optionalMetadataWith, Bind.bind, EStateM.bind, reported]
  rfl

/-- The exact route probe stops both workers before either can read or
repair files. The common installation continuation is also unreachable. -/
theorem stopsBeforeRecovery (seen : NativeMarkerRouteError admission)
    (marked bootstrap : EStateM IO.Error CensusOpenState Reopened) :
    admission.recoverWithMarked directory marked bootstrap (admission.reached, admission.held) =
      .error seen.cause (admission.reached, admission.held) := by
  have probe := optionalLookupError _ _ seen.lookup seen.notMissing
  simp only [CensusOpenAdmissionReports.recoverWithMarked, recoverSegmentedWalWith, rejectFlatWalWith,
    Bind.bind, EStateM.bind, seen.flat, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Pure.pure, EStateM.pure, probe]

def run (_seen : NativeMarkerRouteError admission)
    (marked bootstrap : DiskDirectory → CensusDirectoryCache → EStateM IO.Error CensusOpenState Reopened)
    (install : DiskDirectory → DescriptorSlot → CensusDirectoryCache → Reopened → EStateM IO.Error CensusOpenState SegmentedSession) :
    EStateM.Result IO.Error CensusOpenState SegmentedSession :=
  admission.run fun path owner cache =>
    admission.recoverWithMarked path (marked path cache) (bootstrap path cache) >>= install path owner cache

/-- The reached native admission returns an error at this exact
directory and lock capture. The unlock result selects the diagnostic
and retained lock authority while the filesystem image is unchanged. -/
theorem returns (seen : NativeMarkerRouteError admission)
    (marked bootstrap : DiskDirectory → CensusDirectoryCache → EStateM IO.Error CensusOpenState Reopened)
    (install : DiskDirectory → DescriptorSlot → CensusDirectoryCache → Reopened → EStateM IO.Error CensusOpenState SegmentedSession) :
    seen.run marked bootstrap install = .error (seen.cleanup.diagnostic seen.cause) (admission.reached, seen.cleanup.files) ∧
      seen.cleanup.files.image = retry.image ∧
      admission.owner ∈ admission.reached.slots ∧ admission.cached ∈ admission.reached.slots ∧
      admission.view.modelObject admission.root = admission.reached.inode admission.cached.description ∧
      admission.view.child admission.root "LOCK" = some seen.lock ∧
      admission.view.modelObject seen.lock = admission.reached.inode admission.owner.description ∧
      (TryLockObserves seen.cleanup.files.owners directory (.ok true) ↔ seen.cleanup.result = .ok ()) := by
  refine ⟨seen.cleanup.returns _ ?_, seen.cleanup.keepsFiles, seen.cleanup.ownerLive,
    seen.cleanup.cachedLive, admission.opened.captures.2.2.2.2.1, seen.lockEntry, seen.lockInode, seen.cleanup.admits⟩
  simp only [Bind.bind, EStateM.bind, seen.stopsBeforeRecovery]

end NativeMarkerRouteError

end Alvoki.Storage.DiskSession
