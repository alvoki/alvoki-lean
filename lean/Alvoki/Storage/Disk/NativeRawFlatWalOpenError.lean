import Alvoki.Storage.Disk.NativeRawMarkerRouteError

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap : Type}

/-- The second flat-WAL guard runs after the lock and cache initialization.
It can reject a reported flat binding or propagate a lookup error other
than ENOENT. Each report uses the same reached raw heap. -/
inductive RawHeldFlatWalError (calls : RawOpenAdmissionCallbacks heap)
    (directory : DiskDirectory) (before : heap) : IO.Error → Prop where
  | lookupError {cause : IO.Error}
      (reported : calls.lookup (directory.file .wal) before = .ok (.error cause) before)
      (notMissing : ∀ path message, cause ≠ .noFileOrDirectory path 2 message) :
      RawHeldFlatWalError calls directory before cause
  | flatPresent {metadata : IO.FS.Metadata}
      (reported : calls.lookup (directory.file .wal) before = .ok (.ok metadata) before) :
      RawHeldFlatWalError calls directory before
        (IO.userError s!"unsupported flat WAL binding: '{directory.file .wal}'")

theorem RawHeldFlatWalError.stops
    {calls : RawOpenAdmissionCallbacks heap} {directory : DiskDirectory} {before : heap} {cause : IO.Error}
    (seen : RawHeldFlatWalError calls directory before cause) :
    rejectFlatWalWith directory (optionalMetadataWith (calls.lookup (directory.file .wal))) before =
      .error cause before := by
  cases seen with
  | lookupError reported notMissing =>
    have rejected := rawOptionalMetadataError _ reported notMissing
    simp only [rejectFlatWalWith, Bind.bind, EStateM.bind, rejected]
  | flatPresent reported =>
    simp [rejectFlatWalWith, optionalMetadataWith, Bind.bind, EStateM.bind, reported, Pure.pure, EStateM.pure,
      throw, throwThe, MonadExceptOf.throw, EStateM.throw]

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {cleanup : NativeOpenErrorUnlock admission admission.reached}

/-- The public open returns the second flat guard's diagnostic or the
local unlock error. The guard stops before the marker probe, recovery
workers and installer, while using the same lock and raw cache heap. -/
theorem RawHeldFlatWalError.returns {cause : IO.Error}
    (seen : RawHeldFlatWalError calls directory seed.afterPending cause)
    (observed : RawHeldOpenCleanup (admitted := admitted) cleanup seed)
    (marked bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap α) :
    observed.Returned (calls.recoverAndInstall marked bootstrap install) cause := by
  apply observed.returnsError
  intro cache
  simp only [RawOpenAdmissionCallbacks.recoverAndInstall, recoverSegmentedWalWith, Bind.bind, EStateM.bind, seen.stops]

end Alvoki.Storage.DiskSession
