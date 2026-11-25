import Alvoki.Storage.Disk.NativeRawFinalizedOpenError
import Alvoki.Storage.Disk.NativeRawFlatWalOpenError

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap α : Type} {calls : RawOpenAdmissionCallbacks heap} {directory : DiskDirectory}

/-- The initialized opener can fail at either late guard before selecting
a recovery worker. The second guard is reached only with no flat WAL. -/
inductive RawHeldLateGuardError (calls : RawOpenAdmissionCallbacks heap)
    (directory : DiskDirectory) (before : heap) : IO.Error → Prop where
  | flat {cause : IO.Error} (seen : RawHeldFlatWalError calls directory before cause) :
    RawHeldLateGuardError calls directory before cause
  | marker {cause : IO.Error}
      (noFlat : optionalMetadataWith (calls.lookup (directory.file .wal)) before = .ok none before)
      (reported : calls.lookup (directory.file .walBoundary) before = .ok (.error cause) before)
      (notMissing : ∀ path message, cause ≠ .noFileOrDirectory path 2 message) :
    RawHeldLateGuardError calls directory before cause

theorem RawHeldLateGuardError.stops {before : heap} {cause : IO.Error}
    (seen : RawHeldLateGuardError calls directory before cause)
    (marked bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap α)
    (lock : IO.FS.Handle) (cache : DiskTable.OpenSyncFiles) :
    calls.recoverAndInstall marked bootstrap install directory lock cache before = .error cause before := by
  cases seen with
  | flat fault =>
    simp only [RawOpenAdmissionCallbacks.recoverAndInstall, recoverSegmentedWalWith, Bind.bind, EStateM.bind, fault.stops]
  | marker noFlat reported notMissing =>
    have rejected := rawOptionalMetadataError _ reported notMissing
    simp only [RawOpenAdmissionCallbacks.recoverAndInstall, recoverSegmentedWalWith, rejectFlatWalWith, Bind.bind,
      EStateM.bind, noFlat, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Pure.pure, EStateM.pure, rejected]

variable {input : FilePath} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {release : IO.FS.Handle → heap → heap}

/-- Either late guard leaves the cache available for its scope drop.
The same handle then enters local unlock and the reported final close,
with no recovery worker or table installation in between. -/
theorem RawHeldLateGuardError.returnsFinalized {cause : IO.Error}
    (seen : RawHeldLateGuardError calls directory seed.afterPending cause)
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed seed.afterPending)
    (finalized : RawOpenErrorLockFinalization view directory release admitted.lock admission.owner disposal.reached)
    (marked bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap α) :
    disposal.Finalized (calls.recoverAndInstall marked bootstrap install) cause finalized := by
  let recover := calls.recoverAndInstall marked bootstrap install
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, held, _⟩ := seed.installs
  have returned := disposal.returns recover cause (seen.stops marked bootstrap install admitted.lock) held
  exact disposal.returnsAfterLockFinalization recover cause returned finalized

end Alvoki.Storage.DiskSession
