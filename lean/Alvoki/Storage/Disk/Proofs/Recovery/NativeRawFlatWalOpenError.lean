import Alvoki.Storage.Disk.NativeRawRecoveryReturn

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

end Alvoki.Storage.DiskSession
