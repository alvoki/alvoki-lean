import Alvoki.Storage.Disk.WalSegmentCachedExtentOpen

namespace Alvoki.Storage.WalSegmentRepair

open System

/-- The accepted checkpoint and marker determine the only WAL read used by
the bounded opener. Matching that read suffices to transfer its repair and
installation result. -/
theorem reopenMarkedBoundedWithCachedExtents_eq_of_selectedWal [Monad m] [LawfulMonad m]
    [MonadExceptOf IO.Error m] (dir : DiskDirectory)
    (readOptional : FilePath → m (Option ByteArray))
    (readRunSize : FilePath → m Nat) (readRunPrefix : FilePath → Nat → m ByteArray)
    (list : FilePath → m (Array IO.FS.DirEntry)) (lstat : FilePath → m (Except IO.Error IO.FS.Metadata))
    (readSeal : FilePath → Nat → m ByteArray) (readKeeper : FilePath → Nat → Nat → m ByteArray)
    (readBin : FilePath → m ByteArray) (readPrefix : FilePath → Nat → m KeeperPrefix)
    (removeFile : FilePath → m (Except IO.Error Unit)) (write : FilePath → ByteArray → m Unit)
    (sync : Array FilePath → m Unit) (renameFile : FilePath → FilePath → m Unit)
    {checkpoint : Option (PackedTable × UInt64)} {marker : ByteArray} {length : UInt64}
    (checkpointRead :
      readIntegrityCheckpointSized dir (readOptional (dir.file .manifest)) readRunSize readRunPrefix = pure checkpoint)
    (markerRead : readOptional (dir.file .walBoundary) = pure (some marker))
    (decoded : WAL.Boundary.decode marker = .ok length)
    (walRead : let watermark := (checkpoint.getD (.empty, 0)).1.committed.toNat
      readSelectedWithCachedExtents dir watermark length list lstat readSeal readKeeper =
        readSelectedWithPrefix dir watermark length list lstat readBin readPrefix) :
    reopenMarkedBoundedWithCachedExtents dir readOptional readRunSize readRunPrefix list lstat readSeal readKeeper
      removeFile write sync renameFile =
    reopenMarkedBoundedWithSizedCheckpoint dir readOptional readRunSize readRunPrefix list lstat readBin readPrefix
      removeFile write sync renameFile := by
  simp [reopenMarkedBoundedWithCachedExtents, reopenMarkedBoundedWithSizedCheckpoint,
    prepareBoundedMarkedFromCheckpoint, prepareBoundedMarkedFromReaders, checkpointRead, markerRead,
    decoded, liftExcept, Except.mapError, walRead]

end Alvoki.Storage.WalSegmentRepair
