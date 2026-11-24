import Alvoki.Storage.Disk.IntegrityCheckpointSizedRead
import Alvoki.Storage.Disk.WalSegmentBoundedOpen

namespace Alvoki.Storage.WalSegmentRepair

open System

/-- Check selected run extents before reading their payloads, then use the
same strict replay and repair as bounded WAL open. -/
def reopenMarkedBoundedWithSizedCheckpoint [Monad m] [MonadExceptOf IO.Error m] (dir : DiskDirectory)
    (readOptional : FilePath → m (Option ByteArray))
    (readRunSize : FilePath → m Nat) (readRunPrefix : FilePath → Nat → m ByteArray)
    (list : FilePath → m (Array IO.FS.DirEntry)) (lstat : FilePath → m (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → m ByteArray) (readPrefix : FilePath → Nat → m KeeperPrefix)
    (removeFile : FilePath → m (Except IO.Error Unit)) (write : FilePath → ByteArray → m Unit)
    (sync : Array FilePath → m Unit) (renameFile : FilePath → FilePath → m Unit) : m Reopened := do
  let (plan, reopened, keeperFileSize) ← prepareBoundedMarkedFromCheckpoint dir
    (readIntegrityCheckpointSized dir (readOptional (dir.file .manifest)) readRunSize readRunPrefix)
    readOptional list lstat readBin readPrefix
  finishBoundedMarkedOpen dir plan keeperFileSize removeFile write sync renameFile
  return reopened

/-- When acquisition returns the same checkpoint, it determines the same
marked-open action, including the selected WAL, repair barriers and result.
`readIntegrityCheckpointSized_compatible` supplies this equality for healthy reports. -/
theorem reopenMarkedBoundedWithSizedCheckpoint_eq_of_checkpoint [Monad m] [MonadExceptOf IO.Error m]
    (dir : DiskDirectory) (readOptional : FilePath → m (Option ByteArray))
    (readRunSize : FilePath → m Nat) (readRunPrefix : FilePath → Nat → m ByteArray)
    (list : FilePath → m (Array IO.FS.DirEntry)) (lstat : FilePath → m (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → m ByteArray) (readPrefix : FilePath → Nat → m KeeperPrefix)
    (removeFile : FilePath → m (Except IO.Error Unit)) (write : FilePath → ByteArray → m Unit)
    (sync : Array FilePath → m Unit) (renameFile : FilePath → FilePath → m Unit)
    (checkpoint : readIntegrityCheckpointSized dir (readOptional (dir.file .manifest)) readRunSize readRunPrefix =
      readIntegrityCheckpoint (readOptional (dir.file .manifest))
        (fun generation index => readBin (dir.file (.run generation index)))
        (fun report => liftExcept (report.mapError IO.userError))) :
    reopenMarkedBoundedWithSizedCheckpoint dir readOptional readRunSize readRunPrefix list lstat readBin readPrefix
      removeFile write sync renameFile =
      reopenMarkedBoundedWith dir readOptional list lstat readBin readPrefix removeFile write sync renameFile := by
  unfold reopenMarkedBoundedWithSizedCheckpoint reopenMarkedBoundedWith prepareBoundedMarkedWith
  rw [checkpoint]

end Alvoki.Storage.WalSegmentRepair
