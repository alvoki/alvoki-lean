import Alvoki.Storage.Disk.WalSegmentOpenFast

namespace Alvoki.Storage.WalSegmentRepair

open System
open WAL (frameSize)

/-- Keep the observed physical size separate from the bytes needed by replay
and replacement. Unread keeper tail bytes are never represented as input. -/
structure KeeperPrefix where
  bytes : ByteArray
  fileSize : Nat

private def readSelectedWithPrefix [Monad m] [MonadExceptOf IO.Error m]
    (dir : DiskDirectory) (watermark : Nat) (length : UInt64)
    (list : FilePath → m (Array IO.FS.DirEntry)) (lstat : FilePath → m (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → m ByteArray) (readPrefix : FilePath → Nat → m KeeperPrefix) :
    m (WalSegmentMarkerReads × Nat) := do
  let through := length.toNat / frameSize
  unless length.toNat % frameSize = 0 ∧ watermark ≤ through do
    throw (IO.userError "invalid absolute WAL segment marker")
  let entries ← list dir.path
  let offsets ← scanWalSegmentOffsets (probeWalSegmentWith dir lstat) (entries.toList.map (·.fileName))
  let some (required, newer) := selectWalSegmentReadsThrough offsets watermark through
    | throw (IO.userError "no WAL segment covers the checkpoint watermark")
  let some keeper := required.getLast?
    | throw (IO.userError "no WAL segment covers the commit marker")
  let sealed := required.dropLast
  let payloads ← readWalSegmentPayloadsWith dir readBin sealed
  let keeperSize := (through - keeper) * frameSize
  let kept ← readPrefix (dir.file (.walSegment keeper)) keeperSize
  unless kept.bytes.size = keeperSize ∧ keeperSize ≤ kept.fileSize do
    throw (IO.userError "invalid WAL keeper prefix or physical size")
  return (⟨sealed.zip payloads ++ [(keeper, kept.bytes)], newer⟩, kept.fileSize)

/-- Strict read-only preparation, using the same checkpoint, absolute marker,
canonical inventory and replay checks as the complete-payload worker. -/
def prepareBoundedMarkedWith [Monad m] [MonadExceptOf IO.Error m] (dir : DiskDirectory)
    (readOptional : FilePath → m (Option ByteArray))
    (list : FilePath → m (Array IO.FS.DirEntry)) (lstat : FilePath → m (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → m ByteArray) (readPrefix : FilePath → Nat → m KeeperPrefix) :
    m (Plan × Reopened × Nat) := do
  let checkpoint ← readIntegrityCheckpoint (readOptional (dir.file .manifest))
    (fun generation index => readBin (dir.file (.run generation index)))
    (fun report => liftExcept (report.mapError IO.userError))
  let (base, generation) := checkpoint.getD (.empty, 0)
  let some marker ← readOptional (dir.file .walBoundary)
    | throw (IO.userError "segmented WAL is missing its commit marker")
  let length ← liftExcept ((WAL.Boundary.decode marker).mapError IO.userError)
  let (reads, keeperFileSize) ← readSelectedWithPrefix dir base.committed.toNat length list lstat readBin readPrefix
  let (_, table) ← liftExcept ((recoverMarkedWalSegments base length reads.files).mapError IO.userError)
  let some (keeper, keeperBytes) := reads.files.getLast?
    | throw (IO.userError "no WAL segment covers the commit marker")
  return (⟨length.toNat / frameSize, keeper, reads.newer, keeperBytes⟩,
    ⟨table, generation, length, keeper⟩, keeperFileSize)

/-- Apply the usual repair barriers. Physical size, rather than the loaded
prefix size, determines whether the existing keeper needs replacement. -/
def finishBoundedMarkedOpen [Monad m] [MonadExceptOf IO.Error m] (dir : DiskDirectory) (plan : Plan)
    (keeperFileSize : Nat) (removeFile : FilePath → m (Except IO.Error Unit)) (write : FilePath → ByteArray → m Unit)
    (sync : Array FilePath → m Unit) (renameFile : FilePath → FilePath → m Unit) : m Unit := do
  unless plan.valid && plan.keeperBytes.size == plan.keeperSize && decide (plan.keeperSize ≤ keeperFileSize) do
    throw (IO.userError "invalid WAL segment repair plan")
  if plan.newer.isEmpty && keeperFileSize == plan.keeperSize then
    sync #[dir.path]
    sync #[dir.file (.walSegment plan.keeper)]
  else
    runRepairPlan dir plan (decide (plan.keeperSize < keeperFileSize)) removeFile write sync renameFile

/-- Read only the keeper prefix and settle the original selected layout. -/
def reopenMarkedBoundedWith [Monad m] [MonadExceptOf IO.Error m] (dir : DiskDirectory)
    (readOptional : FilePath → m (Option ByteArray))
    (list : FilePath → m (Array IO.FS.DirEntry)) (lstat : FilePath → m (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → m ByteArray) (readPrefix : FilePath → Nat → m KeeperPrefix)
    (removeFile : FilePath → m (Except IO.Error Unit)) (write : FilePath → ByteArray → m Unit)
    (sync : Array FilePath → m Unit) (renameFile : FilePath → FilePath → m Unit) : m Reopened := do
  let (plan, reopened, keeperFileSize) ← prepareBoundedMarkedWith dir readOptional list lstat readBin readPrefix
  finishBoundedMarkedOpen dir plan keeperFileSize removeFile write sync renameFile
  return reopened

end Alvoki.Storage.WalSegmentRepair
