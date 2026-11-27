import Alvoki.Storage.Disk.WAL.WalSegmentOpenFast

namespace Alvoki.Storage.WalSegmentRepair

open System
open WAL (frameSize)

/-- Keep the observed physical size separate from the bytes needed by replay
and replacement. Unread keeper tail bytes are never represented as input. -/
structure KeeperPrefix where
  bytes : ByteArray
  fileSize : Nat

def readSelectedWithPrefix [Monad m] [MonadExceptOf IO.Error m]
    (dir : DiskDirectory) (watermark : Nat) (length : UInt64)
    (list : FilePath → m (Array IO.FS.DirEntry)) (lstat : FilePath → m (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → m ByteArray) (readPrefix : FilePath → Nat → m KeeperPrefix) :
    m (WalSegmentMarkerReads × Nat) :=
  withAbsoluteWalCutoff watermark length fun through => do
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

/-- Replay the exact strict checkpoint against the absolute marker and selected WAL. -/
@[inline] def prepareBoundedMarkedFromReaders [Monad m] [MonadExceptOf IO.Error m] (dir : DiskDirectory)
    (readCheckpoint : m (Option (PackedTable × UInt64)))
    (readOptional : FilePath → m (Option ByteArray))
    (readWal : Nat → UInt64 → m (WalSegmentMarkerReads × Nat)) :
    m (Plan × Reopened × Nat) := do
  let checkpoint ← readCheckpoint
  let (base, generation) := checkpoint.getD (.empty, 0)
  let some marker ← readOptional (dir.file .walBoundary)
    | throw (IO.userError "segmented WAL is missing its commit marker")
  let length ← liftExcept ((WAL.Boundary.decode marker).mapError IO.userError)
  let (reads, keeperFileSize) ← readWal base.committed.toNat length
  let (_, table) ← liftExcept ((recoverMarkedWalSegments base length reads.files).mapError IO.userError)
  let some (keeper, keeperBytes) := reads.files.getLast?
    | throw (IO.userError "no WAL segment covers the commit marker")
  return (⟨length.toNat / frameSize, keeper, reads.newer, keeperBytes⟩,
    ⟨table, generation, length, keeper⟩, keeperFileSize)

/-- Prepare with the original sealed reads and marker-bounded keeper. -/
def prepareBoundedMarkedFromCheckpoint [Monad m] [MonadExceptOf IO.Error m] (dir : DiskDirectory)
    (readCheckpoint : m (Option (PackedTable × UInt64)))
    (readOptional : FilePath → m (Option ByteArray))
    (list : FilePath → m (Array IO.FS.DirEntry)) (lstat : FilePath → m (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → m ByteArray) (readPrefix : FilePath → Nat → m KeeperPrefix) :
    m (Plan × Reopened × Nat) :=
  prepareBoundedMarkedFromReaders dir readCheckpoint readOptional
    (fun watermark length => readSelectedWithPrefix dir watermark length list lstat readBin readPrefix)

/-- Strict read-only preparation, using the same checkpoint, absolute marker,
canonical inventory and replay checks as the complete-payload worker. -/
def prepareBoundedMarkedWith [Monad m] [MonadExceptOf IO.Error m] (dir : DiskDirectory)
    (readOptional : FilePath → m (Option ByteArray))
    (list : FilePath → m (Array IO.FS.DirEntry)) (lstat : FilePath → m (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → m ByteArray) (readPrefix : FilePath → Nat → m KeeperPrefix) :
    m (Plan × Reopened × Nat) :=
  prepareBoundedMarkedFromCheckpoint dir
    (readIntegrityCheckpoint (readOptional (dir.file .manifest))
      (fun generation index => readBin (dir.file (.run generation index)))
      (fun report => liftExcept (report.mapError IO.userError)))
    readOptional list lstat readBin readPrefix

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

/-- The bounded reader takes earlier payloads from the same selected path
order and requests exactly the marker-selected bytes at the keeper path. -/
theorem readSelectedWithPrefix_reported (dir : DiskDirectory) (watermark : Nat) (length : UInt64)
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → Except IO.Error ByteArray)
    (readPrefix : FilePath → Nat → Except IO.Error KeeperPrefix)
    (checked : length.toNat % frameSize = 0 ∧ watermark ≤ length.toNat / frameSize)
    {entries : Array IO.FS.DirEntry} (listed : list dir.path = .ok entries)
    {offsets sealed newer : List Nat} {keeper : Nat}
    (scanned : scanWalSegmentOffsets (probeWalSegmentWith dir lstat) (entries.toList.map (·.fileName)) =
      .ok offsets)
    (addresses : selectWalSegmentReadsThrough offsets watermark (length.toNat / frameSize) =
      some (sealed ++ [keeper], newer))
    {files : List ByteArray} (payloads : readWalSegmentPayloadsWith dir readBin sealed = .ok files)
    {kept : KeeperPrefix} (read : readPrefix (dir.file (.walSegment keeper))
      ((length.toNat / frameSize - keeper) * frameSize) = .ok kept)
    (size : kept.bytes.size = (length.toNat / frameSize - keeper) * frameSize)
    (covers : (length.toNat / frameSize - keeper) * frameSize ≤ kept.fileSize) :
    readSelectedWithPrefix dir watermark length list lstat readBin readPrefix =
      .ok (⟨sealed.zip files ++ [(keeper, kept.bytes)], newer⟩, kept.fileSize) := by
  simp [readSelectedWithPrefix, withAbsoluteWalCutoff, checked, listed, scanned, addresses, payloads, read, size, covers,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Preparation installs the selected replay and carries the admitted keeper
extent, independently of how the exact checkpoint and WAL bytes were read. -/
theorem prepareBoundedMarkedFromReaders_reported (dir : DiskDirectory)
    (readCheckpoint : Except IO.Error (Option (PackedTable × UInt64)))
    (readOptional : FilePath → Except IO.Error (Option ByteArray))
    (readWal : Nat → UInt64 → Except IO.Error (WalSegmentMarkerReads × Nat))
    {checkpoint : Option (PackedTable × UInt64)} (checkpointRead : readCheckpoint = .ok checkpoint)
    {marker : ByteArray} {length : UInt64}
    (markerRead : readOptional (dir.file .walBoundary) = .ok (some marker))
    (decoded : WAL.Boundary.decode marker = .ok length)
    {reads : WalSegmentMarkerReads} {fileSize : Nat}
    (walRead : readWal (checkpoint.getD (.empty, 0)).1.committed.toNat length = .ok (reads, fileSize))
    {selected : ByteArray} {table : PackedTable} {keeper : Nat} {bytes : ByteArray}
    (replayed : recoverMarkedWalSegments (checkpoint.getD (.empty, 0)).1 length reads.files = .ok (selected, table))
    (keeperRead : reads.files.getLast? = some (keeper, bytes)) :
    prepareBoundedMarkedFromReaders dir readCheckpoint readOptional readWal =
      .ok (⟨length.toNat / frameSize, keeper, reads.newer, bytes⟩,
        ⟨table, (checkpoint.getD (.empty, 0)).2, length, keeper⟩, fileSize) := by
  simp [prepareBoundedMarkedFromReaders, checkpointRead, markerRead, decoded, walRead, replayed, keeperRead,
    liftExcept, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.mapError]

/-- Successful strict checkpoint, marker and bounded payload reports feed
the same selected replay result and carry the keeper's physical size. -/
theorem prepareBoundedMarkedWith_reported (dir : DiskDirectory)
    (readOptional : FilePath → Except IO.Error (Option ByteArray))
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → Except IO.Error ByteArray)
    (readPrefix : FilePath → Nat → Except IO.Error KeeperPrefix)
    {checkpoint : Option (PackedTable × UInt64)}
    (checkpointRead : readIntegrityCheckpoint (readOptional (dir.file .manifest))
      (fun generation index => readBin (dir.file (.run generation index)))
      (fun report => report.mapError IO.userError) = .ok checkpoint)
    {marker : ByteArray} {length : UInt64}
    (markerRead : readOptional (dir.file .walBoundary) = .ok (some marker))
    (decoded : WAL.Boundary.decode marker = .ok length)
    {reads : WalSegmentMarkerReads} {fileSize : Nat}
    (walRead : readSelectedWithPrefix dir (checkpoint.getD (.empty, 0)).1.committed.toNat length list lstat
      readBin readPrefix = .ok (reads, fileSize))
    {selected : ByteArray} {table : PackedTable} {keeper : Nat} {bytes : ByteArray}
    (replayed : recoverMarkedWalSegments (checkpoint.getD (.empty, 0)).1 length reads.files = .ok (selected, table))
    (keeperRead : reads.files.getLast? = some (keeper, bytes)) :
    prepareBoundedMarkedWith dir readOptional list lstat readBin readPrefix =
      .ok (⟨length.toNat / frameSize, keeper, reads.newer, bytes⟩,
        ⟨table, (checkpoint.getD (.empty, 0)).2, length, keeper⟩, fileSize) := by
  have validation : (fun {α : Type} (report : Except String α) =>
      (liftExcept (report.mapError IO.userError) : Except IO.Error α)) =
      (fun {α : Type} report => report.mapError IO.userError) := by
    funext α report
    cases report <;> rfl
  unfold prepareBoundedMarkedWith prepareBoundedMarkedFromCheckpoint
  rw [validation]
  exact prepareBoundedMarkedFromReaders_reported dir _ _ _ checkpointRead markerRead decoded walRead replayed keeperRead

end Alvoki.Storage.WalSegmentRepair
