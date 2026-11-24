import Alvoki.Storage.Disk.IntegrityCheckpointRead
import Alvoki.Storage.Disk.WalSegmentMarkerRead
import Alvoki.Storage.Disk.WalSegmentRepairIO

namespace Alvoki.Storage.WalSegmentRepair

open System

structure Reopened where
  table : PackedTable
  generation : UInt64
  walBytes : UInt64
  keeper : Nat

private def validate [Monad m] [MonadExceptOf IO.Error m] (result : Except String α) : m α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

/-- Prepare the exact selected checkpoint, WAL table and repair target
without modifying the directory. The caller holds its database lock. -/
def prepareMarkedWith [Monad m] [MonadExceptOf IO.Error m] (directory : DiskDirectory)
    (readOptional : FilePath → m (Option ByteArray))
    (list : FilePath → m (Array IO.FS.DirEntry)) (lstat : FilePath → m (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → m ByteArray) : m (Plan × Reopened) := do
  let checkpoint ← readIntegrityCheckpoint (readOptional (directory.file .manifest))
    (fun generation index => readBin (directory.file (.run generation index))) validate
  let (base, generation) := checkpoint.getD (.empty, 0)
  let some marker ← readOptional (directory.file .walBoundary)
    | throw (IO.userError "segmented WAL is missing its commit marker")
  let length ← validate (WAL.Boundary.decode marker)
  let reads ← readWalSegmentsThroughWith directory base.committed.toNat length list lstat readBin
  let (_, table) ← validate (recoverMarkedWalSegments base length reads.files)
  let some (keeper, keeperBytes) := reads.files.getLast?
    | throw (IO.userError "no WAL segment covers the commit marker")
  pure (⟨length.toNat / WAL.frameSize, keeper, reads.newer, keeperBytes⟩,
    ⟨table, generation, length, keeper⟩)

/-- Recover an already marked segmented WAL under the caller's database
lock. Return the prepared table and offsets after the repair barriers have
settled. The caller keeps the paths stable through the schedule. -/
def reopenMarkedWith [Monad m] [MonadExceptOf IO.Error m] (directory : DiskDirectory)
    (readOptional : FilePath → m (Option ByteArray))
    (list : FilePath → m (Array IO.FS.DirEntry)) (lstat : FilePath → m (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → m ByteArray) (removeFile : FilePath → m (Except IO.Error Unit))
    (write : FilePath → ByteArray → m Unit) (sync : Array FilePath → m Unit)
    (renameFile : FilePath → FilePath → m Unit) : m Reopened := do
  let (plan, reopened) ← prepareMarkedWith directory readOptional list lstat readBin
  runAt directory (pure plan) removeFile write sync renameFile
  pure reopened

theorem prepareMarkedWith_reported (directory : DiskDirectory)
    (readOptional : FilePath → Except IO.Error (Option ByteArray))
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → Except IO.Error ByteArray) {checkpoint : Option (PackedTable × UInt64)}
    (checkpointRead : readIntegrityCheckpoint (readOptional (directory.file .manifest))
      (fun generation index => readBin (directory.file (.run generation index)))
      (fun report => report.mapError IO.userError) = .ok checkpoint)
    {marker : ByteArray} {length : UInt64} {reads : WalSegmentMarkerReads}
    (markerRead : readOptional (directory.file .walBoundary) = .ok (some marker))
    (decoded : WAL.Boundary.decode marker = .ok length)
    (walRead : readWalSegmentsThroughWith directory (checkpoint.getD (.empty, 0)).1.committed.toNat
      length list lstat readBin = .ok reads)
    {selected : ByteArray} {table : PackedTable} {keeper : Nat} {keeperBytes : ByteArray}
    (recovered : recoverMarkedWalSegments (checkpoint.getD (.empty, 0)).1 length reads.files =
      .ok (selected, table))
    (target : reads.files.getLast? = some (keeper, keeperBytes)) :
    prepareMarkedWith directory readOptional list lstat readBin =
      .ok (⟨length.toNat / WAL.frameSize, keeper, reads.newer, keeperBytes⟩,
        ⟨table, (checkpoint.getD (.empty, 0)).2, length, keeper⟩) := by
  have translate : (fun {β : Type} (report : Except String β) => (validate report : Except IO.Error β)) =
      (fun {β : Type} report => report.mapError IO.userError) := by
    funext β report
    cases report <;> rfl
  simp [prepareMarkedWith, translate, checkpointRead, markerRead, decoded, walRead, recovered, target,
    validate, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem reopenMarkedWith_reported [Monad m] [LawfulMonad m] [MonadExceptOf IO.Error m]
    (directory : DiskDirectory) (readOptional : FilePath → m (Option ByteArray))
    (list : FilePath → m (Array IO.FS.DirEntry)) (lstat : FilePath → m (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → m ByteArray) (removeFile : FilePath → m (Except IO.Error Unit))
    (write : FilePath → ByteArray → m Unit) (sync : Array FilePath → m Unit)
    (renameFile : FilePath → FilePath → m Unit) {plan : Plan} {reopened : Reopened}
    (prepared : prepareMarkedWith directory readOptional list lstat readBin = pure (plan, reopened))
    (settled : runAt directory (pure plan) removeFile write sync renameFile = pure ()) :
    reopenMarkedWith directory readOptional list lstat readBin removeFile write sync renameFile =
      pure reopened := by
  simp [reopenMarkedWith, prepared, settled]

end Alvoki.Storage.WalSegmentRepair
