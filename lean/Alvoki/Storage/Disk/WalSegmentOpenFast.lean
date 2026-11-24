import Alvoki.Storage.Disk.WalSegmentRepairOpen

namespace Alvoki.Storage.WalSegmentRepair

open System

def Plan.alignedWithoutPrune (plan : Plan) : Bool :=
  plan.valid && plan.newer.isEmpty && plan.keeperBytes.size == plan.keeperSize

/-- The first barrier also settles the empty suffix inventory. Sync the
keeper after that barrier so a failed directory sync cannot expose a
keeper sync under an unsettled commit marker. -/
def finishMarkedOpen [Monad m] [MonadExceptOf IO.Error m] (directory : DiskDirectory) (plan : Plan)
    (removeFile : FilePath → m (Except IO.Error Unit)) (write : FilePath → ByteArray → m Unit)
    (sync : Array FilePath → m Unit) (renameFile : FilePath → FilePath → m Unit) : m Unit := do
  if plan.alignedWithoutPrune then
    sync #[directory.path]
    sync #[directory.file (.walSegment plan.keeper)]
  else
    runAt directory (pure plan) removeFile write sync renameFile

/-- Use the same strict preparation and repair as reopenMarkedWith. A
validated, already aligned keeper with no later names needs only the
metadata and keeper barriers. -/
def reopenMarkedFastWith [Monad m] [MonadExceptOf IO.Error m] (directory : DiskDirectory)
    (readOptional : FilePath → m (Option ByteArray))
    (list : FilePath → m (Array IO.FS.DirEntry)) (lstat : FilePath → m (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → m ByteArray) (removeFile : FilePath → m (Except IO.Error Unit))
    (write : FilePath → ByteArray → m Unit) (sync : Array FilePath → m Unit)
    (renameFile : FilePath → FilePath → m Unit) : m Reopened := do
  let (plan, reopened) ← prepareMarkedWith directory readOptional list lstat readBin
  finishMarkedOpen directory plan removeFile write sync renameFile
  pure reopened

end Alvoki.Storage.WalSegmentRepair
