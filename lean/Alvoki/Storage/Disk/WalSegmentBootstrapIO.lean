import Alvoki.Storage.Disk.WalSegmentRepairOpen
import Alvoki.Storage.Disk.WalSegmentRotationIO

namespace Alvoki.Storage.WalSegmentRepair

open System

/-- Finish markerless bootstrap after the locked directory checks. Segment
zero must be durable before publishing the zero marker. -/
@[macro_inline] def bootstrapEmptyWith [Monad m] [MonadExceptOf IO.Error m] (directory : DiskDirectory)
    (empty : Option ByteArray) (createEmpty : FilePath → m Unit)
    (write : FilePath → ByteArray → m Unit) (sync : Array FilePath → m Unit)
    (renameFile : FilePath → FilePath → m Unit) : m Reopened := do
  WalSegmentRotation.runAt directory 0 (fun _ => pure empty) createEmpty (fun path => sync #[path])
  Publication.run (Publication.performReplacement (write · (WAL.Boundary.encode 0))
    sync renameFile (directory.file .stagedWalBoundary) directory.path (fun _ => directory.file .walBoundary) #[])
  pure ⟨.empty, 0, 0, 0⟩

end Alvoki.Storage.WalSegmentRepair
