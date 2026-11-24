import Alvoki.Storage.Disk.WalSegmentRepairOpen
import Alvoki.Storage.Disk.WalSegmentRotationIO
import Alvoki.Storage.Disk.RunFileName

namespace Alvoki.Storage.WalSegmentRepair

open System

def conflictsWithBootstrap (name : String) : Bool :=
  name == "MANIFEST" || name == "MANIFEST.next" || name == "WAL.next" ||
    (name.startsWith "WAL-segment-" && name != renderWalSegmentName 0) ||
    (parseRunFileName name).isSome

/-- Check the owned directory before enabling any bootstrap write. A leftover
marker stage is permitted only alongside a checked empty segment zero. -/
@[macro_inline] def prepareBootstrapWith [Monad m] [MonadExceptOf IO.Error m] (directory : DiskDirectory)
    (list : FilePath → m (Array IO.FS.DirEntry)) (readEmpty : FilePath → m (Option ByteArray))
    (metadata : FilePath → m (Option IO.FS.Metadata)) : m (Option ByteArray) := do
  let entries ← list directory.path
  if entries.any (fun entry => conflictsWithBootstrap entry.fileName) then
    throw (IO.userError WAL.Boundary.missingOpenMarker)
  let empty ← readEmpty (directory.file (.walSegment 0))
  if let some staged ← metadata (directory.file .stagedWalBoundary) then
    unless staged.type == .file && empty.isSome do
      throw (IO.userError WAL.Boundary.missingOpenMarker)
  pure empty

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

@[macro_inline] def bootstrapSegmentedWith [Monad m] [MonadExceptOf IO.Error m] (directory : DiskDirectory)
    (list : FilePath → m (Array IO.FS.DirEntry)) (readEmpty : FilePath → m (Option ByteArray))
    (metadata : FilePath → m (Option IO.FS.Metadata)) (createEmpty : FilePath → m Unit)
    (write : FilePath → ByteArray → m Unit) (sync : Array FilePath → m Unit)
    (renameFile : FilePath → FilePath → m Unit) : m Reopened := do
  let empty ← prepareBootstrapWith directory list readEmpty metadata
  bootstrapEmptyWith directory empty createEmpty write sync renameFile

end Alvoki.Storage.WalSegmentRepair
