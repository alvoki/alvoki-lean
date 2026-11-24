import Alvoki.Storage.Disk.DiskPaths
import Alvoki.Storage.Disk.WalBoundary
import Alvoki.Storage.Publication.DiskPublication

namespace Alvoki.Storage.WalSegmentCommit

open System

@[inline] def performMarkerAt [Monad m] (dir : DiskDirectory) (activeFirst newBytes : Nat)
    (write : FilePath → ByteArray → m Unit) (sync : Array FilePath → m Unit)
    (rename : FilePath → FilePath → m Unit) : Publication.Step → m Unit :=
  Publication.performReplacement (fun file => write file (WAL.Boundary.encode newBytes.toUInt64))
    sync rename (dir.file .stagedWalBoundary) dir.path (fun _ => dir.file .walBoundary)
    #[dir.file (.walSegment activeFirst)]

/-- Append prepared WAL bytes and publish one absolute byte boundary. -/
@[macro_inline] def commitBytesAt [Monad m] (dir : DiskDirectory) (activeFirst : Nat)
    (bytes : ByteArray) (newBytes : Nat) (append write : FilePath → ByteArray → m Unit)
    (sync : Array FilePath → m Unit) (rename : FilePath → FilePath → m Unit) : m Unit :=
  WAL.Boundary.commit (append (dir.file (.walSegment activeFirst)) bytes)
    (Publication.run (performMarkerAt dir activeFirst newBytes write sync rename))

/-- Append one prepared frame to a stable, existing segment before publishing the
absolute byte count. The caller holds the writer lock and has checked that the
segment ends at the previous marker, and that the new count fits in UInt64.
The append callback writes and flushes that segment. The write callback owns the
distinct staging path and creates a fresh staged marker. -/
@[macro_inline] def commitAt [Monad m] (dir : DiskDirectory) (activeFirst : Nat)
    (event : WAL.Write) (newBytes : Nat) (append write : FilePath → ByteArray → m Unit)
    (sync : Array FilePath → m Unit) (rename : FilePath → FilePath → m Unit) : m Unit :=
  commitBytesAt dir activeFirst (WAL.encodeFrame event) newBytes append write sync rename

/-- Use the existing append-first schedule and one grouped sync for the
active segment and the staged absolute marker. -/
theorem commitAt_fileEffects [Monad m] (dir : DiskDirectory) (activeFirst : Nat)
    (event : WAL.Write) (newBytes : Nat) (append write : FilePath → ByteArray → m Unit)
    (sync : Array FilePath → m Unit) (rename : FilePath → FilePath → m Unit) :
    commitAt dir activeFirst event newBytes append write sync rename =
      WAL.Boundary.commit (append (dir.file (.walSegment activeFirst)) (WAL.encodeFrame event)) (do
        let staged := dir.file .stagedWalBoundary
        write staged (WAL.Boundary.encode newBytes.toUInt64)
        sync #[dir.file (.walSegment activeFirst), staged]
        rename staged (dir.file .walBoundary)
        sync #[dir.path]
        pure ()) := rfl

end Alvoki.Storage.WalSegmentCommit
