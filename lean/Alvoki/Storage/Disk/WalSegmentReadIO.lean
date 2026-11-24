import Alvoki.Storage.Disk.WalSegmentFileName

namespace Alvoki.Storage
open System

/-- Only Linux ENOENT supplies absence. A canonical nonregular entry must
stop the plan before it can select an older segment as active. -/
def classifyWalSegmentLookup (path : FilePath) (first : Nat) (result : Except IO.Error IO.FS.Metadata) :
    Except IO.Error (Option Nat) :=
  match result with
  | .ok metadata =>
    if metadata.type == .file then .ok (some first)
    else .error (IO.userError s!"expected a regular WAL segment: '{path}'")
  | .error error@(.noFileOrDirectory _ osCode _) =>
    if osCode == 2 then .ok none else .error error
  | .error error => .error error

def probeWalSegmentWith [Monad m] [MonadExceptOf IO.Error m] (directory : DiskDirectory)
    (lstat : FilePath → m (Except IO.Error IO.FS.Metadata)) (first : Nat) : m (Option Nat) := do
  let path := directory.file (.walSegment first)
  match classifyWalSegmentLookup path first (← lstat path) with
  | .ok found => pure found
  | .error error => throw error

def probeListedWalSegment [Monad m] (probe : Nat → m (Option Nat)) (name : String) : m (Option Nat) :=
  match parseWalSegmentName name with
  | none => pure none
  | some first => probe first

def scanWalSegmentOffsets [Monad m] (probe : Nat → m (Option Nat)) (names : List String) : m (List Nat) :=
  (·.mergeSort) <$> names.filterMapM (probeListedWalSegment probe)

/-- Select the greatest present start at or below the checkpoint watermark,
then keep the ordered addresses from that start onward. Older addresses
can have gaps. -/
def selectWalSegmentReads (offsets : List Nat) (watermark : Nat) : Option (Nat × List Nat) := do
  let first ← (offsets.filter (fun offset => decide (offset ≤ watermark))).max?
  return (first, offsets.filter (fun offset => decide (first ≤ offset)))

def readWalSegmentPayloadsWith [Monad m] (directory : DiskDirectory) (readBin : FilePath → m ByteArray)
    (offsets : List Nat) : m (List ByteArray) :=
  offsets.mapM (fun first => readBin (directory.file (.walSegment first)))

/-- Under a caller-held lock, list the canonical directory, finish all
canonical no-follow metadata lookups, and read the selected paths in order.
The result contains the first offset, the planned offsets, and the raw
payloads. Layout and marker coverage validation come after acquisition. -/
def readWalSegmentsWith [Monad m] [MonadExceptOf IO.Error m] (directory : DiskDirectory) (watermark : Nat)
    (list : FilePath → m (Array IO.FS.DirEntry)) (lstat : FilePath → m (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → m ByteArray) : m (Nat × List Nat × List ByteArray) := do
  let entries ← list directory.path
  let offsets ← scanWalSegmentOffsets (probeWalSegmentWith directory lstat) (entries.toList.map (·.fileName))
  let some (first, selected) := selectWalSegmentReads offsets watermark
    | throw (IO.userError "no WAL segment covers the checkpoint watermark")
  let payloads ← readWalSegmentPayloadsWith directory readBin selected
  pure (first, selected, payloads)

/-- Native acquisition uses the same stable-directory and regular-file
binding contract as the lock-held inventory. -/
def readWalSegments (directory : DiskDirectory) (watermark : Nat) : IO (Nat × List Nat × List ByteArray) :=
  readWalSegmentsWith directory watermark FilePath.readDir (fun path => path.symlinkMetadata.toBaseIO)
    IO.FS.readBinFile

theorem readWalSegments_fileEffects (directory : DiskDirectory) (watermark : Nat) :
    readWalSegments directory watermark = (do
      let entries ← directory.path.readDir
      let offsets ← scanWalSegmentOffsets (fun first => do
        let path := directory.file (.walSegment first)
        match classifyWalSegmentLookup path first (← path.symlinkMetadata.toBaseIO) with
        | .ok found => pure found
        | .error error => throw error) (entries.toList.map (·.fileName))
      let some (first, selected) := selectWalSegmentReads offsets watermark
        | throw (IO.userError "no WAL segment covers the checkpoint watermark")
      let payloads ← selected.mapM (fun offset => IO.FS.readBinFile (directory.file (.walSegment offset)))
      pure (first, selected, payloads)) := rfl

end Alvoki.Storage
