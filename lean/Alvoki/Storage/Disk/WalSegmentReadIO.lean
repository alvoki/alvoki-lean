import Alvoki.Storage.Disk.WalSegmentFileName
import Alvoki.Storage.Disk.WriteAheadLog

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

/-- Split the ordered suffix after the last start at or before the marker.
Later addresses are needed only as names for a possible repair. -/
def selectWalSegmentReadsThrough (offsets : List Nat) (watermark through : Nat) :
    Option (List Nat × List Nat) := do
  let (_, selected) ← selectWalSegmentReads offsets watermark
  let needed := fun start => decide (start ≤ through)
  pure (selected.takeWhile needed, selected.dropWhile needed)

structure WalSegmentMarkerReads where
  files : List (Nat × ByteArray)
  newer : List Nat

/-- Check the absolute WAL marker before running any selected read.
The callback receives its cutoff as an absolute frame offset. -/
@[macro_inline] def withAbsoluteWalCutoff [Monad m] [MonadExceptOf IO.Error m]
    (watermark : Nat) (length : UInt64) (read : Nat → m α) : m α := do
  let through := length.toNat / WAL.frameSize
  unless length.toNat % WAL.frameSize = 0 ∧ watermark ≤ through do
    throw (IO.userError "invalid absolute WAL segment marker")
  read through

/-- A rejected marker stops at the entry heap, before the callback.
An accepted marker reaches exactly the callback with the selected cutoff. -/
theorem withAbsoluteWalCutoff_estate {heap α : Type} (watermark : Nat) (length : UInt64)
    (read : Nat → EStateM IO.Error heap α) :
    withAbsoluteWalCutoff watermark length read =
      if length.toNat % WAL.frameSize = 0 ∧ watermark ≤ length.toNat / WAL.frameSize then
        read (length.toNat / WAL.frameSize)
      else throw (IO.userError "invalid absolute WAL segment marker") := by
  funext before
  by_cases checked : length.toNat % WAL.frameSize = 0 ∧ watermark ≤ length.toNat / WAL.frameSize <;>
    simp [withAbsoluteWalCutoff, checked, Bind.bind, EStateM.bind, MonadExcept.throw, throwThe,
      MonadExceptOf.throw, EStateM.throw]

/-- Validate the marker's absolute byte count before listing. Check the
later names by metadata too, but read only payloads through the marker. -/
def readWalSegmentsThroughWith [Monad m] [MonadExceptOf IO.Error m] (directory : DiskDirectory)
    (watermark : Nat) (length : UInt64) (list : FilePath → m (Array IO.FS.DirEntry))
    (lstat : FilePath → m (Except IO.Error IO.FS.Metadata)) (readBin : FilePath → m ByteArray) :
    m WalSegmentMarkerReads := do
  let through := length.toNat / WAL.frameSize
  if length.toNat % WAL.frameSize = 0 ∧ watermark ≤ through then
    let entries ← list directory.path
    let offsets ← scanWalSegmentOffsets (probeWalSegmentWith directory lstat) (entries.toList.map (·.fileName))
    let some (required, newer) := selectWalSegmentReadsThrough offsets watermark through
      | throw (IO.userError "no WAL segment covers the checkpoint watermark")
    let payloads ← readWalSegmentPayloadsWith directory readBin required
    pure ⟨required.zip payloads, newer⟩
  else throw (IO.userError "invalid absolute WAL segment marker")

/-- The caller holds the directory lock from the checkpoint and marker
reads through use of this inventory. The byte count came from `WAL.commit`. -/
def readWalSegmentsThrough (directory : DiskDirectory) (watermark : Nat) (length : UInt64) :
    IO WalSegmentMarkerReads :=
  readWalSegmentsThroughWith directory watermark length FilePath.readDir
    (fun path => path.symlinkMetadata.toBaseIO) IO.FS.readBinFile

theorem readWalSegmentsThrough_fileEffects (directory : DiskDirectory) (watermark : Nat) (length : UInt64) :
    readWalSegmentsThrough directory watermark length = (do
      let through := length.toNat / WAL.frameSize
      if length.toNat % WAL.frameSize = 0 ∧ watermark ≤ through then
        let entries ← directory.path.readDir
        let offsets ← scanWalSegmentOffsets
          (probeWalSegmentWith directory fun path => path.symlinkMetadata.toBaseIO) (entries.toList.map (·.fileName))
        let some (required, newer) := selectWalSegmentReadsThrough offsets watermark through
          | throw (IO.userError "no WAL segment covers the checkpoint watermark")
        let payloads ← required.mapM (fun offset => IO.FS.readBinFile (directory.file (.walSegment offset)))
        pure ⟨required.zip payloads, newer⟩
      else throw (IO.userError "invalid absolute WAL segment marker")) := rfl

end Alvoki.Storage
