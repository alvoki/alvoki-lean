import Alvoki.Storage.Disk.WAL.CollectionRange
import Alvoki.Storage.Disk.WAL.WalSegmentReadIO
import Alvoki.Storage.Disk.RunFileSelection

namespace Alvoki.Storage

open System
open WAL (frameSize)

/-- A sealed file's end comes from its own size. After a partial collection,
the next observed filename can be separated from this file by a gap. -/
def walCollectionEnd (first keeper : Nat) (range : MarkedWalRange) (metadata : IO.FS.Metadata) :
    Option Nat :=
  let bytes := metadata.byteSize.toNat
  let last := first + bytes / frameSize
  if (metadata.type == .file) ∧ metadata.numLinks = 1 ∧ 0 < bytes ∧ bytes % frameSize = 0 ∧
      last ≤ keeper ∧ last ≤ range.watermark then some last else none

/-- Retain the metadata from the same canonical, no-follow probe that
admitted the address. A listed name may already be absent. -/
def readWalSegmentExtentWith [Monad m] [MonadExceptOf IO.Error m] (directory : DiskDirectory)
    (lstat : FilePath → m (Except IO.Error IO.FS.Metadata)) (name : String) :
    m (Option (Nat × IO.FS.Metadata)) := do
  let some first := parseWalSegmentName name | return none
  let path := directory.file (.walSegment first)
  let report ← lstat path
  match classifyWalSegmentLookup path first report with
  | .error error => throw error
  | .ok none => return none
  | .ok (some offset) => return report.toOption.map (offset, ·)

def readWalSegmentExtentsWith [Monad m] [MonadExceptOf IO.Error m] (directory : DiskDirectory)
    (lstat : FilePath → m (Except IO.Error IO.FS.Metadata)) (names : List String) :
    m (List (Nat × IO.FS.Metadata)) := do
  let extents ← names.filterMapM (readWalSegmentExtentWith directory lstat)
  return extents.mergeSort (fun left right => left.1 ≤ right.1)

def walCollectionOffsetsFromExtents (extents : List (Nat × IO.FS.Metadata)) (keeper : Nat)
    (range : MarkedWalRange) : List Nat :=
  extents.filterMap fun (first, metadata) =>
    if first = keeper then none else (walCollectionEnd first keeper range metadata).map (fun _ => first)

/-- The recovered suffix must still reach the installed keeper. Check each
required sealed span by its observed size and the keeper by the exact
settled size. Older covered segments may have gaps between them. -/
def checkWalCollectionSuffix (through keeper : Nat) : List (Nat × IO.FS.Metadata) → Bool
  | [] => false
  | [(first, metadata)] => first == keeper && metadata.byteSize.toNat == (through - keeper) * frameSize
  | (first, metadata) :: (next, nextMetadata) :: rest =>
    first < next && metadata.byteSize.toNat == (next - first) * frameSize &&
      checkWalCollectionSuffix through keeper ((next, nextMetadata) :: rest)

def checkWalCollectionInventory (extents : List (Nat × IO.FS.Metadata)) (keeper : Nat)
    (range : MarkedWalRange) : Bool :=
  match selectWalSegmentReadsThrough (extents.map (·.1)) range.watermark range.through with
  | some (start :: _, []) =>
    checkWalCollectionSuffix range.through keeper (extents.dropWhile fun entry => entry.1 < start)
  | _ => false

/-- Observe a strict pair and its physical inventory using read-only
callbacks while the caller holds the existing sequential writer session.
Exact completeness depends on the native directory enumeration contract. -/
def planWalCollectionWith [Monad m] [MonadExceptOf IO.Error m] (directory : DiskDirectory)
    (generation : UInt64) (walBytes keeper : Nat)
    (readOptional : FilePath → m (Option ByteArray))
    (list : FilePath → m (Array IO.FS.DirEntry))
    (lstat : FilePath → m (Except IO.Error IO.FS.Metadata)) : m (List Nat) := do
  let manifest ← readOptional (directory.file .manifest)
  let _ ← liftExcept ((validateIntegrityRunCollectionGeneration generation manifest).mapError IO.userError)
  let marker ← readOptional (directory.file .walBoundary)
  let pair : DirectoryPublication.Bindings := ⟨manifest, marker⟩
  let some range := pair.walRange | throw (IO.userError "invalid checkpoint and WAL marker for collection")
  unless walBytes = range.through * frameSize do
    throw (IO.userError "installed WAL byte count disagrees with its durable marker")
  let entries ← list directory.path
  let extents ← readWalSegmentExtentsWith directory lstat (entries.toList.map (·.fileName))
  unless checkWalCollectionInventory extents keeper range do
    throw (IO.userError "WAL collection inventory disagrees with the installed keeper")
  return walCollectionOffsetsFromExtents extents keeper range

end Alvoki.Storage
