import Alvoki.Storage.Disk.Proofs.Native.WAL.NativeWalFileFsyncEffects

namespace Alvoki.Storage.DiskSession

open System WalSegmentCommit

/-- The three inodes needed after both regular-file syncs return. -/
structure WalPublicationPayloads where
  keeper : Nat
  oldMarker : Nat
  newMarker : Nat
  keeperBytes : ByteArray
  oldMarkerBytes : ByteArray
  newMarkerBytes : ByteArray

namespace WalPublicationPayloads

/-- The group leaves the old canonical marker in place. Its staged
replacement is already synced but has no authority until rename. -/
structure Grouped (payloads : WalPublicationPayloads) (directory : DiskDirectory) (first : Nat)
    (atGroup : CheckpointStorageObservation) : Prop where
  keeperNamed : atGroup.files.names (directory.file (.walSegment first)) = some payloads.keeper
  oldNamed : atGroup.files.names (directory.file .walBoundary) = some payloads.oldMarker
  stagedNamed : atGroup.files.names (directory.file .stagedWalBoundary) = some payloads.newMarker
  keeperStored : atGroup.files.bytes payloads.keeper = [payloads.keeperBytes]
  oldStored : atGroup.files.bytes payloads.oldMarker = [payloads.oldMarkerBytes]
  stagedStored : atGroup.files.bytes payloads.newMarker = [payloads.newMarkerBytes]
  oldSettled : ∀ names ∈ atGroup.crashNames,
    names (directory.file (.walSegment first)) = some payloads.keeper ∧
    names (directory.file .walBoundary) = some payloads.oldMarker

def markerInode (payloads : WalPublicationPayloads) (published : Bool) : Nat :=
  if published then payloads.newMarker else payloads.oldMarker

def markerBytes (payloads : WalPublicationPayloads) (published : Bool) : ByteArray :=
  if published then payloads.newMarkerBytes else payloads.oldMarkerBytes

/-- One namespace map supplies both named inodes and their own durable
payloads. Changing the selected marker does not change the full keeper. -/
structure Selection (payloads : WalPublicationPayloads) (directory : DiskDirectory) (first : Nat)
    (atHeap : CheckpointStorageObservation) (names : FilePath → Option Nat) (published : Bool) : Prop where
  keeperNamed : names (directory.file (.walSegment first)) = some payloads.keeper
  keeperStored : atHeap.files.bytes payloads.keeper = [payloads.keeperBytes]
  markerNamed : names (directory.file .walBoundary) = some (payloads.markerInode published)
  markerStored : atHeap.files.bytes (payloads.markerInode published) = [payloads.markerBytes published]

structure Selections (payloads : WalPublicationPayloads) (directory : DiskDirectory) (first : Nat)
    (atHeap : CheckpointStorageObservation) (liveNew : Bool) (allows : Bool → Prop) : Prop where
  live : payloads.Selection directory first atHeap atHeap.files.names liveNew
  survivors : ∀ names ∈ atHeap.crashNames, ∃ published,
    allows published ∧ payloads.Selection directory first atHeap names published

/-- A cache read preserves the two publication paths in the live map
and in one preceding map for each survivor. The old marker may be
named only in that preceding crash map. -/
structure CacheReadFrame (directory : DiskDirectory) (first : Nat)
    (before reached : CheckpointStorageObservation) : Prop where
  live : before.files.Frames
    (fun path => path = directory.file (.walSegment first) ∨ path = directory.file .walBoundary) reached.files
  survivors : ∀ names ∈ reached.crashNames, ∃ prior ∈ before.crashNames,
    (⟨prior, before.files.bytes⟩ : CheckpointSurvivingFiles).Frames
      (fun path => path = directory.file (.walSegment first) ∨ path = directory.file .walBoundary)
      ⟨names, reached.files.bytes⟩

theorem Selections.frameCacheRead {payloads : WalPublicationPayloads} {directory : DiskDirectory} {first : Nat}
    {before reached : CheckpointStorageObservation} {liveNew : Bool} {allows : Bool → Prop}
    (selected : payloads.Selections directory first before liveNew allows)
    (frame : CacheReadFrame directory first before reached) :
    payloads.Selections directory first reached liveNew allows := by
  have transfer {names prior : FilePath → Option Nat} {published : Bool}
      (kept : (⟨prior, before.files.bytes⟩ : CheckpointSurvivingFiles).Frames
        (fun path => path = directory.file (.walSegment first) ∨ path = directory.file .walBoundary)
        ⟨names, reached.files.bytes⟩)
      (one : payloads.Selection directory first before prior published) :
      payloads.Selection directory first reached names published := by
    obtain ⟨keeper, keeperBytes⟩ := kept _ (.inl rfl)
    obtain ⟨marker, markerBytes⟩ := kept _ (.inr rfl)
    exact ⟨keeper.trans one.keeperNamed, (keeperBytes _ one.keeperNamed).trans one.keeperStored,
      marker.trans one.markerNamed, (markerBytes _ one.markerNamed).trans one.markerStored⟩
  refine ⟨transfer frame.live selected.live, ?_⟩
  intro names survives
  obtain ⟨prior, possible, same⟩ := frame.survivors names survives
  obtain ⟨published, allowed, one⟩ := selected.survivors prior possible
  exact ⟨published, allowed, transfer same one⟩

end WalPublicationPayloads

/-- Observed binding update of a same-directory marker replacement. -/
def walMarkerRenameBinding (names : DiskFile → Option Nat) (staged : Nat) : DiskFile → Option Nat
  | .walBoundary => some staged
  | .stagedWalBoundary => none
  | file => names file

/-- The physical rename either keeps the reached live names or moves
the stage to the canonical name. Each crash map is related to one prior
map for all modeled database paths, with or without the same replacement.
Bytes on a selected object are unchanged regardless of that choice. -/
structure WalMarkerRenameEffect (directory : DiskDirectory) (staged : Nat) (effective : Bool)
    (entry reached : CheckpointStorageObservation) : Prop where
  visible : ∀ file, reached.files.names (directory.file file) =
    if effective then walMarkerRenameBinding (entry.files.names ∘ directory.file) staged file
    else entry.files.names (directory.file file)
  survivors : ∀ names ∈ reached.crashNames, ∃ prior ∈ entry.crashNames,
    ∃ survives : Bool, (survives = true → effective = true) ∧ ∀ file, names (directory.file file) =
      if survives then walMarkerRenameBinding (prior ∘ directory.file) staged file
      else prior (directory.file file)
  bytes : ∀ names, names = reached.files.names ∨ names ∈ reached.crashNames → ∀ file inode,
    names (directory.file file) = some inode → reached.files.bytes inode = entry.files.bytes inode

theorem WalMarkerRenameEffect.selects {directory : DiskDirectory} {first : Nat}
    {payloads : WalPublicationPayloads} {entry reached : CheckpointStorageObservation} {effective : Bool}
    (group : payloads.Grouped directory first entry)
    (effect : WalMarkerRenameEffect directory payloads.newMarker effective entry reached) :
    payloads.Selections directory first reached effective (fun published => published = true → effective = true) := by
  have emits {names : FilePath → Option Nat} {new : Bool}
      (available : names = reached.files.names ∨ names ∈ reached.crashNames)
      (keeper : names (directory.file (.walSegment first)) = some payloads.keeper)
      (marker : names (directory.file .walBoundary) = some (payloads.markerInode new)) :
      payloads.Selection directory first reached names new := by
    refine ⟨keeper, (effect.bytes _ available _ _ keeper).trans group.keeperStored, marker, ?_⟩
    rw [effect.bytes _ available _ _ marker]
    cases new
    · exact group.oldStored
    · exact group.stagedStored
  constructor
  · apply emits (.inl rfl)
    · simpa [walMarkerRenameBinding, group.keeperNamed] using effect.visible (.walSegment first)
    · cases chosen : effective <;>
        simpa [walMarkerRenameBinding, WalPublicationPayloads.markerInode, group.oldNamed, chosen] using
          effect.visible .walBoundary
  · intro names allowed
    obtain ⟨prior, possible, survives, relevant, updated⟩ := effect.survivors names allowed
    obtain ⟨keeper, marker⟩ := group.oldSettled prior possible
    refine ⟨survives, relevant, emits (.inr allowed) ?_ ?_⟩
    · simpa [walMarkerRenameBinding, keeper] using updated (.walSegment first)
    · cases chosen : survives <;>
        simpa [walMarkerRenameBinding, WalPublicationPayloads.markerInode, marker, chosen] using updated .walBoundary

/-- A directory sync preserves the visible child bindings and file bytes.
An effective sync settles all child paths together. A before-effect
failure lets each surviving map come from one earlier map instead. -/
structure WalRootSyncEffect (directory : DiskDirectory) (effective : Bool)
    (entry reached : CheckpointStorageObservation) : Prop where
  visible : ∀ file, reached.files.names (directory.file file) = entry.files.names (directory.file file)
  settled : effective = true → ∀ names ∈ reached.crashNames, ∀ file,
    names (directory.file file) = reached.files.names (directory.file file)
  unchanged : effective = false → ∀ names ∈ reached.crashNames, ∃ prior ∈ entry.crashNames,
    ∀ file, names (directory.file file) = prior (directory.file file)
  bytes : ∀ names, names = reached.files.names ∨ names ∈ reached.crashNames → ∀ file inode,
    names (directory.file file) = some inode → reached.files.bytes inode = entry.files.bytes inode

theorem WalRootSyncEffect.selects {directory : DiskDirectory} {first : Nat}
    {payloads : WalPublicationPayloads} {entry reached : CheckpointStorageObservation} {effective : Bool}
    {allowed : Bool → Prop} (renamed : payloads.Selections directory first entry true allowed)
    (effect : WalRootSyncEffect directory effective entry reached) :
    payloads.Selections directory first reached true
      (fun published => if effective then published = true else allowed published) := by
  have transfer {names prior : FilePath → Option Nat} {published : Bool}
      (available : names = reached.files.names ∨ names ∈ reached.crashNames)
      (binding : ∀ file, names (directory.file file) = prior (directory.file file))
      (seen : payloads.Selection directory first entry prior published) :
      payloads.Selection directory first reached names published := by
    have keeper := (binding (.walSegment first)).trans seen.keeperNamed
    have marker := (binding .walBoundary).trans seen.markerNamed
    exact ⟨keeper, (effect.bytes _ available _ _ keeper).trans seen.keeperStored,
      marker, (effect.bytes _ available _ _ marker).trans seen.markerStored⟩
  refine ⟨transfer (.inl rfl) effect.visible renamed.live, ?_⟩
  intro names survives
  cases applied : effective with
  | false =>
    obtain ⟨prior, possible, same⟩ := effect.unchanged applied names survives
    obtain ⟨published, selected, observed⟩ := renamed.survivors prior possible
    exact ⟨published, selected, transfer (.inr survives) same observed⟩
  | true =>
    exact ⟨true, rfl, transfer (.inr survives)
      (fun file => (effect.settled applied names survives file).trans (effect.visible file)) renamed.live⟩

end Alvoki.Storage.DiskSession
