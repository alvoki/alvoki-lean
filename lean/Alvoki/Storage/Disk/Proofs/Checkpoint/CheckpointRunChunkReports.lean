import Alvoki.Storage.Disk.Proofs.Filesystem.DescriptorInventory
import Alvoki.Storage.Disk.ReadRecoveryPrefix
import Alvoki.Storage.Disk.Proofs.WAL.WalSegmentSizedCheckpointReports

namespace Alvoki.Storage.WalSegmentRepair

open System Manifest DiskSession

/-- Observations for bounded file reads. A stat pairs the native
metadata with its observed object identity. A successful open reports its
reached inventory, slot and initial cursor. Separate opens can reuse a
numeric slot with a different description. -/
structure CheckpointRunChunkReads where
  stat : FilePath → Except IO.Error (IO.FS.Metadata × Nat)
  openRead : FilePath → Except IO.Error (DescriptorInventory × DescriptorSlot × Nat)
  objectBytes : Nat → Option ByteArray
  readChunk : Nat → USize → EStateM IO.Error Nat ByteArray

/-- Project the read result for the exact opened description. The payload
callback discards its cursor, which the primitive model retains on error. -/
def CheckpointRunChunkReads.readOpenedPrefix (reads : CheckpointRunChunkReads) (mismatch : IO.Error)
    (opened : DescriptorInventory × DescriptorSlot × Nat) (count : Nat) : Except IO.Error ByteArray :=
  let (_, slot, offset) := opened
  match readExactPrefixWith mismatch
    (reads.readChunk slot.description) count ByteArray.empty offset with
  | .ok bytes _ => .ok bytes
  | .error cause _ => .error cause

def CheckpointRunChunkReads.readFilePrefix (reads : CheckpointRunChunkReads) (mismatch : IO.Error)
    (path : FilePath) (count : Nat) : Except IO.Error ByteArray :=
  reads.openRead path >>= fun opened => reads.readOpenedPrefix mismatch opened count

def CheckpointRunChunkReads.readPrefix (reads : CheckpointRunChunkReads) : FilePath → Nat → Except IO.Error ByteArray :=
  reads.readFilePrefix (IO.userError checkpointIntegrityMismatch)

/-- At one immutable run path, validate the connection to the known
published bytes. Successful stat and open observations share an object
identity. The observed fresh open supplies offset zero. The chunk reports
interpret the same description as live at each reached read. -/
structure CheckpointRunChunkReads.ObservesFile (reads : CheckpointRunChunkReads)
    (path : FilePath) (payload : ByteArray) where
  metadata : IO.FS.Metadata
  object : Nat
  inventory : DescriptorInventory
  slot : DescriptorSlot
  stat : reads.stat path = .ok (metadata, object)
  regular : metadata.type = .file
  extent : metadata.byteSize.toNat = payload.size
  opened : reads.openRead path = .ok (inventory, slot, 0)
  live : slot ∈ inventory.slots
  sameObject : inventory.inode slot.description = object
  contents : reads.objectBytes object = some payload
  observes : ∀ source, reads.objectBytes (inventory.inode slot.description) = some source →
    PrefixChunkObserves source (reads.readChunk slot.description)
  healthy : ∀ source, reads.objectBytes (inventory.inode slot.description) = some source →
    PrefixChunksAvailable source (reads.readChunk slot.description)

theorem CheckpointRunChunkReads.ObservesFile.readOpenedExactPrefix
    {reads : CheckpointRunChunkReads} {path : FilePath} {payload : ByteArray}
    (seen : reads.ObservesFile path payload) (mismatch : IO.Error) (count : Nat)
    (fits : count < USize.size) (covered : count ≤ payload.size) :
    reads.readOpenedPrefix mismatch (seen.inventory, seen.slot, 0) count = .ok (payload.extract 0 count) := by
  have source : reads.objectBytes (seen.inventory.inode seen.slot.description) = some payload := by
    rw [seen.sameObject, seen.contents]
  have read := readExactPrefixWith_completesAtStart mismatch
    (seen.observes payload source) (seen.healthy payload source) count fits covered
  simp [CheckpointRunChunkReads.readOpenedPrefix, read]

theorem CheckpointRunChunkReads.ObservesFile.readExact
    {reads : CheckpointRunChunkReads} {path : FilePath} {payload : ByteArray}
    (seen : reads.ObservesFile path payload) (fits : payload.size < USize.size) :
    reads.readPrefix path payload.size = .ok payload := by
  simp [CheckpointRunChunkReads.readPrefix, CheckpointRunChunkReads.readFilePrefix, seen.opened,
    seen.readOpenedExactPrefix _ _ fits (Nat.le_refl _), Bind.bind, Except.bind]

/-- Opened-file observations for precisely the runs selected by the manifest. -/
abbrev CheckpointRunChunkReads.ObservesSelected (reads : CheckpointRunChunkReads) (directory : DiskDirectory)
    (binding : Option ByteArray) (durable : CheckpointPublication.RunFiles) : Prop :=
  ∀ bytes manifest, binding = some bytes → IntegrityCheckpoint.decode bytes = .ok manifest →
    ∀ index, index < manifest.header.runCount.toNat → ∀ payload,
      durable manifest.header.generation index = some payload →
      Nonempty (reads.ObservesFile (directory.file (.run manifest.header.generation index)) payload)

/-- Only the strict manifest's selected generation and ordered indices
need these observations. The committed checkpoint proves the size bound;
the immutable published binding, same-object open and primitive chunk
reports supply the bytes consumed by the existing sized checkpoint reader. -/
def SizedCheckpointRunReports.ofChunkReads {directory : DiskDirectory}
    {reports : OpenPathReadReports} {binding : Option ByteArray} {durable : CheckpointPublication.RunFiles}
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint durable binding checkpoint)
    (reads : CheckpointRunChunkReads)
    (metadata : ∀ path, reports.lstat path = (reads.stat path).map Prod.fst)
    (observes : reads.ObservesSelected directory binding durable) :
    SizedCheckpointRunReports directory reports binding durable where
  readPrefix := reads.readPrefix
  runs := by
    intro bytes manifest visible decoded index within payload stored
    obtain ⟨seen⟩ := observes bytes manifest visible decoded index within payload stored
    refine ⟨seen.metadata, ?_, seen.regular, seen.extent, seen.readExact
      (selected.runSizeFits visible decoded within stored)⟩
    rw [metadata, seen.stat]
    rfl

end Alvoki.Storage.WalSegmentRepair
