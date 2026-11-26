import Alvoki.Storage.Disk.NativeReadyPowerLoss
import Alvoki.Storage.Disk.RawHealthyMarkedOpenEffects

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {published : CheckpointPublication.Image} {vacant : TryLockObserves retry.owners directory (.ok true)}
  {checkpoint : Option (PackedTable × UInt64)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {opening : MarkedReadyOpenObservations input directory inventory retry layout published vacant selected}
  {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
  {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)} {stage : LongKeeperStageCallbacks heap}
  {rename : FilePath → FilePath → EStateM IO.Error heap Unit}

namespace RawHealthyMarkedOpenEffects

variable (seen : RawHealthyMarkedOpenEffects opening view calls init entry phaseIdentity tokenIdentity
  allocatePhase allocateToken stream remove stage rename)
  (files : heap → CheckpointSurvivingFiles)

/-- The returned cache directory and acquired flock handle name the
objects observed at this admission's entry. The actual entry census may
already contain other live descriptions. -/
theorem entryAuthority
    (root : (files entry).names directory.path = opening.reads.bindings directory.path)
    (lock : (files entry).names (directory.file .lock) = opening.reads.bindings (directory.file .lock)) :
    (files entry).names directory.path = some ((view.handle seen.seed.afterPending seen.seed.handle).1.inode
      (view.handle seen.seed.afterPending seen.seed.handle).2.1.description) ∧
    (files entry).names (directory.file .lock) = some ((view.handle seen.raw.afterFlock seen.raw.lock).1.inode
      (view.handle seen.raw.afterFlock seen.raw.lock).2.1.description) := by
  have bound := opening.reads.sameObjects
  constructor
  · rw [seen.seed.sameHandle, seen.seed.openedHandle]
    exact root.trans bound.1
  · rw [seen.raw.sameLock, seen.raw.appendHandle]
    exact lock.trans bound.2.1

end RawHealthyMarkedOpenEffects

/-- A stat tied to the actual entry cannot attribute the read to a
different inode with the same bytes. -/
theorem _root_.Alvoki.Storage.WalSegmentRepair.CheckpointRunChunkReads.ObservesFile.matchesStoredEntry {reads : CheckpointRunChunkReads}
    {path : FilePath} {payload : ByteArray} (read : reads.ObservesFile path payload)
    (files : CheckpointSurvivingFiles)
    (actualName : ∀ metadata inode, reads.stat path = .ok (metadata, inode) → files.names path = some inode)
    (stored : files.Stored path payload) :
    files.names path = some read.object ∧ files.bytes read.object = [payload] := by
  obtain ⟨inode, bound, bytes⟩ := stored
  have named := actualName _ _ read.stat
  have same := Option.some.inj (bound.symm.trans named)
  exact ⟨named, same ▸ bytes⟩

namespace MarkedReadyOpenObservations

variable (opening : MarkedReadyOpenObservations input directory inventory retry layout published vacant selected)
  (files : CheckpointSurvivingFiles)

/-- The selected marker is read from the exact inode at the observed
entry, with its known bytes. -/
theorem readsEntryMarker {payload : ByteArray}
    (selectedMarker : retry.image.directory.active.walBoundary = some payload)
    (actualName : ∀ metadata inode,
      opening.reads.reads.stat (directory.file .walBoundary) = .ok (metadata, inode) →
      files.names (directory.file .walBoundary) = some inode)
    (stored : files.Stored (directory.file .walBoundary) payload) :
    ∃ read : opening.reads.reads.ObservesFile (directory.file .walBoundary) payload,
      files.names (directory.file .walBoundary) = some read.object ∧ files.bytes read.object = [payload] := by
  obtain ⟨file, _⟩ := opening.reads.metadata.markerFile payload selectedMarker
  let read := file.observesFile
  exact ⟨read, read.matchesStoredEntry files actualName stored⟩

/-- The chronological reader uses the actual observed inode and extent
bytes of each selected immutable seal. -/
theorem readsEntrySeal (segment : WalSegment) (chosen : segment ∈ layout.sealed)
    (actualName : ∀ metadata inode,
      opening.reads.reads.stat (directory.file (.walSegment segment.first)) = .ok (metadata, inode) →
      files.names (directory.file (.walSegment segment.first)) = some inode)
    (stored : files.Stored (directory.file (.walSegment segment.first)) segment.bytes) :
    ∃ read : opening.reads.reads.ObservesFile (directory.file (.walSegment segment.first)) segment.bytes,
      files.names (directory.file (.walSegment segment.first)) = some read.object ∧
        files.bytes read.object = [segment.bytes] := by
  let read := (opening.reads.wal.sealedFile segment chosen).observesFile
  exact ⟨read, read.matchesStoredEntry files actualName stored⟩

end MarkedReadyOpenObservations

end Alvoki.Storage.DiskSession
