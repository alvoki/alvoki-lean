import Alvoki.Storage.Disk.Proofs.Native.Recovery.NativeMarkedReadPrefix
import Alvoki.Storage.Disk.Checkpoint.PhysicalBarrierReopen

namespace Alvoki.Storage.DiskSession

open System Manifest WalSegmentRepair

/-- One report of the surviving names and durable bytes, shared by all
selected file reads. Reboot starts without a pre-existing descriptor. -/
structure WriteCrashView where
  names : FilePath → Option Nat
  contents : Nat → ByteArray
  rebootObjects : Nat → Nat

def WriteCrashView.reboot (crash : WriteCrashView) : DescriptorInventory :=
  ⟨[], by simp, crash.rebootObjects⟩

/-- The admitted marked open reads the selected files of the reported
survivor. The lineage permits either an already aligned keeper or the
reported repair of a longer keeper and visible suffix. -/
structure NativeWriteCrashReads {state : NativeReadyState} (crash : WriteCrashView) (input : FilePath)
    {retry : LockedFileState FileImage} (vacant : TryLockObserves retry.owners state.session.directory (.ok true))
    {history : List WAL.Write} (layout : CanonicalKeeperLayout retry.image history)
    (selected : SelectedIntegrityCheckpoint state.writer.published.durable
      retry.image.directory.active.manifest state.writer.checkpoint) where
  opening : MarkedReadyOpenObservations input state.session.directory crash.reboot
    retry layout state.writer.published vacant selected
  directory : opening.reads.bindings state.session.directory.path = crash.names state.session.directory.path
  lock : opening.reads.bindings (state.session.directory.file .lock) = crash.names (state.session.directory.file .lock)
  manifest : CheckpointCrashChild crash.names opening.admission
    (state.session.directory.file .manifest) "MANIFEST"
  marker : CheckpointCrashChild crash.names opening.admission
    (state.session.directory.file .walBoundary) "WAL.commit"
  runs : ∀ bytes manifest, retry.image.directory.active.manifest = some bytes →
    IntegrityCheckpoint.decode bytes = .ok manifest → ∀ index < manifest.header.runCount.toNat,
      CheckpointCrashChild crash.names opening.admission
        (state.session.directory.file (.run manifest.header.generation index))
        (renderRunFileName manifest.header.generation index)
  wal : ∀ segment ∈ layout.sealed ++ [layout.keeper], CheckpointCrashChild crash.names opening.admission
    (state.session.directory.file (.walSegment segment.first)) (renderWalSegmentName segment.first)
  bytes : ∀ inode payload, opening.reads.reads.objectBytes inode = some payload → crash.contents inode = payload
  previousTokens : state.session.phaseRef ∈ opening.callbacks.liveRefs ∧
    state.session.sessionRef ∈ opening.callbacks.liveRefs

namespace NativeWriteCrashReads

variable {state : NativeReadyState} {crash : WriteCrashView} {input : FilePath} {history : List WAL.Write}
  {retry : LockedFileState FileImage} {vacant : TryLockObserves retry.owners state.session.directory (.ok true)}
  {layout : CanonicalKeeperLayout retry.image history}
  {selected : SelectedIntegrityCheckpoint state.writer.published.durable
    retry.image.directory.active.manifest state.writer.checkpoint}

/-- The no-follow stat and chunk reads identify the same survivor
inode and its reported durable bytes. -/
def ReadsSurvivor (seen : NativeWriteCrashReads crash input vacant layout selected)
    (path : FilePath) (payload : ByteArray) : Prop :=
  ∃ read : seen.opening.reads.reads.ObservesFile path payload,
    crash.names path = some read.object ∧ crash.contents read.object = payload

private theorem readsFile (seen : NativeWriteCrashReads crash input vacant layout selected)
    {path : FilePath} {name : String} {object : DeviceInode} {payload : ByteArray}
    (child : CheckpointCrashChild crash.names seen.opening.admission path name)
    (bound : seen.opening.admission.view.child seen.opening.admission.root name = some object)
    (contents : seen.opening.reads.reads.objectBytes (seen.opening.admission.view.modelObject object) = some payload)
    (calls : RunChunkPathReport seen.opening.reads.reads path name seen.opening.admission.root seen.opening.admission.view) :
    seen.ReadsSurvivor path payload :=
  ⟨calls.observesFile bound contents, child.sameObject calls bound contents,
    seen.bytes _ _ (calls.observesFile bound contents).contents⟩

theorem readsManifest (seen : NativeWriteCrashReads crash input vacant layout selected) {bytes : ByteArray}
    (present : retry.image.directory.active.manifest = some bytes) :
    seen.ReadsSurvivor (state.session.directory.file .manifest) bytes := by
  obtain ⟨⟨file⟩, _⟩ := seen.opening.reads.metadata.manifestFile bytes present
  exact seen.readsFile seen.manifest file.bound file.contents file.calls

theorem readsRun (seen : NativeWriteCrashReads crash input vacant layout selected) {bytes payload : ByteArray}
    {manifest : IntegrityCheckpoint} (present : retry.image.directory.active.manifest = some bytes)
    (decoded : IntegrityCheckpoint.decode bytes = .ok manifest) {index : Nat}
    (within : index < manifest.header.runCount.toNat)
    (stored : state.writer.published.durable manifest.header.generation index = some payload) :
    seen.ReadsSurvivor (state.session.directory.file (.run manifest.header.generation index)) payload := by
  obtain ⟨_, bound, contents, ⟨calls⟩⟩ :=
    seen.opening.reads.runs bytes manifest present decoded index within payload stored
  exact seen.readsFile (seen.runs bytes manifest present decoded index within) bound contents calls

theorem readsMarker (seen : NativeWriteCrashReads crash input vacant layout selected) {bytes : ByteArray}
    (present : retry.image.directory.active.walBoundary = some bytes) :
    seen.ReadsSurvivor (state.session.directory.file .walBoundary) bytes := by
  obtain ⟨file, _⟩ := seen.opening.reads.metadata.markerFile bytes present
  exact seen.readsFile seen.marker file.bound file.contents file.calls

theorem readsKeeper (seen : NativeWriteCrashReads crash input vacant layout selected) :
    seen.ReadsSurvivor (state.session.directory.file (.walSegment layout.keeper.first))
      (layout.keeper.bytes ++ layout.tail) := by
  let file := seen.opening.reads.wal.keeper
  exact seen.readsFile (seen.wal _ (List.mem_append_right _ (by simp))) file.bound file.contents file.calls

theorem readsSeal (seen : NativeWriteCrashReads crash input vacant layout selected)
    (segment : WalSegment) (present : segment ∈ layout.sealed) :
    seen.ReadsSurvivor (state.session.directory.file (.walSegment segment.first)) segment.bytes := by
  let file := seen.opening.reads.wal.sealedFile segment present
  exact seen.readsFile (seen.wal _ (List.mem_append_left _ present)) file.bound file.contents file.calls

end NativeWriteCrashReads

end Alvoki.Storage.DiskSession
