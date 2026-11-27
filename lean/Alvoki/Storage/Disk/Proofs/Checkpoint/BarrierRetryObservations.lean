import Alvoki.Storage.Disk.Proofs.Filesystem.FileObservationFrame
import Alvoki.Storage.Disk.Proofs.Checkpoint.PhysicalWalAtBarrier

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair

/-- The reported names and durable inode bytes of one checkpoint survivor. -/
structure CheckpointSurvivingFiles where
  names : FilePath → Option Nat
  bytes : Nat → List ByteArray

/-- Frame the names recovery can select and the durable bytes of their
objects. Other names and objects have no role in this handoff. -/
def CheckpointSurvivingFiles.Frames (selectedPath : FilePath → Prop)
    (before after : CheckpointSurvivingFiles) : Prop :=
  FileObservationFrame CheckpointSurvivingFiles.names CheckpointSurvivingFiles.bytes selectedPath before after

private theorem CheckpointSurvivingFiles.Frames.rfl {selectedPath} {files : CheckpointSurvivingFiles} : files.Frames selectedPath files :=
  fun _ _ => ⟨Eq.refl _, fun _ _ => Eq.refl _⟩

theorem CheckpointSurvivingFiles.Frames.trans {selectedPath} {first middle last : CheckpointSurvivingFiles}
    (earlier : first.Frames selectedPath middle) (later : middle.Frames selectedPath last) : first.Frames selectedPath last :=
  FileObservationFrame.trans earlier later

abbrev CheckpointAdmissionState := DescriptorInventory × LockedFileState FileImage × CheckpointSurvivingFiles

/-- The guards reached an append-open of the lock file. An error at
that invocation returns before flock, retaining any raw descriptor or
lock-file effects reported by the failed open. -/
structure CheckpointBarrierLockOpenFailure (directory : DiskDirectory) (before : LockedFileState FileImage)
    (files reached : CheckpointSurvivingFiles) where
  input : FilePath
  census : DescriptorInventory
  afterCensus : DescriptorInventory
  realPath : FilePath → EStateM IO.Error CheckpointAdmissionState FilePath
  lookup : FilePath → EStateM IO.Error CheckpointAdmissionState (Except IO.Error IO.FS.Metadata)
  openAppend : FilePath → EStateM IO.Error CheckpointAdmissionState DescriptorSlot
  resolved : realPath input (census, before, files) = .ok directory.path (census, before, files)
  flat : optionalMetadataWith (lookup (directory.file .wal)) (census, before, files) = .ok none (census, before, files)
  lock : Option IO.FS.Metadata
  probed : optionalMetadataWith (lookup (directory.file .lock)) (census, before, files) = .ok lock (census, before, files)
  safe : ∀ metadata, lock = some metadata → (metadata.type == .file && metadata.numLinks == 1) = true
  cause : IO.Error
  failed : openAppend (directory.file .lock) (census, before, files) = .error cause (afterCensus, before, reached)

theorem CheckpointBarrierLockOpenFailure.returns {directory before files reached}
    (failure : CheckpointBarrierLockOpenFailure directory before files reached)
    (acquire : DiskDirectory → DescriptorSlot → EStateM IO.Error CheckpointAdmissionState SegmentedSession) :
    DiskTable.withOpenAdmission failure.input failure.realPath failure.lookup failure.openAppend acquire
      (failure.census, before, files) = .error failure.cause (failure.afterCensus, before, reached) :=
  DiskTable.withOpenAdmission_lockOpenError failure.realPath failure.lookup failure.openAppend acquire
    failure.resolved failure.flat failure.probed failure.safe failure.failed

/-- The first directory barrier of an already settled image can report
an error before or after taking effect. These failed admissions and
preparations issue no selected file writes. The reports give their local
namespace and byte frames and the exact returned cleanup state. -/
inductive CheckpointBarrierRetryPrefix (directory : DiskDirectory) (keeper : Nat)
    (selectedPath : FilePath → Prop) (initial : LockedFileState FileImage) (survivor : CheckpointSurvivingFiles) :
    LockedFileState FileImage → CheckpointSurvivingFiles → Prop where
  | start : CheckpointBarrierRetryPrefix directory keeper selectedPath initial survivor initial survivor
  | lockOpenFailed {before : LockedFileState FileImage} {atOpen reached : CheckpointSurvivingFiles}
      (prior : CheckpointBarrierRetryPrefix directory keeper selectedPath initial survivor before atOpen)
      (failure : CheckpointBarrierLockOpenFailure directory before atOpen reached)
      (frame : atOpen.Frames selectedPath reached) :
      CheckpointBarrierRetryPrefix directory keeper selectedPath initial survivor before reached
  | prefixFailed {before : LockedFileState FileImage} {files : Type} {atOpen reached : CheckpointSurvivingFiles}
      (prior : CheckpointBarrierRetryPrefix directory keeper selectedPath initial survivor before atOpen)
      (failure : CachedOpenPrefixFailure files directory before) (unchanged : failure.reached = before.image)
      (frame : atOpen.Frames selectedPath reached) :
      CheckpointBarrierRetryPrefix directory keeper selectedPath initial survivor failure.after reached
  | rejected {before : LockedFileState FileImage} {atOpen reached : CheckpointSurvivingFiles}
      (prior : CheckpointBarrierRetryPrefix directory keeper selectedPath initial survivor before atOpen)
      (rejection : CachedOpenRejection directory before) (frame : atOpen.Frames selectedPath reached) :
      CheckpointBarrierRetryPrefix directory keeper selectedPath initial survivor rejection.after reached
  | authorizationFailed {before : LockedFileState FileImage} {atOpen reached : CheckpointSurvivingFiles}
      (prior : CheckpointBarrierRetryPrefix directory keeper selectedPath initial survivor before atOpen)
      (failure : CachedOpenAuthorizationFailure directory before) (first : failure.target.first = keeper)
      (frame : atOpen.Frames selectedPath reached) :
      CheckpointBarrierRetryPrefix directory keeper selectedPath initial survivor failure.after reached
  | referenceDrops {before : LockedFileState FileImage} {description : Nat} {atDrop : CheckpointSurvivingFiles}
      (prior : CheckpointBarrierRetryPrefix directory keeper selectedPath initial survivor before atDrop)
      (references : HeldLockReferences description) (drops : List LockReferenceDrop) :
      CheckpointBarrierRetryPrefix directory keeper selectedPath initial survivor
        (references.afterFileDrops drops directory before) atDrop

/-- Preserve the selected files through the actual reported failure and
drop endpoints. The authorization failure may settle the directory again. -/
theorem CheckpointBarrierRetryPrefix.reached {directory keeper selectedPath initial survivor after files}
    (attempts : CheckpointBarrierRetryPrefix directory keeper selectedPath initial survivor after files)
    (settled : initial.image.syncDirectory = initial.image) :
    ReportedReopenPrefix directory keeper initial after ∧ after.image = initial.image ∧ survivor.Frames selectedPath files := by
  induction attempts with
  | start => exact ⟨.start, rfl, .rfl⟩
  | lockOpenFailed _ _ frame ih =>
    exact ⟨ih.1, ih.2.1, CheckpointSurvivingFiles.Frames.trans ih.2.2 frame⟩
  | prefixFailed _ failure unchanged frame ih =>
    exact ⟨.prefixFailed ih.1 failure unchanged, unchanged.trans ih.2.1, CheckpointSurvivingFiles.Frames.trans ih.2.2 frame⟩
  | rejected _ rejection frame ih =>
    refine ⟨.rejected ih.1 rejection, ?_, CheckpointSurvivingFiles.Frames.trans ih.2.2 frame⟩
    simp only [CachedOpenRejection.after, CachedOpenAttempt.cleanupError_keepsFiles, ih.2.1]
  | authorizationFailed _ failed first frame ih =>
    refine ⟨.authorizationFailed ih.1 failed first, ?_, CheckpointSurvivingFiles.Frames.trans ih.2.2 frame⟩
    rcases failed.imageOutcome with unchanged | sync
    · exact unchanged.trans ih.2.1
    · exact sync.trans ((congrArg FileImage.syncDirectory ih.2.1).trans settled)
  | referenceDrops _ references drops ih =>
    exact ⟨.referenceDrops ih.1 references drops, ih.2.1, ih.2.2⟩

/-- Protect the manifest, marked WAL and only the run names selected by
that crash manifest. -/
def checkpointSurvivorPath (directory : DiskDirectory) (before : SegmentedWriterState)
    (binding : Option ByteArray) (path : FilePath) : Prop :=
  path = directory.file .manifest ∨ checkpointWalPath directory before path ∨
  ∃ bytes metadata index, binding = some bytes ∧ Manifest.IntegrityCheckpoint.decode bytes = .ok metadata ∧
    index < metadata.header.runCount.toNat ∧ path = directory.file (.run metadata.header.generation index)

end Alvoki.Storage.DiskSession
