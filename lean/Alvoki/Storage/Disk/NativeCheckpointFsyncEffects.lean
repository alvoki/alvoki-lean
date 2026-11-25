import Alvoki.Storage.Disk.NativeCheckpointRawSyncStop
import Alvoki.Storage.Disk.Checkpoint.BarrierRetryObservations
import Alvoki.Storage.Disk.CheckpointRunPrefixCustody

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair
open WAL.Boundary (WalInodeImage)

/-- Keep the visible binding map and the jointly selectable crash maps
at one heap. The byte choices are indexed by inode. -/
structure CheckpointStorageObservation where
  files : CheckpointSurvivingFiles
  crashNames : List (FilePath → Option Nat)

/-- Earlier and later observations agree on the selected footprint.
Each later crash map has one earlier map for all protected paths. -/
structure CheckpointStorageObservation.Frames (footprint : FilePath → Prop)
    (entry reached : CheckpointStorageObservation) : Prop where
  visible : entry.files.Frames footprint reached.files
  survivors : ∀ names ∈ reached.crashNames, ∃ prior ∈ entry.crashNames,
    ∀ path, footprint path → names path = prior path

theorem CheckpointStorageObservation.Frames.refl (footprint : FilePath → Prop)
    (entry : CheckpointStorageObservation) : entry.Frames footprint entry :=
  ⟨fun _ _ => ⟨rfl, fun _ _ => rfl⟩, fun names allowed => ⟨names, allowed, fun _ _ => rfl⟩⟩

theorem CheckpointStorageObservation.Frames.trans {footprint : FilePath → Prop}
    {entry middle reached : CheckpointStorageObservation}
    (first : entry.Frames footprint middle) (second : middle.Frames footprint reached) :
    entry.Frames footprint reached := by
  constructor
  · intro path keep
    obtain ⟨intermediate, persists⟩ := first.visible path keep
    obtain ⟨final, durable⟩ := second.visible path keep
    exact ⟨final.trans intermediate, fun inode named =>
      (durable inode (intermediate.trans named)).trans (persists inode named)⟩
  · intro names allowed
    obtain ⟨intermediate, possible, kept⟩ := second.survivors names allowed
    obtain ⟨prior, earlier, preserved⟩ := first.survivors intermediate possible
    exact ⟨prior, earlier, fun path keep => (kept path keep).trans (preserved path keep)⟩

end Alvoki.Storage.DiskSession

namespace Alvoki.Storage.CheckpointPublication

open System DiskSession WalSegmentRepair
open WAL.Boundary (WalInodeImage)

/-- The scoped observation keeps the run view's actual names paired
with the same inode image. -/
def RunDirectoryInodeView.storageObservation {directory : DiskDirectory}
    {image : WalInodeImage} {runs : RunUnlinkImage} (view : RunDirectoryInodeView directory image runs) :
    CheckpointStorageObservation :=
  ⟨⟨view.visible, image.crashBytes⟩, view.crashBindings⟩

/-- A run write followed by a sync, including a stop, preserves an
unrelated recovery footprint. File synchronization can change the
durable choices only for the inode identified by the issued descriptor. -/
theorem RunWriteInodeFrame.preservesCheckpointFootprint {directory : DiskDirectory}
    {before after : WalInodeImage} {oldRuns newRuns : RunUnlinkImage}
    {path : FilePath} {inode : Nat} {flushed : WalInodeImage}
    {entry : RunDirectoryInodeView directory before oldRuns}
    {reached : RunDirectoryInodeView directory after newRuns}
    (effect : RunWriteInodeFrame path inode flushed entry reached)
    (syncFrame : ∀ other, other ≠ inode → after.crashBytes other = flushed.crashBytes other)
    (privateBinding : ∀ other, entry.visible other = some inode → other = path)
    {footprint : FilePath → Prop} (separate : ∀ other, footprint other → other ≠ path) :
    entry.storageObservation.Frames footprint reached.storageObservation := by
  constructor
  · intro other selected
    refine ⟨effect.visibleNames other (separate other selected), ?_⟩
    intro oldInode bound
    have distinct : oldInode ≠ inode := by
      intro same
      exact separate other selected (privateBinding other (same ▸ bound))
    exact (syncFrame oldInode distinct).trans (effect.crashBytes oldInode distinct)
  · intro names allowed
    obtain ⟨prior, earlier, same⟩ := effect.crashNames names allowed
    exact ⟨prior, earlier, fun other selected => same other (separate other selected)⟩

end Alvoki.Storage.CheckpointPublication

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair
open WAL.Boundary (WalInodeImage)

variable {heap image : Type} {view : OpenCloseHeapView heap image}
  {directory : DiskDirectory} {selected issued reached : heap} {handle : IO.FS.Handle} {reason : FilePath}

/-- A literal stopped file sync acts on the inode still held at the
issue heap. Before any effect it leaves durable bytes unchanged. After
the reported effect it changes only that inode's durable choices. -/
theorem CheckpointFsyncTarget.stoppedRunFrames
    (target : CheckpointFsyncTarget view selected issued handle)
    (calls : CheckpointRawSyncCalls heap) (stopped : calls.fsync handle issued = .error reason reached)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ heap, RunDirectoryInodeView directory (inodes heap) (runs heap))
    (path : FilePath) (effective : Bool)
    (effect : calls.fsync handle issued = .error reason reached →
      let inode := (view.descriptors issued).inode (view.handle issued handle).2.1.description
      (observe issued).visible path = some inode ∧
      (∀ other, (observe issued).visible other = some inode → other = path) ∧
      inodes reached = (if effective then (inodes issued).completeFileSync inode else inodes issued) ∧
      (observe reached).visible = (observe issued).visible ∧
      (observe reached).crashBindings = (observe issued).crashBindings)
    {footprint : FilePath → Prop} (separate : ∀ other, footprint other → other ≠ path) :
    let inode := (view.handle selected handle).1.inode (view.handle selected handle).2.1.description
    (observe issued).visible path = some inode ∧
    (observe issued).storageObservation.Frames footprint (observe reached).storageObservation := by
  intro inode
  obtain ⟨bound, privateBinding, bytes, visible, surviving⟩ := effect stopped
  rw [target.inode] at bound privateBinding bytes
  refine ⟨bound, ?_⟩
  let frame : RunWriteInodeFrame path inode (inodes issued) (observe issued) (observe reached) :=
    ⟨fun other _ => congrFun visible other,
      fun names allowed => ⟨names, surviving ▸ allowed, fun _ _ => rfl⟩,
      fun _ _ => rfl, fun _ _ => rfl⟩
  apply frame.preservesCheckpointFootprint _ privateBinding separate
  intro other distinct
  change inodes reached = (if effective then (inodes issued).completeFileSync inode else inodes issued) at bytes
  rw [bytes]
  cases effective <;> simp [WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, distinct]

/-- The first directory fsync leaves inode bytes unchanged. An effective
barrier may settle all visible names, but a protected name that was
already settled agrees with one earlier joint choice. -/
theorem CheckpointFsyncTarget.stoppedDirectoryFrames
    (target : CheckpointFsyncTarget view selected issued handle)
    (calls : CheckpointRawSyncCalls heap) (stopped : calls.fsync handle issued = .error reason reached)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ heap, RunDirectoryInodeView directory (inodes heap) (runs heap))
    (effective : Bool)
    (effect : calls.fsync handle issued = .error reason reached →
      (observe issued).visible directory.path =
        some ((view.descriptors issued).inode (view.handle issued handle).2.1.description) ∧
      inodes reached = inodes issued ∧ (observe reached).visible = (observe issued).visible ∧
      ∀ names ∈ (observe reached).crashBindings,
        if effective then names = (observe reached).visible else names ∈ (observe issued).crashBindings)
    {footprint : FilePath → Prop}
    (hasChoice : (observe issued).crashBindings ≠ [])
    (settled : ∀ prior ∈ (observe issued).crashBindings, ∀ name, footprint name →
      prior name = (observe issued).visible name) :
    let inode := (view.handle selected handle).1.inode (view.handle selected handle).2.1.description
    (observe issued).visible directory.path = some inode ∧
    (observe issued).storageObservation.Frames footprint (observe reached).storageObservation := by
  intro inode
  obtain ⟨bound, bytes, visible, survives⟩ := effect stopped
  rw [target.inode] at bound
  refine ⟨bound, ?_⟩
  constructor
  · intro path selectedPath
    exact ⟨congrFun visible path, fun inode _ => congrArg (fun image : WalInodeImage => image.crashBytes inode) bytes⟩
  · intro names allowed
    have choice := survives names allowed
    cases effective with
    | false =>
      exact ⟨names, choice, fun _ _ => rfl⟩
    | true =>
      have named : names = (observe reached).visible := choice
      obtain ⟨prior, earlier⟩ := List.exists_mem_of_ne_nil _ hasChoice
      refine ⟨prior, earlier, ?_⟩
      intro path selectedPath
      rw [named, visible]
      exact (settled prior earlier path selectedPath).symm

end Alvoki.Storage.DiskSession
