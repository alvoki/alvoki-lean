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
  · exact first.visible.trans second.visible
  · intro names allowed
    obtain ⟨intermediate, possible, kept⟩ := second.survivors names allowed
    obtain ⟨prior, earlier, preserved⟩ := first.survivors intermediate possible
    exact ⟨prior, earlier, fun path keep => (kept path keep).trans (preserved path keep)⟩

theorem CheckpointStorageObservation.Frames.weaken {entry reached : CheckpointStorageObservation}
    {footprint scope : FilePath → Prop} (frame : entry.Frames footprint reached)
    (included : ∀ path, scope path → footprint path) : entry.Frames scope reached := by
  constructor
  · exact fun path keep => frame.visible path (included path keep)
  · intro names allowed
    obtain ⟨prior, earlier, same⟩ := frame.survivors names allowed
    exact ⟨prior, earlier, fun path keep => same path (included path keep)⟩

/-- Changes outside the selected paths may create a crash choice from the earlier
live map or from an earlier crash map. One predecessor covers the entire scope. -/
structure CheckpointStorageObservation.NameFrame (scope : FilePath → Prop)
    (before after : CheckpointStorageObservation) : Prop where
  live : ∀ path, scope path → after.files.names path = before.files.names path
  survivors : ∀ names ∈ after.crashNames, ∃ prior, (prior = before.files.names ∨ prior ∈ before.crashNames) ∧
    ∀ path, scope path → names path = prior path

theorem CheckpointStorageObservation.NameFrame.trans {scope : FilePath → Prop}
    {first middle last : CheckpointStorageObservation}
    (left : first.NameFrame scope middle) (right : middle.NameFrame scope last) : first.NameFrame scope last := by
  refine ⟨fun path inside => (right.live path inside).trans (left.live path inside), ?_⟩
  intro names possible
  obtain ⟨intermediate, prior | prior, same⟩ := right.survivors names possible
  · subst intermediate
    exact ⟨_, .inl rfl, fun path inside => (same path inside).trans (left.live path inside)⟩
  · obtain ⟨original, allowed, kept⟩ := left.survivors intermediate prior
    exact ⟨original, allowed, fun path inside => (same path inside).trans (kept path inside)⟩

theorem CheckpointStorageObservation.NameFrame.settledFrom {scope : FilePath → Prop}
    {before after : CheckpointStorageObservation} (frame : before.NameFrame scope after)
    (settled : ∀ names ∈ before.crashNames, ∀ path, scope path → names path = before.files.names path) :
    ∀ names ∈ after.crashNames, ∀ path, scope path → names path = before.files.names path := by
  intro names possible path inside
  obtain ⟨prior, rfl | previous, same⟩ := frame.survivors names possible
  · exact same path inside
  · exact (same path inside).trans (settled prior previous path inside)

theorem CheckpointStorageObservation.Frames.nameFrame {entry reached : CheckpointStorageObservation}
    {scope : FilePath → Prop} (frame : entry.Frames scope reached) : entry.NameFrame scope reached :=
  ⟨fun path inside => (frame.visible path inside).1, fun names possible => by
    obtain ⟨prior, allowed, kept⟩ := frame.survivors names possible
    exact ⟨prior, .inr allowed, kept⟩⟩

/-- Settlement of a footprint survives a joint namespace frame. -/
theorem CheckpointStorageObservation.Frames.settledFrom {entry reached : CheckpointStorageObservation}
    {footprint : FilePath → Prop} (frame : entry.Frames footprint reached)
    (settled : ∀ names ∈ entry.crashNames, ∀ path, footprint path → names path = entry.files.names path) :
    ∀ names ∈ reached.crashNames, ∀ path, footprint path → names path = reached.files.names path := by
  intro names allowed path selected
  exact (frame.nameFrame.settledFrom settled names allowed path selected).trans
    (frame.nameFrame.live path selected).symm

/-- Preserve the durable contents of every inode reachable at a scoped
path in a surviving namespace. The live file frame alone only covers
inodes still bound in the live namespace. -/
structure CheckpointStorageObservation.CrashFileFrame (scope : FilePath → Prop)
    (before after : CheckpointStorageObservation) : Prop extends before.Frames scope after where
  bytes : ∀ names ∈ after.crashNames, ∀ path, scope path → ∀ inode, names path = some inode →
    ∀ payload ∈ after.files.bytes inode, payload ∈ before.files.bytes inode

namespace CheckpointStorageObservation.CrashFileFrame

theorem refl (scope : FilePath → Prop) (atHeap : CheckpointStorageObservation) : atHeap.CrashFileFrame scope atHeap :=
  ⟨.refl _ _, fun _ _ _ _ _ _ _ present => present⟩

theorem trans {scope : FilePath → Prop} {first middle last : CheckpointStorageObservation}
    (firstFrame : first.CrashFileFrame scope middle) (lastFrame : middle.CrashFileFrame scope last) :
    first.CrashFileFrame scope last := by
  refine ⟨firstFrame.toFrames.trans lastFrame.toFrames, ?_⟩
  intro names allowed path inside inode bound payload possible
  obtain ⟨prior, earlier, same⟩ := lastFrame.toFrames.survivors names allowed
  exact firstFrame.bytes prior earlier path inside inode ((same path inside).symm.trans bound) payload
    (lastFrame.bytes names allowed path inside inode bound payload possible)

end CheckpointStorageObservation.CrashFileFrame

/-- Transport the selected file together with its durable payload. -/
theorem CheckpointSurvivingFiles.Frames.stored {footprint : FilePath → Prop}
    {first last : CheckpointSurvivingFiles} (frame : first.Frames footprint last)
    {path : FilePath} {payload : ByteArray} (selected : footprint path)
    (initial : first.Stored path payload) : last.Stored path payload := by
  obtain ⟨inode, bound, durable⟩ := initial
  obtain ⟨name, bytes⟩ := frame path selected
  exact ⟨inode, name.trans bound, (bytes inode bound).trans durable⟩

/-- An exclusive create installs the new inode. A crash can also keep
the path's earlier live or durable binding. -/
structure ExclusiveCreateNameEffect (path : FilePath) (inode : Nat)
    (before after : CheckpointStorageObservation) : Prop where
  named : after.files.names path = some inode
  survivors : ∀ names ∈ after.crashNames, names path = some inode ∨
    ∃ prior, (prior = before.files.names ∨ prior ∈ before.crashNames) ∧ names path = prior path

/-- A regular-file fsync changes crash bytes at one inode. The
observation keeps both the visible names and the joint crash maps. -/
structure RegularFileSyncEffect (inode : Nat) (choices : List ByteArray)
    (entry reached : CheckpointStorageObservation) : Prop where
  names : reached.files.names = entry.files.names
  crashNames : reached.crashNames = entry.crashNames
  bytes : ∀ other, reached.files.bytes other = if other = inode then choices else entry.files.bytes other

theorem RegularFileSyncEffect.frames {inode : Nat} {choices : List ByteArray}
    {entry reached : CheckpointStorageObservation} (effect : RegularFileSyncEffect inode choices entry reached)
    {footprint : FilePath → Prop}
    (apart : ∀ path, footprint path → ∀ other, entry.files.names path = some other → other ≠ inode) :
    entry.Frames footprint reached := by
  constructor
  · intro path keep
    refine ⟨congrFun effect.names path, fun other bound => ?_⟩
    simpa [apart path keep other bound] using effect.bytes other
  · intro names allowed
    exact ⟨names, effect.crashNames ▸ allowed, fun _ _ => rfl⟩

theorem RegularFileSyncEffect.stored {inode : Nat} {payload : ByteArray}
    {entry reached : CheckpointStorageObservation} (effect : RegularFileSyncEffect inode [payload] entry reached)
    {path : FilePath} (bound : entry.files.names path = some inode) : reached.files.Stored path payload :=
  ⟨inode, (congrFun effect.names path).trans bound, by simpa using effect.bytes inode⟩

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

/-- Project the primitive file sync effect into the storage observation.
The choices can describe a completed sync, a partial effect, or the
original crash bytes when the syscall had no effect. -/
theorem RunDirectoryInodeView.fileSyncEffect {directory : DiskDirectory}
    {before after : WalInodeImage} {oldRuns newRuns : RunUnlinkImage}
    (entry : RunDirectoryInodeView directory before oldRuns) (reached : RunDirectoryInodeView directory after newRuns)
    {inode : Nat} {choices : List ByteArray}
    (bytes : after = before.reportFileSync inode choices)
    (names : reached.visible = entry.visible) (crashNames : reached.crashBindings = entry.crashBindings) :
    RegularFileSyncEffect inode choices entry.storageObservation reached.storageObservation := by
  refine ⟨names, crashNames, fun other => ?_⟩
  change after.crashBytes other = _
  rw [bytes]
  rfl

end Alvoki.Storage.CheckpointPublication

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair
open WAL.Boundary (WalInodeImage)

variable {heap image : Type} {view : OpenCloseHeapView heap image}
  {directory : DiskDirectory} {selected issued reached : heap} {handle : IO.FS.Handle} {reason : FilePath}

/-- The reached descriptor identifies the staged inode. Its durable byte
choices can vary independently of the protected paths, provided those
paths did not name that inode at the syscall. -/
theorem RawFsyncTarget.fileEffectFrames
    (target : RawFsyncTarget view selected issued handle)
    (entry after : CheckpointStorageObservation) (path : FilePath) {choices : List ByteArray}
    {footprint : FilePath → Prop}
    (named : entry.files.names path = some ((view.descriptors issued).inode (view.handle issued handle).2.1.description))
    (outside : ∀ path, footprint path →
      entry.files.names path ≠ some ((view.descriptors issued).inode (view.handle issued handle).2.1.description))
    (effect : RegularFileSyncEffect ((view.descriptors issued).inode (view.handle issued handle).2.1.description)
      choices entry after) :
    entry.files.names path = some ((view.handle selected handle).1.inode (view.handle selected handle).2.1.description) ∧
    entry.Frames footprint after := by
  refine ⟨named.trans (congrArg some target.inode), effect.frames ?_⟩
  intro other keep inode binding same
  exact outside other keep (binding.trans (congrArg some same))

/-- A literal stopped file sync acts on the inode still held at the
issue heap. Before any effect it leaves durable bytes unchanged. After
the reported effect it changes only that inode's durable choices. -/
theorem RawFsyncTarget.stoppedRunFrames
    (target : RawFsyncTarget view selected issued handle)
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
  let issuedInode := (view.descriptors issued).inode (view.handle issued handle).2.1.description
  let choices := if effective then [(inodes issued).visible issuedInode] else (inodes issued).crashBytes issuedInode
  have reported : inodes reached = (inodes issued).reportFileSync issuedInode choices := by
    rw [bytes]
    cases effective with
    | true => rfl
    | false =>
      have unchanged : (inodes issued).crashBytes =
          ((inodes issued).reportFileSync issuedInode ((inodes issued).crashBytes issuedInode)).crashBytes := by
        funext other
        by_cases same : other = issuedInode <;> simp [WalInodeImage.reportFileSync, same]
      exact congrArg (fun durable => { inodes issued with crashBytes := durable }) unchanged
  exact target.fileEffectFrames (observe issued).storageObservation (observe reached).storageObservation path
    bound (fun other keep alias => separate other keep (privateBinding other alias))
    ((observe issued).fileSyncEffect (observe reached) reported visible surviving)

/-- Apply the successful regular-file law at the actual issued syscall.
The descriptor's inode and the visible path must agree at issue. -/
theorem RawFsyncTarget.returnedFileEffect
    (target : RawFsyncTarget view selected issued handle)
    (calls : RawSyncCalls heap) (returned : calls.fsync handle issued = .ok () reached)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ heap, RunDirectoryInodeView directory (inodes heap) (runs heap))
    (path : FilePath)
    (effect : calls.fsync handle issued = .ok () reached →
      let inode := (view.descriptors issued).inode (view.handle issued handle).2.1.description
      (observe issued).visible path = some inode ∧
      inodes reached = (inodes issued).completeFileSync inode ∧
      (observe reached).visible = (observe issued).visible ∧
      (observe reached).crashBindings = (observe issued).crashBindings) :
    let inode := (view.handle selected handle).1.inode (view.handle selected handle).2.1.description
    (observe issued).visible path = some inode ∧
    RegularFileSyncEffect inode [(inodes issued).visible inode]
      (observe issued).storageObservation (observe reached).storageObservation := by
  intro inode
  obtain ⟨bound, bytes, names, survivors⟩ := effect returned
  rw [target.inode] at bound bytes
  exact ⟨bound, (observe issued).fileSyncEffect (observe reached) bytes names survivors⟩

/-- The first directory fsync leaves inode bytes unchanged. An effective
barrier may settle all visible names, but a protected name that was
already settled agrees with one earlier joint choice. -/
theorem RawFsyncTarget.stoppedDirectoryFrames
    (target : RawFsyncTarget view selected issued handle)
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
