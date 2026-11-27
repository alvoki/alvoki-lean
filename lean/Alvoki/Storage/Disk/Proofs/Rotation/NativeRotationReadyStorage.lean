import Alvoki.Storage.Disk.Proofs.Rotation.NativeRotationWriteEntry

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting
open WAL.Boundary (WalInodeImage)

/-- The raw heap's live child and joint crash samples project to the held
directory observation at one WAL path. Bytes follow that path's inode. -/
structure RotationCreateFiles.ObservesWalChild (files : RotationCreateFiles) (root : DeviceInode)
    (directory : DiskDirectory) (start : Nat) (storage : CheckpointStorageObservation)
    (visible : Nat → ByteArray) : Prop where
  live : storage.files.names (directory.file (.walSegment start)) =
    (files.view.child root (renderWalSegmentName start)).map files.view.modelObject
  survivors : ∀ names ∈ storage.crashNames, names (directory.file (.walSegment start)) ∈
    (files.crashNames (renderWalSegmentName start)).map (Option.map files.view.modelObject)
  bytes : ∀ inode, storage.files.names (directory.file (.walSegment start)) = some inode →
    storage.files.bytes inode = files.inodes.crashBytes inode ∧ visible inode = files.inodes.visible inode

private theorem RotationCreateFiles.ObservesWalChild.published
    {files : RotationCreateFiles} {root : DeviceInode} {directory : DiskDirectory} {start : Nat}
    {storage : CheckpointStorageObservation} {visible : Nat → ByteArray}
    (atChild : files.ObservesWalChild root directory start storage visible)
    {child : DeviceInode} {payload : ByteArray}
    (named : files.view.child root (renderWalSegmentName start) = some child)
    (durableName : files.crashNames (renderWalSegmentName start) = [some child])
    (durableBytes : files.inodes.crashBytes (files.view.modelObject child) = [payload])
    (liveBytes : files.inodes.visible (files.view.modelObject child) = payload) :
    let path := directory.file (.walSegment start)
    storage.files.Stored path payload ∧
    (∀ names ∈ storage.crashNames, names path = storage.files.names path) ∧
    ∀ inode, storage.files.names path = some inode → visible inode = payload := by
  have bound := atChild.live.trans (congrArg (Option.map files.view.modelObject) named)
  exact ⟨⟨_, bound, (atChild.bytes _ bound).1.trans durableBytes⟩, fun names chosen => by
    have survives := atChild.survivors names chosen
    rw [durableName, List.map_singleton, List.mem_singleton] at survives
    exact survives.trans bound.symm, fun inode atPath => by
    obtain rfl := Option.some.inj (atPath.symm.trans bound)
    exact (atChild.bytes _ atPath).2.trans liveBytes⟩

/-- The former active keeper becomes a seal. That change requires only
the old keeper's already durable bytes. -/
theorem NativeReadyStorage.protectedAfterRotation
    {state next : NativeReadyState} {storage : CheckpointStorageObservation}
    (old : NativeReadyStorage state storage) (valid : state.Valid)
    (sameWriter : next.writer = state.writer.rotated valid.retained.rotationTarget)
    (sameDirectory : next.session.directory = state.session.directory)
    (sameRoot : next.census.inode next.directorySlot.description = state.census.inode state.directorySlot.description)
    (sameLock : next.census.inode next.owner.description = state.census.inode state.owner.description) :
    NativeReadyProtectedStorage next storage.files := by
  have sameManifest : next.writer.target.pair.manifest = state.writer.target.pair.manifest := by rw [sameWriter]; rfl
  have sameRuns : next.writer.published.durable = state.writer.published.durable := by rw [sameWriter]; rfl
  have seals : next.writer.wal.sealed = state.writer.wal.sealed ++ [state.writer.wal.active] := by rw [sameWriter]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [sameDirectory, sameRoot] using old.directoryBound
  · simpa only [sameDirectory, sameLock] using old.lockBound
  · simpa only [sameManifest, sameDirectory] using old.manifest
  · intro segment member
    rw [seals, List.mem_append, List.mem_singleton] at member
    rw [sameDirectory]
    rcases member with sealed | rfl
    · exact old.sealedFiles _ sealed
    · exact old.keeper
  · intro bytes metadata manifest decoded index inBounds payload durable
    rw [sameManifest] at manifest
    rw [sameRuns] at durable
    exact sameDirectory.symm ▸ old.runs bytes metadata manifest decoded index inBounds payload durable

/-- All protected paths after rotation were already covered, including
the old active keeper now in the sealed list. -/
theorem NativeReadyState.rotationProtectedPaths {state next : NativeReadyState}
    (valid : state.Valid) (sameWriter : next.writer = state.writer.rotated valid.retained.rotationTarget)
    (sameDirectory : next.session.directory = state.session.directory)
    {path : FilePath} (immutable : next.writeFramePath path) : state.crashPath path := by
  have sameManifest : next.writer.target.pair.manifest = state.writer.target.pair.manifest := by rw [sameWriter]; rfl
  have seals : next.writer.wal.sealed = state.writer.wal.sealed ++ [state.writer.wal.active] := by rw [sameWriter]; rfl
  simp only [NativeReadyState.writeFramePath, sameDirectory, sameManifest, seals, List.mem_append,
    List.mem_singleton] at immutable
  apply NativeReadyState.crashPath_iff_write.mpr
  rcases immutable with root | lock | manifest | ⟨segment, member, same⟩ | run
  · exact .inr (.inr (.inl root))
  · exact .inr (.inr (.inr (.inl lock)))
  · exact .inr (.inr (.inr (.inr (.inl manifest))))
  · rcases member with sealed | rfl
    · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨segment, sealed, same⟩)))))
    · exact .inr (.inl same)
  · exact .inr (.inr (.inr (.inr (.inr (.inr run)))))

/-- Rotation adds the new keeper to the old protected footprint. The old
keeper's durable payload now supplies the final sealed descriptor. -/
private theorem NativeReadyStorage.afterRotation
    {state next : NativeReadyState} {before after : CheckpointStorageObservation}
    (initial : NativeReadyStorage state before) (valid : state.Valid)
    (sameWriter : next.writer = state.writer.rotated valid.retained.rotationTarget)
    (sameDirectory : next.session.directory = state.session.directory)
    (sameRoot : next.census.inode next.directorySlot.description = state.census.inode state.directorySlot.description)
    (sameLock : next.census.inode next.owner.description = state.census.inode state.owner.description)
    (keeps : before.Frames state.crashPath after)
    (keeper : after.files.Stored (next.session.directory.file (.walSegment next.writer.wal.active.first))
      next.writer.wal.active.bytes)
    (settlesKeeper : ∀ names ∈ after.crashNames,
      names (next.session.directory.file (.walSegment next.writer.wal.active.first)) =
        after.files.names (next.session.directory.file (.walSegment next.writer.wal.active.first))) :
    NativeReadyStorage next after := by
  have old := initial.frame keeps
  have sameHistory : next.writer.history = state.writer.history := by rw [sameWriter]; rfl
  refine ⟨old.protectedAfterRotation valid sameWriter sameDirectory sameRoot sameLock, ?_, keeper, ?_⟩
  · simpa only [sameDirectory, sameHistory] using old.marker
  · intro names chosen path inside
    rcases NativeReadyState.crashPath_iff_write.mp inside with marker | active | immutable
    · apply old.settled names chosen path
      exact NativeReadyState.crashPath_iff_write.mpr (.inl (sameDirectory ▸ marker))
    · exact active.symm ▸ settlesKeeper names chosen
    · exact old.settled names chosen path (NativeReadyState.rotationProtectedPaths valid sameWriter sameDirectory immutable)

section Reached

variable {heap : Type} {opened : NativeOpenedHandle heap} {current position : NativeOpenedPosition opened}
  {next : NativeReadPosition current.current.history current.current.submissions}
  {storage : heap → CheckpointStorageObservation} {visible : heap → Nat → ByteArray}

local notation "oldState" => current.current.ready.state
local notation "newState" => position.current.ready.state

/-- The exclusive create, both barriers and ready setter publish the new
keeper at the literal return, while the prior keeper becomes a seal. -/
theorem NativeCreatedRotationContinuation.writeStorageEntry
    {report : NativeReadyCreatedRotation oldState}
    (rotation : NativeCreatedRotationContinuation current.current.ready next report)
    {seen : OpenRotationObservation.Created current report}
    (returned : seen.Reached report.lookup position)
    (atState : position.current = ⟨current.current.history, current.current.submissions, next⟩)
    (initial : NativeReadyStorage oldState (storage current.reached))
    (keeps : seen.LocalFrames (fun before after => (storage before).Frames (oldState).crashPath (storage after)))
    (child : (seen.view.files position.reached).image.ObservesWalChild report.parent.root
      (newState).session.directory (newState).writer.wal.active.first (storage position.reached) (visible position.reached)) :
    position.WriteStorageEntry seen.view (seen.writeCache position)
      (storage position.reached) (visible position.reached) := by
  have stateEq : newState = report.next current.current.ready.readPrefix.refines.1 :=
    (congrArg (fun state : NativeExecutionPosition => state.ready.state) atState).trans rotation.reached
  have atFiles : (seen.view.files position.reached).image = report.settled :=
    congrArg (fun files : OpenRotationFiles => files.2.2) returned.fileState
  have sameReady : newState = next.state := congrArg (fun state : NativeExecutionPosition => state.ready.state) atState
  have sameBytes : report.settled.inodes.visible (report.settled.view.modelObject report.created.child.child) =
      next.state.writer.wal.active.bytes := by
    have empty : next.state.writer.wal.active.bytes = ByteArray.empty :=
      congrArg WalSegment.bytes rotation.frame.keeper
    rw [empty, report.bytes, report.view, report.created.inode]
    exact report.created.empty
  have sameDirectory : (newState).session.directory = (oldState).session.directory := by rw [stateEq]; rfl
  rw [atFiles, sameReady] at child
  obtain ⟨keeper, settled, live⟩ :=
    child.published rotation.successor rotation.successorCrash rotation.successorBytes sameBytes
  rw [← sameReady] at keeper settled live
  have inodes := (report.custody current.current.ready.readPrefix.refines.1).2.1
  have framed := returned.frames (frame := fun before after => (storage before).Frames (oldState).crashPath (storage after))
    CheckpointStorageObservation.Frames.trans keeps
  apply returned.writeStorageEntryCreated rotation atState _ live
  refine initial.afterRotation current.current.ready.readPrefix.refines.1 ?_ sameDirectory ?_ ?_ framed keeper settled
  · rw [stateEq]; rfl
  · rw [stateEq]; exact congrFun inodes _
  · rw [stateEq]; exact congrFun inodes _

/-- Reusing the checked empty successor yields the same ready storage
on the reached raw heap. Its measured empty bytes also remain visible. -/
theorem NativeExistingRotationContinuation.writeStorageEntry
    {report : NativeReadyExistingRotation oldState}
    (rotation : NativeExistingRotationContinuation current.current.ready next report)
    {seen : OpenRotationObservation.Existing current report}
    (returned : seen.Reached report.opened.lookup position)
    (atState : position.current = ⟨current.current.history, current.current.submissions, next⟩)
    (initial : NativeReadyStorage oldState (storage current.reached))
    (keeps : seen.LocalFrames (fun before after => (storage before).Frames (oldState).crashPath (storage after)))
    (child : (seen.view.files position.reached).image.ObservesWalChild report.opened.root
      (newState).session.directory (newState).writer.wal.active.first (storage position.reached) (visible position.reached)) :
    position.WriteStorageEntry seen.view (seen.writeCache position)
      (storage position.reached) (visible position.reached) := by
  have stateEq : newState = report.next current.current.ready.readPrefix.refines.1 :=
    (congrArg (fun state : NativeExecutionPosition => state.ready.state) atState).trans rotation.reached
  have atFiles : (seen.view.files position.reached).image = report.directory.settled :=
    congrArg (fun files : OpenRotationFiles => files.2.2) returned.fileState
  have sameReady : newState = next.state := congrArg (fun state : NativeExecutionPosition => state.ready.state) atState
  have sameBytes : report.directory.settled.inodes.visible
      (report.directory.settled.view.modelObject report.opened.statChild.child) = next.state.writer.wal.active.bytes := by
    have empty : next.state.writer.wal.active.bytes = ByteArray.empty :=
      congrArg WalSegment.bytes rotation.frame.keeper
    rw [empty, report.directory.bytes, report.directory.view, report.opened.custody.2.1]
    change (if report.file.effective then _ else report.opened.files.inodes).visible _ = _
    cases effective : report.file.effective <;>
      simpa [effective, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync] using report.opened.custody.2.2.2.2
  have sameDirectory : (newState).session.directory = (oldState).session.directory := by rw [stateEq]; rfl
  rw [atFiles, sameReady] at child
  obtain ⟨keeper, settled, live⟩ :=
    child.published rotation.successor rotation.successorCrash rotation.successorBytes sameBytes
  rw [← sameReady] at keeper settled live
  have inodes := (report.custody current.current.ready.readPrefix.refines.1).2.1
  have framed := returned.frames (frame := fun before after => (storage before).Frames (oldState).crashPath (storage after))
    CheckpointStorageObservation.Frames.trans keeps
  apply returned.writeStorageEntryExisting rotation atState _ live
  refine initial.afterRotation current.current.ready.readPrefix.refines.1 ?_ sameDirectory ?_ ?_ framed keeper settled
  · rw [stateEq]; rfl
  · rw [stateEq]; exact congrFun inodes _
  · rw [stateEq]; exact congrFun inodes _

end Reached

end Alvoki.Storage.DiskSession
