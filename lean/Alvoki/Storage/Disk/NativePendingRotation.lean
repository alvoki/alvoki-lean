import Alvoki.Storage.Disk.NativeReadyRotation
import Alvoki.Storage.Disk.RotationDirectoryFsyncStop

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL (frameSize)

/-- The final directory fsync is issued by the reached ready writer
after exclusive creation and file sync. Its temporary successor
description is released before the directory callback. The active
append cache remains owned until a later successful final barrier. -/
structure NativeRotationDirectoryFailure (state : NativeReadyState) (diagnostic : Option IO.Error) where
  lookup : FilePath → Except IO.Error IO.FS.Metadata
  parent : RotationCreateParent state.session.directory state.writer lookup state.census
  owner : parent.owner = state.owner
  created : RotationRawSuccessor parent
  reported : RotationDirectoryFsyncFailure created diagnostic
  cache : reported.cache = state.cache
  pending : state.cache.consume (rotationSuccessorPath state.session.directory state.writer) = state.cache
  afterFile : List LockReferenceDrop
  temporaryClose : reported.beforeDirectory = afterFile ++ [created.raw.closeEvent]
  appendCustody : ∀ entry ∈ state.cache.active,
    entry.1 = state.session.directory.file (.walSegment state.writer.installed.activeFirst) ∧
    entry.2.2.1 ∈ reported.effectInventory.slots ∧
    entry.2.1.inode entry.2.2.1.description = reported.effectInventory.inode entry.2.2.1.description ∧
    reported.after.view.modelObject parent.keeper.child = reported.effectInventory.inode entry.2.2.1.description

abbrev NativeRotationDirectoryStop (state : NativeReadyState) := NativeRotationDirectoryFailure state none

namespace NativeRotationDirectoryFailure

variable {state : NativeReadyState} {diagnostic : Option IO.Error}

def session (_stop : NativeRotationDirectoryFailure state diagnostic) : SegmentedSession :=
  { state.session with phase := .poisoned }

theorem cachePreserved (stop : NativeRotationDirectoryFailure state diagnostic) :
    stop.reported.toRotationSuccessorFileIssue.atIssue = state.cache := by
  let path := rotationSuccessorPath state.session.directory state.writer
  change (stop.reported.cache.remember path stop.created.handle).consume path = state.cache
  have consumed : (state.cache.remember path stop.created.handle).consume path = state.cache.consume path := by
    simp [Cache.remember, pushPending, Cache.consume]
  rw [stop.cache, consumed]
  exact stop.pending

theorem temporaryReleased (stop : NativeRotationDirectoryFailure state diagnostic) :
    stop.reported.effectInventory =
      state.census.afterDrops (stop.reported.drops ++ stop.afterFile ++ [stop.created.raw.closeEvent]) ∧
    stop.reported.effectInventory.references stop.created.raw.description = [] := by
  have closed :
      stop.reported.effectInventory =
        state.census.afterDrops (stop.reported.drops ++ stop.afterFile ++ [stop.created.raw.closeEvent]) := by
    change ((state.census.insert stop.created.raw stop.created.free).afterDrops stop.reported.drops).afterDrops
      stop.reported.beforeDirectory = _
    rw [stop.temporaryClose, DescriptorInventory.afterDrops_append, ← List.append_assoc]
    exact DescriptorInventory.insert_thenClose _ _ _ _
  refine ⟨closed, ?_⟩
  rw [closed, DescriptorInventory.references_afterDrops, stop.created.fresh]
  rfl

/-- The stop holds the original writer and cached directory on their
original objects. The absent successor is now visible at the exact
canonical path on the newly created and already synced inode. -/
theorem custody (stop : NativeRotationDirectoryFailure state diagnostic) (valid : state.Valid) :
    stop.reported.directoryHandle.2.1 = state.directorySlot ∧
    state.directorySlot ∈ stop.reported.effectInventory.slots ∧
    stop.reported.pathObject state.session.directory.path = some stop.parent.root ∧
    stop.reported.after.view.modelObject stop.parent.root =
      stop.reported.effectInventory.inode state.directorySlot.description ∧
    state.owner ∈ stop.reported.effectInventory.slots ∧
    stop.reported.effectInventory.inode = state.census.inode ∧
    stop.reported.after.view.child stop.parent.root "LOCK" = some stop.parent.lock.child ∧
    stop.reported.after.view.modelObject stop.parent.lock.child =
      stop.reported.effectInventory.inode state.owner.description ∧
    stop.reported.after.view.child stop.parent.root (renderWalSegmentName (state.writer.installed.walBytes / frameSize)) =
      some stop.created.child.child ∧
    stop.reported.after.view.modelObject stop.created.child.child =
      stop.reported.effectInventory.inode stop.created.raw.description ∧
    stop.reported.after.inodes.crashBytes (stop.reported.effectInventory.inode stop.created.raw.description) =
      [ByteArray.empty] := by
  obtain ⟨captured, known⟩ := valid.captured
  have same : stop.reported.directoryHandle = (captured, state.directorySlot, 0) :=
    Option.some.inj (stop.reported.captured.symm.trans ((congrArg Cache.directory stop.cache).trans known))
  obtain ⟨_, lock, lockObject, _⟩ := (RotationRawCreateEffect.afterOpen stop.created).keepsLock
  have successor := stop.created.child.binds
  rw [stop.created.child.atRoot, stop.created.child.atName] at successor
  have sameSlot : stop.reported.directoryHandle.2.1 = state.directorySlot :=
    congrArg (fun handle : RotationSuccessorHandle => handle.2.1) same
  refine ⟨sameSlot, sameSlot ▸ stop.reported.directoryLive, stop.reported.bound, ?_,
    stop.owner ▸ stop.reported.ownerStillLive, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact (congrArg (fun view => view.modelObject stop.parent.root) stop.reported.view).trans
      ((congrFun stop.created.objects _).trans (sameSlot ▸ stop.reported.effectObject))
  · exact (congrArg (fun view => view.child stop.parent.root "LOCK") stop.reported.view).trans lock
  · exact (congrArg (fun view => view.modelObject stop.parent.lock.child) stop.reported.view).trans
      (lockObject.trans (congrArg (fun slot : DescriptorSlot => state.census.inode slot.description) stop.owner))
  · exact (congrArg (fun view => view.child stop.parent.root
      (renderWalSegmentName (state.writer.installed.walBytes / frameSize))) stop.reported.view).trans successor
  · exact (congrArg (fun view => view.modelObject stop.created.child.child) stop.reported.view).trans stop.created.inode
  · rw [stop.reported.bytes]
    exact stop.created.syncedBytes

theorem keepsKeeperMarker (stop : NativeRotationDirectoryFailure state diagnostic) :
    NativeRotationKeeperMarker state.writer stop.parent.root stop.reported.after
      stop.parent.keeper.child stop.parent.marker.child := by
  obtain ⟨keeper, marker, keeperCrash, markerCrash, keeperBytes, markerBytes⟩ := stop.reported.keepsKeeperMarker
  exact ⟨keeper, marker, keeperCrash, markerCrash, keeperBytes, markerBytes⟩

theorem rejectsReads (stop : NativeRotationDirectoryFailure state diagnostic) (sequence : UInt64)
    (sameSession : Bool) (read : PackedTable → Option α) :
    stop.session.sessionRef = state.session.sessionRef ∧
    stop.session.phaseRef = state.session.phaseRef ∧
    stop.session.runAcquireAt sequence = .error (IO.userError "publication failed; reopen the database") stop.session ∧
    stop.session.runSnapshotRead sameSession read =
      .error (IO.userError "publication failed; reopen the database") stop.session :=
  ⟨rfl, rfl, rfl, SegmentedSession.runSnapshotRead_poisoned rfl sameSession read⟩

end NativeRotationDirectoryFailure

/-- Both final barrier failure channels preserve the same reached
authority, physical files and previously acknowledged client responses. -/
structure NativeRotationFailureState (current : NativeReadPosition history log)
    (failure : NativeRotationDirectoryFailure current.state diagnostic) : Prop where
  readyBefore : current.state.session.phase = .ready current.state.writer.installed
  directorySlot : failure.reported.directoryHandle.2.1 = current.state.directorySlot
  directoryLive : current.state.directorySlot ∈ failure.reported.effectInventory.slots
  directoryBound : failure.reported.pathObject current.state.session.directory.path = some failure.parent.root
  directoryObject : failure.reported.after.view.modelObject failure.parent.root =
    failure.reported.effectInventory.inode current.state.directorySlot.description
  ownerLive : current.state.owner ∈ failure.reported.effectInventory.slots
  ownerHeld : current.state.writer.owners.Owns current.state.session.directory current.state.session.descriptor
  sameInodes : failure.reported.effectInventory.inode = current.state.census.inode
  lockName : failure.reported.after.view.child failure.parent.root "LOCK" = some failure.parent.lock.child
  lockObject : failure.reported.after.view.modelObject failure.parent.lock.child =
    failure.reported.effectInventory.inode current.state.owner.description
  successorName : failure.reported.after.view.child failure.parent.root
    (renderWalSegmentName (current.state.writer.installed.walBytes / frameSize)) = some failure.created.child.child
  successorObject : failure.reported.after.view.modelObject failure.created.child.child =
    failure.reported.effectInventory.inode failure.created.raw.description
  successorBytes : failure.reported.after.inodes.crashBytes (failure.reported.effectInventory.inode failure.created.raw.description) =
    [ByteArray.empty]
  temporaryReleased : failure.reported.effectInventory.references failure.created.raw.description = []
  appendRetained : ∀ entry ∈ current.state.cache.active,
    entry.1 = current.state.session.directory.file (.walSegment current.state.writer.installed.activeFirst) ∧
    entry.2.2.1 ∈ failure.reported.effectInventory.slots ∧
    entry.2.1.inode entry.2.2.1.description = failure.reported.effectInventory.inode entry.2.2.1.description ∧
    failure.reported.after.view.modelObject failure.parent.keeper.child = failure.reported.effectInventory.inode entry.2.2.1.description
  kept : NativeRotationKeeperMarker current.state.writer failure.parent.root failure.reported.after
    failure.parent.keeper.child failure.parent.marker.child
  reads : PendingClientReplay log current.reads history
  bounded : ∀ read ∈ current.reads, read.BoundedBy history.length

private theorem NativeReadPosition.rotationFailureState (current : NativeReadPosition history log)
    (failure : NativeRotationDirectoryFailure current.state diagnostic) : NativeRotationFailureState current failure := by
  obtain ⟨valid, _, replay⟩ := current.readPrefix.refines
  obtain ⟨directory, directoryLive, directoryBound, directoryObject, ownerLive, inodes, lock, lockObject, successor,
    successorObject, bytes⟩ := failure.custody valid
  exact ⟨valid.phase, directory, directoryLive, directoryBound, directoryObject, ownerLive, valid.retained.held,
    inodes, lock, lockObject, successor, successorObject, bytes, failure.temporaryReleased.2, failure.appendCustody,
    failure.keepsKeeperMarker, replay, current.readPrefix.readsBounded⟩

structure NativePendingRotation (current : NativeReadPosition history log)
    (stop : NativeRotationDirectoryStop current.state) extends NativeRotationFailureState current stop where
  stopped : stop.reported.run = .error current.state.session.directory.path
    (stop.session.phase, ⟨(current.state.cache, stop.reported.cut.image), current.state.writer.owners⟩)

/-- The actual stop happens after file sync and before old append
retirement. The case needs no response or ensuing open. -/
theorem NativeReadPosition.stopsDuringRotation (current : NativeReadPosition history log)
    (stop : NativeRotationDirectoryStop current.state) : NativePendingRotation current stop := by
  have stopped := stop.reported.stopsSchedule
  rw [stop.cachePreserved] at stopped
  exact ⟨current.rotationFailureState stop, stopped⟩

structure NativeReturnedRotationError (current : NativeReadPosition history log) (cause : IO.Error)
    (failure : NativeRotationDirectoryFailure current.state (some cause)) extends NativeRotationFailureState current failure where
  returned : failure.reported.run =
    .ok (.error (IO.userError s!"sync failed for '{current.state.session.directory.path}': {cause}"))
      (failure.session.phase, ⟨(current.state.cache, failure.reported.cut.image), current.state.writer.owners⟩)

/-- The grouped directory fsync returns its original path-specific
diagnostic and exact poisoned state before the old append cache reset. -/
theorem NativeReadPosition.rotationReturnsError (current : NativeReadPosition history log) (cause : IO.Error)
    (failure : NativeRotationDirectoryFailure current.state (some cause)) : NativeReturnedRotationError current cause failure := by
  have returned := failure.reported.returnsError
  rw [failure.cachePreserved] at returned
  exact ⟨current.rotationFailureState failure, returned⟩

/-- The same failure's physical successor name and selected bytes determine
the bounded retry. Every allowed survivor retains the earlier ledger.
An effective barrier allows only the new empty successor. -/
theorem NativeRotationFailureState.selectsReportedSurvivor {current : NativeReadPosition history log}
    {stop : NativeRotationDirectoryFailure current.state diagnostic} (pending : NativeRotationFailureState current stop)
    {name : Option DeviceInode}
    (survived : name ∈ stop.reported.after.crashNames
      (renderWalSegmentName (current.state.writer.installed.walBytes / frameSize)))
    {payload : ByteArray}
    (bytes : payload ∈ stop.reported.after.inodes.crashBytes (stop.reported.after.view.modelObject
      (name.getD stop.parent.keeper.child)))
    {retry : LockedFileState FileImage}
    (reported : ReportedReopenPrefix current.state.session.directory
      (stop.reported.cut.survivingWal current.state.writer.wal.directory.active name.isSome).active.first
      (stop.reported.cut.crashedFiles current.state.writer.wal.directory.active name.isSome) retry) :
    let keeper := (stop.reported.cut.survivingWal current.state.writer.wal.directory.active name.isSome).active
    BoundedReopenTrace current.state.session.directory
      (CheckpointRetryTarget current.state.writer.history keeper.first)
      (stop.reported.cut.crashedFiles current.state.writer.wal.directory.active name.isSome) retry ∧
    retry.image.directory.active = current.state.writer.target.pair ∧
    (stop.reported.effective = true → name = some stop.created.child.child ∧ payload = ByteArray.empty) ∧
    (∃ layout : CanonicalKeeperLayout retry.image current.state.writer.history,
      layout.keeper = keeper ∧ layout.keeper.bytes = payload ∧ Prepared retry.image layout.target layout.plan) ∧
    PendingClientReplay log current.reads history ∧ ∀ read ∈ current.reads, read.BoundedBy history.length := by
  let valid := current.readPrefix.refines.1
  have ready : current.state.writer.RetainedReady current.state.session.directory stop.parent.owner.description :=
    (congrArg DescriptorSlot.description stop.owner).symm ▸ valid.owner.symm ▸ valid.retained
  obtain ⟨trace, pair, selected, prepared⟩ := stop.reported.preparesReopenPrefix ready survived bytes reported
  exact ⟨trace, pair, selected, prepared, pending.reads, pending.bounded⟩

end Alvoki.Storage.DiskSession
