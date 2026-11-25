import Alvoki.Storage.Disk.NativeReadyRotation
import Alvoki.Storage.Disk.RotationDirectoryFsyncStop

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL (frameSize)

/-- The final directory fsync is issued by the reached ready writer
after exclusive creation and file sync. Its temporary successor
description is released before the directory callback. The active
append cache remains owned until a later successful final barrier. -/
structure NativeRotationDirectoryStop (state : NativeReadyState) where
  lookup : FilePath → Except IO.Error IO.FS.Metadata
  parent : RotationCreateParent state.session.directory state.writer lookup state.census
  owner : parent.owner = state.owner
  created : RotationRawSuccessor parent
  reported : RotationDirectoryFsyncStop created
  cache : reported.cache = state.cache
  pending : state.cache.consume (rotationSuccessorPath state.session.directory state.writer) = state.cache
  afterFile : List LockReferenceDrop
  temporaryClose : reported.beforeDirectory = afterFile ++ [created.raw.closeEvent]
  appendCustody : ∀ entry ∈ state.cache.active,
    entry.1 = state.session.directory.file (.walSegment state.writer.installed.activeFirst) ∧
    entry.2.2.1 ∈ reported.effectInventory.slots ∧
    entry.2.1.inode entry.2.2.1.description = reported.effectInventory.inode entry.2.2.1.description ∧
    reported.after.view.modelObject parent.keeper.child = reported.effectInventory.inode entry.2.2.1.description

namespace NativeRotationDirectoryStop

variable {state : NativeReadyState}

def session (_stop : NativeRotationDirectoryStop state) : SegmentedSession :=
  { state.session with phase := .poisoned }

theorem cachePreserved (stop : NativeRotationDirectoryStop state) :
    stop.reported.toRotationSuccessorFileIssue.atIssue = state.cache := by
  let path := rotationSuccessorPath state.session.directory state.writer
  change (stop.reported.cache.remember path stop.created.handle).consume path = state.cache
  have consumed : (state.cache.remember path stop.created.handle).consume path = state.cache.consume path := by
    simp [Cache.remember, pushPending, Cache.consume]
  rw [stop.cache, consumed]
  exact stop.pending

theorem temporaryReleased (stop : NativeRotationDirectoryStop state) :
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
theorem custody (stop : NativeRotationDirectoryStop state) (valid : state.Valid) :
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

theorem keepsKeeperMarker (stop : NativeRotationDirectoryStop state) :
    NativeRotationKeeperMarker state.writer stop.parent.root stop.reported.after
      stop.parent.keeper.child stop.parent.marker.child := by
  obtain ⟨keeper, marker, keeperCrash, markerCrash, keeperBytes, markerBytes⟩ := stop.reported.keepsKeeperMarker
  exact ⟨keeper, marker, keeperCrash, markerCrash, keeperBytes, markerBytes⟩

theorem rejectsReads (stop : NativeRotationDirectoryStop state) (sequence : UInt64)
    (sameSession : Bool) (read : PackedTable → Option α) :
    stop.session.sessionRef = state.session.sessionRef ∧
    stop.session.phaseRef = state.session.phaseRef ∧
    stop.session.runAcquireAt sequence = .error (IO.userError "publication failed; reopen the database") stop.session ∧
    stop.session.runSnapshotRead sameSession read =
      .error (IO.userError "publication failed; reopen the database") stop.session :=
  ⟨rfl, rfl, rfl, SegmentedSession.runSnapshotRead_poisoned rfl sameSession read⟩

end NativeRotationDirectoryStop

/-- The pending execution retains the exact outer stop, reached session
and cache. Earlier responses still use the same acknowledged history. -/
structure NativePendingRotation (current : NativeReadPosition history log)
    (stop : NativeRotationDirectoryStop current.state) : Prop where
  readyBefore : current.state.session.phase = .ready current.state.writer.installed
  stopped : stop.reported.run = .error current.state.session.directory.path
    (stop.session.phase, ⟨(current.state.cache, stop.reported.cut.image), current.state.writer.owners⟩)
  directorySlot : stop.reported.directoryHandle.2.1 = current.state.directorySlot
  directoryLive : current.state.directorySlot ∈ stop.reported.effectInventory.slots
  directoryBound : stop.reported.pathObject current.state.session.directory.path = some stop.parent.root
  directoryObject : stop.reported.after.view.modelObject stop.parent.root =
    stop.reported.effectInventory.inode current.state.directorySlot.description
  ownerLive : current.state.owner ∈ stop.reported.effectInventory.slots
  ownerHeld : current.state.writer.owners.Owns current.state.session.directory current.state.session.descriptor
  sameInodes : stop.reported.effectInventory.inode = current.state.census.inode
  lockName : stop.reported.after.view.child stop.parent.root "LOCK" = some stop.parent.lock.child
  lockObject : stop.reported.after.view.modelObject stop.parent.lock.child =
    stop.reported.effectInventory.inode current.state.owner.description
  successorName : stop.reported.after.view.child stop.parent.root
    (renderWalSegmentName (current.state.writer.installed.walBytes / frameSize)) = some stop.created.child.child
  successorObject : stop.reported.after.view.modelObject stop.created.child.child =
    stop.reported.effectInventory.inode stop.created.raw.description
  successorBytes : stop.reported.after.inodes.crashBytes (stop.reported.effectInventory.inode stop.created.raw.description) =
    [ByteArray.empty]
  temporaryReleased : stop.reported.effectInventory.references stop.created.raw.description = []
  appendRetained : ∀ entry ∈ current.state.cache.active,
    entry.1 = current.state.session.directory.file (.walSegment current.state.writer.installed.activeFirst) ∧
    entry.2.2.1 ∈ stop.reported.effectInventory.slots ∧
    entry.2.1.inode entry.2.2.1.description = stop.reported.effectInventory.inode entry.2.2.1.description ∧
    stop.reported.after.view.modelObject stop.parent.keeper.child = stop.reported.effectInventory.inode entry.2.2.1.description
  kept : NativeRotationKeeperMarker current.state.writer stop.parent.root stop.reported.after
    stop.parent.keeper.child stop.parent.marker.child
  reads : PendingClientReplay log current.reads history
  bounded : ∀ read ∈ current.reads, read.BoundedBy history.length

/-- The actual stop happens after file sync and before old append
retirement. The case needs no response or ensuing open. -/
theorem NativeReadPosition.stopsDuringRotation (current : NativeReadPosition history log)
    (stop : NativeRotationDirectoryStop current.state) : NativePendingRotation current stop := by
  obtain ⟨valid, _, replay⟩ := current.readPrefix.refines
  obtain ⟨directory, directoryLive, directoryBound, directoryObject, ownerLive, inodes, lock, lockObject, successor, successorObject, bytes⟩ :=
    stop.custody valid
  have stopped := stop.reported.stopsSchedule
  rw [stop.cachePreserved] at stopped
  exact ⟨valid.phase, stopped, directory, directoryLive, directoryBound, directoryObject, ownerLive, valid.retained.held,
    inodes, lock, lockObject, successor, successorObject, bytes, stop.temporaryReleased.2, stop.appendCustody,
    stop.keepsKeeperMarker, replay,
    current.readPrefix.readsBounded⟩

/-- The same stop's physical successor name and selected bytes determine
the bounded retry. Every allowed survivor retains the earlier ledger.
An effective barrier allows only the new empty successor. -/
theorem NativePendingRotation.selectsReportedSurvivor {current : NativeReadPosition history log}
    {stop : NativeRotationDirectoryStop current.state} (pending : NativePendingRotation current stop)
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
  obtain ⟨_, trace, pair, selected, prepared⟩ := stop.reported.refinesReopenPrefix ready survived bytes reported
  exact ⟨trace, pair, selected, prepared, pending.reads, pending.bounded⟩

end Alvoki.Storage.DiskSession
