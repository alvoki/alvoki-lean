import Alvoki.Storage.Disk.Proofs.Rotation.NativeOpenRotation
import Alvoki.Storage.Disk.NativeReadyWriteStorage

namespace Alvoki.Storage.DiskSession

open SyncHandleRouting

variable {heap : Type} {opened : NativeOpenedHandle heap}
  {current position : NativeOpenedPosition opened}

/-- A rotation keeps the cache references of the original opened table. -/
abbrev OpenRotationObservation.writeCache {read create sync entry settled reset}
    (seen : OpenRotationObservation current read create sync entry settled reset)
    (position : NativeOpenedPosition opened) :
    OpenSyncCacheRefs opened.files position.current.ready.state.session.directory.path :=
  ⟨seen.directory, seen.active, seen.pending, seen.references,
    (congrArg DiskDirectory.path position.directory).symm ▸ seen.cachePath⟩

private theorem OpenRotationObservation.Reached.writeStorageEntry {read create sync entry settled reset}
    {seen : OpenRotationObservation current read create sync entry settled reset} {lookup}
    (reached : seen.Reached lookup position)
    (cache : reset.1 = position.current.ready.state.cache)
    (census : reset.2.1 = position.current.ready.state.census)
    {handle : RotationSuccessorHandle}
    (captured : reset.1.directory = some handle)
    (rootInode : handle.1.inode handle.2.1.description =
      position.current.ready.state.census.inode position.current.ready.state.directorySlot.description)
    {storage : CheckpointStorageObservation} {visible : Nat → ByteArray}
    (physical : NativeReadyStorage position.current.ready.state storage)
    (keeper : ∀ inode, storage.files.names (position.current.ready.state.session.directory.file
      (.walSegment position.current.ready.state.writer.wal.active.first)) = some inode →
      visible inode = position.current.ready.state.writer.wal.active.bytes) :
    position.WriteStorageEntry seen.view (seen.writeCache position) storage visible := by
  have reachedCache := congrArg Prod.fst reached.fileState
  have reachedCensus := congrArg (fun files : OpenRotationFiles => files.2.1) reached.fileState
  refine ⟨reachedCensus.trans census, reachedCache.trans cache, physical, keeper, ?_⟩
  intro literal loaded
  have attached := (congrArg Cache.directory reachedCache).trans captured
  change (seen.view.directory position.reached seen.directory).map (seen.view.handle position.reached) =
    some handle at attached
  change seen.view.directory position.reached seen.directory = some literal at loaded
  rw [loaded, Option.map_some] at attached
  rw [Option.some.inj attached]
  exact physical.directoryBound.trans (congrArg some rootInode.symm)

/-- The exclusive-created successor returns the original cached root.
Its capture and live census identify the same inode after the reset. -/
theorem OpenRotationObservation.Reached.writeStorageEntryCreated
    {report : NativeReadyCreatedRotation current.current.ready.state}
    {seen : OpenRotationObservation.Created current report}
    (reached : seen.Reached report.lookup position)
    {next : NativeReadPosition current.current.history current.current.submissions}
    (rotation : NativeCreatedRotationContinuation current.current.ready next report)
    (positionEq : position.current = ⟨current.current.history, current.current.submissions, next⟩)
    {storage : CheckpointStorageObservation} {visible : Nat → ByteArray}
    (physical : NativeReadyStorage position.current.ready.state storage)
    (keeper : ∀ inode, storage.files.names (position.current.ready.state.session.directory.file
      (.walSegment position.current.ready.state.writer.wal.active.first)) = some inode →
      visible inode = position.current.ready.state.writer.wal.active.bytes) :
    position.WriteStorageEntry seen.view (seen.writeCache position) storage visible := by
  have state := (congrArg (fun value : NativeExecutionPosition => value.ready.state) positionEq).trans rotation.reached
  obtain ⟨slot, inodes, _⟩ := report.custody current.current.ready.readPrefix.refines.1
  refine reached.writeStorageEntry (congrArg NativeReadyState.cache state).symm
    (congrArg NativeReadyState.census state).symm report.cached ?_ physical keeper
  rw [state, inodes]
  exact report.capturedObject.symm.trans
    (report.currentObject.trans (congrArg (fun value : DescriptorSlot =>
      current.current.ready.state.census.inode value.description) slot))

/-- When the successor already exists, its temporary read slot is closed.
The cached root has the same captured inode as at the directory barrier. -/
theorem OpenRotationObservation.Reached.writeStorageEntryExisting
    {report : NativeReadyExistingRotation current.current.ready.state}
    {seen : OpenRotationObservation.Existing current report}
    (reached : seen.Reached report.opened.lookup position)
    {next : NativeReadPosition current.current.history current.current.submissions}
    (rotation : NativeExistingRotationContinuation current.current.ready next report)
    (positionEq : position.current = ⟨current.current.history, current.current.submissions, next⟩)
    {storage : CheckpointStorageObservation} {visible : Nat → ByteArray}
    (physical : NativeReadyStorage position.current.ready.state storage)
    (keeper : ∀ inode, storage.files.names (position.current.ready.state.session.directory.file
      (.walSegment position.current.ready.state.writer.wal.active.first)) = some inode →
      visible inode = position.current.ready.state.writer.wal.active.bytes) :
    position.WriteStorageEntry seen.view (seen.writeCache position) storage visible := by
  have state := (congrArg (fun value : NativeExecutionPosition => value.ready.state) positionEq).trans rotation.reached
  obtain ⟨slot, inodes, _⟩ := report.custody current.current.ready.readPrefix.refines.1
  have fileInodes : report.file.after.1.inode = current.current.ready.state.census.inode := by
    rw [report.file.closesReadSlot.1, report.census]
    rfl
  have captured : current.current.ready.state.cache.directory = some report.directory.handle :=
    (congrArg Cache.directory report.cache).symm.trans report.directory.cached
  refine reached.writeStorageEntry (congrArg NativeReadyState.cache state).symm
    (congrArg NativeReadyState.census state).symm captured ?_ physical keeper
  rw [state, inodes]
  have issued := report.directory.currentObject
  rw [fileInodes] at issued
  exact report.directory.capturedObject.symm.trans (issued.trans
    (congrArg (fun value : DescriptorSlot => current.current.ready.state.census.inode value.description) slot))

end Alvoki.Storage.DiskSession
