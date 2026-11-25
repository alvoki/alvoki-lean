import Alvoki.Storage.Disk.NativeGroupedWriteSyncError
import Alvoki.Storage.Disk.NativeExecutionPendingWrite

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentCommit WalSegmentRepair WAL.Boundary

namespace NativeGroupedWriteSyncError

variable {before : NativeReadyState} {prepared : NativeReadyWritePreparation before}

/-- The reached namespace is the one observed after the staged open and
write. Neither file sync nor temporary close replaces the managed names. -/
def pendingCensus (seen : NativeGroupedWriteSyncError prepared) (valid : before.Valid) :
    NativePendingWriteCensus before seen.staging.appendCache := by
  let directory := before.session.directory
  let view := seen.staging.stageView
  let root := seen.staging.root
  let bindings := fun path =>
    if path = directory.path then some (view.modelObject root)
    else if path = directory.file .lock then (view.child root "LOCK").map view.modelObject else none
  obtain ⟨retained, inodes, _, _, _⟩ := seen.staging.selectsKeeper.custody
  have sameInodes : seen.census.inode = before.census.inode := inodes
  have sameDirectory : view.modelObject root = seen.census.inode before.directorySlot.description := by
    rw [sameInodes, seen.staging.stageObjects]
    exact seen.staging.directoryIdentity
  refine ⟨seen.census, seen.keepsSlot (retained _ valid.ownerLive), seen.keepsSlot (retained _ valid.directoryLive),
    congrFun sameInodes _, seen.staging.directoryCapture, seen.staging.directoryCached,
    seen.staging.sameDirectoryInode.trans (congrFun sameInodes _).symm, congrFun sameInodes _,
    bindings, ?_, ?_⟩
  · change bindings (directory.file .lock) = some (seen.census.inode before.owner.description)
    simp only [bindings, file_ne_directory directory .lock, ite_false, ite_true, view, root,
      seen.staging.stageBindings.2.1, Option.map_some, sameInodes, seen.staging.stageObjects, seen.staging.lockIdentity]
  · change bindings directory.path = some (seen.census.inode before.directorySlot.description)
    simp only [bindings, ite_true, sameDirectory]

/-- The disk image used by the shared retry proof, with the exact WAL
files reached by the group and the pre-write immutable sealed bytes. -/
def recoveryFiles (seen : NativeGroupedWriteSyncError prepared) : FileImage :=
  before.writer.wal.appendReopenFiles
    (seen.markerFiles.reopenSegment before.writer.wal.active.first before.writer.history
      before.writer.wal.directory.active.manifest) before.files.image.keeper.staged

theorem recoveryBindings (seen : NativeGroupedWriteSyncError prepared) (valid : before.Valid) :
    seen.recoveryFiles.directory.active = before.writer.target.pair ∧
    seen.recoveryFiles.directory.crashImages = [before.writer.target.pair] ∧
    seen.recoveryFiles.kept = before.files.image.kept := by
  obtain ⟨marker, crashMarkers⟩ := seen.markerFrame
  have beforeMarker := (valid.retained.selectPriorKeeper ByteArray.empty).1
  have pair : (⟨before.writer.wal.directory.active.manifest, prepared.initial.marker.active⟩ :
      DirectoryPublication.Bindings) = before.writer.target.pair := by
    rw [valid.retained.walPair]
    change (⟨before.writer.target.pair.manifest,
      some (WAL.Boundary.encode (WAL.encode before.writer.history).size.toUInt64)⟩ :
        DirectoryPublication.Bindings) = before.writer.target.pair
    rw [← beforeMarker]
  refine ⟨?_, ?_, valid.retained.sealedFiles.symm⟩
  · change (⟨before.writer.wal.directory.active.manifest, seen.markerFiles.marker.active⟩ :
      DirectoryPublication.Bindings) = _
    rw [marker, pair]
  · change seen.markerFiles.marker.crashImages.map (DirectoryPublication.Bindings.mk before.writer.wal.directory.active.manifest) = _
    rw [crashMarkers]
    exact congrArg (fun binding => [binding]) pair

end NativeGroupedWriteSyncError

/-- A returned error from either actual group member reaches the common
poisoned write endpoint. The callback reports are the file projection
of the same native call. The returned cache and descriptor inventory
are the ones after the observed stage handle's finalizer. -/
theorem NativeReadPosition.stopsAtGroupedSyncError (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} (seen : NativeGroupedWriteSyncError prepared)
    (rename : FilePath → FilePath → EStateM IO.Error (CensusDirectoryCache × WriteFiles) Unit) :
    ∃ pending : NativePendingWrite current,
      pending.write.request = seen.request ∧ pending.write.failure.batch = prepared.batch ∧
      pending.write.failure.cause = seen.diagnostic ∧ pending.poisoned.phase = .poisoned ∧
      pending.poisoned.files = ⟨(seen.staging.appendCache, seen.markerFiles), current.state.files.owners⟩ ∧
      pending.files.image = seen.recoveryFiles ∧
      pending.poisoned.descriptors = seen.census ∧
      pending.observed.bindings = (seen.pendingCensus current.readPrefix.refines.1).bindings ∧
      pending.submissions = log ++ [.uncertainBatch prepared.batch] := by
  let valid := current.readPrefix.refines.1
  let logical := seen.logical valid rename
  obtain ⟨failure, observed, calls, rows, batch, synced⟩ := logical.observedFailure
  have sameBatch : failure.batch = prepared.batch := batch
  have cache : observed.cache = current.state.cache := (congrArg WriteRequest.Calls.cache calls).symm
  let write : NativeReadyWriteFailure current.state := ⟨seen.request, failure, observed, seen.rows.trans rows.symm, cache⟩
  have projected := seen.projectedGroup valid rename
  have exactSync : .error failure.cause (logical.group.cache.consume prepared.stagedPath, failure.failed) =
      EStateM.Result.error seen.diagnostic (seen.staging.appendCache, seen.markerFiles) := synced.symm.trans projected
  obtain ⟨cause, next⟩ := EStateM.Result.error.inj exactSync
  obtain ⟨nextCache, failed⟩ := Prod.mk.inj next
  have actual := logical.returnsError seen.request seen.rows valid.retained synced
  have sameCalls : { WriteRequest.Calls.ofFailure observed with cache := current.state.cache } = logical.calls := by
    rw [← calls]
    rfl
  have returned : write.returnedAt seen.staging.appendCache := by
    change { WriteRequest.Calls.ofFailure observed with cache := current.state.cache }.run _ _ _ = _
    rw [sameCalls, actual, nextCache]
  let pending : NativePendingWrite current := ⟨write, seen.staging.appendCache, returned, seen.pendingCensus valid⟩
  refine ⟨pending, rfl, sameBatch, cause, rfl, ?_, ?_, rfl, rfl, ?_⟩
  · change (⟨(seen.staging.appendCache, failure.failed), current.state.files.owners⟩ : LockedFileState _) = _
    rw [failed]
  · change failure.released.image = _
    simp only [SegmentedBatchFailure.released, NativeGroupedWriteSyncError.recoveryFiles, NativeReadyState.files, failed]
  · simp only [NativePendingWrite.submissions, pending, write, sameBatch]

end Alvoki.Storage.DiskSession
