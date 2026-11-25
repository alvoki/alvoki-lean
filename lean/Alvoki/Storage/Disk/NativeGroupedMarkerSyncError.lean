import Alvoki.Storage.Disk.NativeGroupedWriteSyncError

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentCommit WalSegmentRepair WAL.Boundary

private abbrev GroupFiles := DescriptorInventory × WriteFiles

/-- The keeper sync returned successfully before the same staged marker
handle reported an error. The physical report specifies whether that
stage sync took effect before returning the error. -/
structure NativeGroupedMarkerSyncError {before : NativeReadyState} (prepared : NativeReadyWritePreparation before) where
  request : WriteRequest
  rows : request.rows = prepared.rows
  staging : NativeReadyWriteStaging prepared
  openRead : FilePath → EStateM IO.Error WriteFiles CheckpointOpenHandle
  fsync : CheckpointOpenHandle → EStateM IO.Error WriteFiles Unit
  keeperReturned : fsync staging.keeperHandle prepared.staged = .ok () prepared.keeperSynced
  cause : IO.Error
  effective : Bool
  markerReturned : fsync staging.stageHandle prepared.keeperSynced =
    .error cause (if effective then prepared.bothSynced else prepared.keeperSynced)
  finalize : CheckpointOpenHandle → EStateM IO.Error GroupFiles Unit
  finalized :
    let files := reachedState (fsync staging.stageHandle prepared.keeperSynced)
    reachedState (finalize staging.stageHandle (staging.afterMarkerOpen, files)) =
      (staging.afterMarkerOpen.afterDrops [staging.markerSlot.closeEvent], files)

namespace NativeGroupedMarkerSyncError

variable {before : NativeReadyState} {prepared : NativeReadyWritePreparation before}

def toGrouped (seen : NativeGroupedMarkerSyncError prepared) : NativeGroupedWriteSyncError prepared where
  request := seen.request
  rows := seen.rows
  staging := seen.staging
  openRead := seen.openRead
  fsync := seen.fsync
  effect := .complete
  effective := true
  keeperReturned := seen.keeperReturned ▸ FsyncResult.completed
  complete := fun _ _ => rfl
  markerEffective := seen.effective
  markerReturned := by
    simp only [seen.keeperReturned, reachedState, seen.markerReturned]
    have synced : (prepared.keeperSynced.stepMarker prepared.marker .syncStaged).getD prepared.keeperSynced =
        prepared.bothSynced := rfl
    rw [synced]
    cases seen.effective <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> constructor
  finalize := seen.finalize
  finalized := by simpa only [seen.keeperReturned, reachedState] using seen.finalized
  failure := .marker seen.cause prepared.keeperSynced _ seen.keeperReturned (by
    simpa only [seen.keeperReturned, reachedState] using seen.markerReturned)

theorem diagnostic (seen : NativeGroupedMarkerSyncError prepared) :
    seen.toGrouped.diagnostic = IO.userError s!"sync failed for '{prepared.stagedPath}': {seen.cause}" := rfl

theorem finalFiles (seen : NativeGroupedMarkerSyncError prepared) :
    seen.toGrouped.keeperFiles = prepared.keeperSynced ∧
    seen.toGrouped.markerFiles = if seen.effective then prepared.bothSynced else prepared.keeperSynced := by
  constructor
  · simp only [NativeGroupedWriteSyncError.keeperFiles, toGrouped, seen.keeperReturned, reachedState]
  · simp only [NativeGroupedWriteSyncError.markerFiles, NativeGroupedWriteSyncError.keeperFiles, toGrouped,
      seen.keeperReturned, seen.markerReturned, reachedState]

def files (seen : NativeGroupedMarkerSyncError prepared) : FileImage :=
  resumedAppendFiles before.files.image before.writer.history before.writer.wal.active.first seen.toGrouped.markerFiles

/-- The keeper contains the full synced append. Since the failed stage
sync cannot reach rename, that keeper still replays the old checkpoint
and marked prefix for every modeled crash choice. -/
theorem fileSelection (seen : NativeGroupedMarkerSyncError prepared) (valid : before.Valid) :
    seen.files.directory.active = before.writer.target.pair ∧
    seen.files.directory.crashImages = [before.writer.target.pair] ∧
    seen.files.directory.staged .walBoundary = some (prepared.marker, seen.effective) ∧
    seen.files.keeper.active = some (before.writer.wal.active.bytes ++ WAL.encode prepared.batch) ∧
    seen.files.keeper.crashImages = [seen.files.keeper.active] ∧
    SelectedIntegrityCheckpoint before.writer.published.durable seen.files.directory.active.manifest
      before.writer.checkpoint ∧
    selectRetained before.writer.installed.activeFirst (WAL.encode before.writer.history).size.toUInt64
      (before.writer.wal.active.bytes ++ WAL.encode prepared.batch) = .ok before.writer.wal.active.bytes := by
  let ready := valid.retained
  have old : before.files.image.directory.active = before.writer.target.pair := ready.resumed.ready.selected
  obtain ⟨marker, selected⟩ := ready.selectPriorKeeper (WAL.encode prepared.batch)
  have pair : (⟨before.files.image.directory.active.manifest,
      some (WAL.Boundary.encode (WAL.encode before.writer.history).size.toUInt64)⟩ :
      DirectoryPublication.Bindings) = before.writer.target.pair := by
    rw [old, ← marker]
  have bytes := congrArg (fun bytes => some (bytes ++ WAL.encode prepared.batch)) ready.layout.activeBytes.symm
  rw [← ready.layout.activeBytes] at selected
  have checkpoint := pair.symm ▸ ready.resumed.selected
  unfold files
  rw [seen.finalFiles.2]
  cases effect : seen.effective <;> exact ⟨pair, congrArg (fun pair => [pair]) pair, rfl, bytes, rfl, checkpoint, selected⟩

end NativeGroupedMarkerSyncError

/-- Both write interfaces stop before marker rename after the staged
marker error. The exact poisoned return still selects the old history
because the live marker was never replaced. -/
theorem NativeReadPosition.returnsGroupedMarkerError (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} (seen : NativeGroupedMarkerSyncError prepared) :
    NativeReturnedGroupedWriteSyncError current seen.toGrouped :=
  current.returnsGroupedWriteSyncError seen.toGrouped

end Alvoki.Storage.DiskSession
