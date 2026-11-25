import Alvoki.Storage.Disk.NativeGroupedWriteSyncError

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentCommit WalSegmentRepair WAL.Boundary

private abbrev GroupFiles := DescriptorInventory × WriteFiles

private abbrev GroupState := CensusDirectoryCache × GroupFiles

/-- A returned first keeper-sync error still leaves the staged marker as
the next member of the group. The observed finalizer of its consumed
handle removes the reported slot and preserves the reached bytes. -/
structure NativeGroupedKeeperSyncError {before : NativeReadyState} (prepared : NativeReadyWritePreparation before) where
  request : WriteRequest
  rows : request.rows = prepared.rows
  staging : NativeReadyWriteStaging prepared
  openRead : FilePath → EStateM IO.Error WriteFiles CheckpointOpenHandle
  fsync : CheckpointOpenHandle → EStateM IO.Error WriteFiles Unit
  cause : IO.Error
  effect : WalSyncEffect
  effective : Bool
  keeperReturned : fsync staging.keeperHandle prepared.staged =
    .error cause (if effective then prepared.staged.syncWal effect else prepared.staged)
  markerEffective : Bool
  markerReturned : FsyncResult
    (reachedState (fsync staging.keeperHandle prepared.staged))
    (((reachedState (fsync staging.keeperHandle prepared.staged)).stepMarker prepared.marker .syncStaged).getD
      (reachedState (fsync staging.keeperHandle prepared.staged)))
    markerEffective (fsync staging.stageHandle (reachedState (fsync staging.keeperHandle prepared.staged)))
  finalize : CheckpointOpenHandle → EStateM IO.Error GroupFiles Unit
  finalized :
    let files := reachedState (fsync staging.stageHandle (reachedState (fsync staging.keeperHandle prepared.staged)))
    reachedState (finalize staging.stageHandle (staging.afterMarkerOpen, files)) =
      (staging.afterMarkerOpen.afterDrops [staging.markerSlot.closeEvent], files)

namespace NativeGroupedKeeperSyncError

variable {before : NativeReadyState} {prepared : NativeReadyWritePreparation before}

def toGrouped (seen : NativeGroupedKeeperSyncError prepared) : NativeGroupedWriteSyncError prepared where
  request := seen.request
  rows := seen.rows
  staging := seen.staging
  openRead := seen.openRead
  fsync := seen.fsync
  effect := seen.effect
  effective := seen.effective
  keeperReturned := by
    rw [seen.keeperReturned]
    cases seen.effective <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> constructor
  complete := by intro after succeeded; rw [seen.keeperReturned] at succeeded; contradiction
  markerEffective := seen.markerEffective
  markerReturned := seen.markerReturned
  finalize := seen.finalize
  finalized := seen.finalized
  failure := .keeper seen.cause _ seen.keeperReturned

abbrev keeperFiles (seen : NativeGroupedKeeperSyncError prepared) := seen.toGrouped.keeperFiles
abbrev markerFiles (seen : NativeGroupedKeeperSyncError prepared) := seen.toGrouped.markerFiles
abbrev census (seen : NativeGroupedKeeperSyncError prepared) := seen.toGrouped.census
abbrev diagnostic (seen : NativeGroupedKeeperSyncError prepared) := seen.toGrouped.diagnostic
abbrev syncPath (seen : NativeGroupedKeeperSyncError prepared) := seen.toGrouped.syncPath
noncomputable abbrev logical (seen : NativeGroupedKeeperSyncError prepared) := seen.toGrouped.logical
noncomputable abbrev run (seen : NativeGroupedKeeperSyncError prepared) := seen.toGrouped.run

theorem groupReturns (seen : NativeGroupedKeeperSyncError prepared) :
    SyncPathGroup.run seen.syncPath #[prepared.keeperPath, prepared.stagedPath]
      (seen.staging.groupCache, seen.staging.afterMarkerOpen, prepared.staged) =
      .error seen.diagnostic (seen.staging.appendCache, seen.census, seen.markerFiles) :=
  seen.toGrouped.groupReturns
theorem projectedGroup (seen : NativeGroupedKeeperSyncError prepared) (valid : before.Valid) (rename) :
    (seen.logical valid rename).calls.sync #[prepared.keeperPath, prepared.stagedPath]
      (seen.staging.groupCache, prepared.staged) =
    .error seen.diagnostic (seen.staging.appendCache, seen.markerFiles) :=
  seen.toGrouped.projectedGroup valid rename
theorem returnsUnknown (seen : NativeGroupedKeeperSyncError prepared) (valid : before.Valid) (rename) :
    seen.run rename = .error (.commitUnknown seen.diagnostic)
      (.poisoned, ⟨(seen.staging.appendCache, seen.census, seen.markerFiles), before.files.owners⟩) :=
  seen.toGrouped.returnsUnknown valid rename
theorem markerFrame (seen : NativeGroupedKeeperSyncError prepared) :
    seen.markerFiles.marker.active = prepared.initial.marker.active ∧
    seen.markerFiles.marker.crashImages = prepared.initial.marker.crashImages :=
  seen.toGrouped.markerFrame
theorem markerClosed (seen : NativeGroupedKeeperSyncError prepared) :
    seen.staging.markerSlot ∉ seen.census.slots :=
  seen.toGrouped.markerClosed
theorem keepsSlot (seen : NativeGroupedKeeperSyncError prepared) {slot : DescriptorSlot}
    (live : slot ∈ seen.staging.afterSelect.slots) : slot ∈ seen.census.slots :=
  seen.toGrouped.keepsSlot live

end NativeGroupedKeeperSyncError

abbrev NativeReturnedGroupedKeeperError (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} (seen : NativeGroupedKeeperSyncError prepared) :=
  NativeReturnedGroupedWriteSyncError current seen.toGrouped

theorem NativeReadPosition.returnsGroupedKeeperError (current : NativeReadPosition history log)
    {prepared : NativeReadyWritePreparation current.state} (seen : NativeGroupedKeeperSyncError prepared) :
    NativeReturnedGroupedKeeperError current seen :=
  current.returnsGroupedWriteSyncError seen.toGrouped

end Alvoki.Storage.DiskSession
