import Alvoki.Storage.Disk.Proofs.Native.WAL.NativeGroupedWalRetryTarget
import Alvoki.Storage.Disk.Proofs.Write.NativeRawWriteReboot

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentCommit WalSegmentRepair
open WAL.Boundary (WalInodeImage)

/-- File effects of the three reached group-error callbacks and the
marker/keeper footprint of the guard and poison phase update. -/
structure RawSyncCalls.GroupFailureEffects {heap : Type} (calls : RawSyncCalls heap)
    {state : NativeReadyState} {files : DiskTable.OpenSyncFiles}
    (cache : OpenSyncCacheRefs files state.session.directory.path) (view : OpenCloseHeapView heap FileImage)
    (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap)
    (inodes : heap → WalInodeImage) {runs : heap → RunUnlinkImage}
    (observe : ∀ heap, RunDirectoryInodeView state.session.directory (inodes heap) (runs heap))
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
    (rows : List (UInt64 × Option UInt64)) (batch : List WAL.Write) (initial poisoned appended staged : heap) :
    Prop where
  startFrame : (observe initial).storageObservation.Frames
    (fun path => path = state.session.directory.file .walBoundary ∨
      path = state.session.directory.file (.walSegment state.writer.installed.activeFirst))
    (observe poisoned).storageObservation
  keeperVisible : ∀ keeper,
    (observe poisoned).visible (state.session.directory.file (.walSegment state.writer.installed.activeFirst)) = some keeper →
    (inodes poisoned).visible keeper = state.writer.wal.active.bytes
  markerVisible : ∀ marker,
    (observe poisoned).visible (state.session.directory.file .walBoundary) = some marker →
    (inodes poisoned).visible marker = WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64
  stagedNames : ∀ names ∈ (observe staged).crashBindings,
    names (state.session.directory.file (.walSegment state.writer.installed.activeFirst)) =
      (observe poisoned).visible (state.session.directory.file (.walSegment state.writer.installed.activeFirst))
  markerFrame : (observe poisoned).storageObservation.Frames (· = state.session.directory.file .walBoundary)
    (observe staged).storageObservation
  stagedMarkerVisible : ∀ marker, (observe poisoned).visible (state.session.directory.file .walBoundary) = some marker →
    (inodes staged).visible marker = (inodes poisoned).visible marker
  appendFile : ∀ keeper,
    (observe poisoned).visible (state.session.directory.file (.walSegment state.writer.installed.activeFirst)) = some keeper →
    appender.KeeperEffects view cache.active (state.session.directory.file (.walSegment state.writer.installed.activeFirst))
      (WAL.encodeBatch batch) poisoned appended (fun heap => (observe heap).visible) (fun heap => (inodes heap).visible)
      inode buffered keeper
  stageFile : ∀ keeper,
    (observe appended).visible (state.session.directory.file (.walSegment state.writer.installed.activeFirst)) = some keeper →
    stager.MarkerEffects cache view
      (WAL.Boundary.encode (state.writer.installed.walBytes + WAL.frameSize * rows.length).toUInt64) appended staged
      (fun heap => (observe heap).visible) (fun heap => (inodes heap).visible) inode buffered keeper
  fileBarriers : ∀ {keeper oldMarker keeperHandle markerHandle},
    (observe poisoned).visible (state.session.directory.file .walBoundary) = some oldMarker →
    (observe appended).visible (state.session.directory.file (.walSegment state.writer.installed.activeFirst)) = some keeper →
    inode keeperHandle = keeper →
    view.active appended cache.active =
      some (state.session.directory.file (.walSegment state.writer.installed.activeFirst), keeperHandle) →
    view.literalCacheAt staged cache.directory cache.active cache.pending =
      (view.literalCacheAt appended cache.directory cache.active cache.pending).remember
        (state.session.directory.file .stagedWalBoundary) markerHandle →
    calls.GroupedFailureFileEffects cache view inodes observe state.writer.installed.activeFirst appended staged
      keeperHandle markerHandle keeper (inode markerHandle) oldMarker state.writer.wal.active.bytes

section

variable {heap : Type} {state : NativeReadyState} {files : DiskTable.OpenSyncFiles}
  (cache : OpenSyncCacheRefs files state.session.directory.path) (view : OpenCloseHeapView heap FileImage)
  (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap) (calls : RawSyncCalls heap)
  (inodes : heap → WalInodeImage) {runs : heap → RunUnlinkImage}
  (observe : ∀ heap, RunDirectoryInodeView state.session.directory (inodes heap) (runs heap))
  (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)

local notation "dir" => state.session.directory
local notation "first" => state.writer.installed.activeFirst
local notation "append" => appender.run cache.active
local notation "stage" => stager.run cache.pending
local notation "sync" => calls.group state.session.directory.path cache.directory cache.active cache.pending
local notation "storage" => fun heap => RunDirectoryInodeView.storageObservation (observe heap)

/-- The grouped-error receipts share their poisoned entry and return
heap with the write's protected-file frame. The selected reboot admits
the original repair target even when a prefix of the batch survived. -/
theorem RawWriteRebootEntry.selectsGroupErrorRetry
    {initial poisoned appended staged reached rebooted : heap} {cause : IO.Error}
    {rows : List (UInt64 × Option UInt64)} {batch : List WAL.Write}
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (valid : state.Valid) (old : NativeReadyStorage state (storage initial))
    (protectedFrame : (storage initial).Frames state.writeFramePath (storage reached))
    (wrote : append ((dir).file (.walSegment first)) (WAL.encodeBatch batch) poisoned = .ok () appended)
    (remembered : stage ((dir).file .stagedWalBoundary)
      (WAL.Boundary.encode (state.writer.installed.walBytes + WAL.frameSize * rows.length).toUInt64)
      appended = .ok () staged)
    (failed : sync #[ (dir).file (.walSegment first), (dir).file .stagedWalBoundary ] staged = .error cause reached)
    (effects : calls.GroupFailureEffects cache view appender stager inodes observe inode buffered rows batch
      initial poisoned appended staged)
    {names : heap → FilePath → Option Nat} {visible : heap → Nat → ByteArray}
    (seen : RawWriteRebootEntry state view storage names visible reached rebooted) :
    commitBytesAt dir first (WAL.encodeBatch batch) (state.writer.installed.walBytes + WAL.frameSize * rows.length)
      append stage sync rename poisoned = .error cause reached ∧
    BatchRetryTarget state.writer.history batch state.writer.wal.active.first state.writer.target ∧
    RawOpenRetryTrace.SelectedEntry view state state.writer.target names visible rebooted ∧
    TryLockObserves (view.files rebooted).owners dir (.ok true) ∧
    (view.descriptors rebooted).slots = [] := by
  obtain ⟨returned, admitted, _, selected⟩ :=
    NativeReadyState.groupedFailureAcceptsOldWal valid cache view appender stager calls rename inodes observe inode buffered
      old effects.startFrame protectedFrame effects.keeperVisible effects.markerVisible
      effects.stagedNames effects.markerFrame effects.stagedMarkerVisible wrote remembered failed
      effects.appendFile effects.stageFile effects.fileBarriers
  have sameFirst : state.writer.installed.activeFirst = state.writer.wal.active.first :=
    valid.retained.resumed.keeper.trans valid.retained.active
  obtain ⟨pair, keeper⟩ := selected (names rebooted) seen.chosen (visible rebooted)
    (fun path inode scope named => seen.samplesWal path inode (by simpa only [sameFirst] using scope) named)
  exact ⟨returned, admitted, seen.selectsRetry old protectedFrame admitted pair keeper⟩

end
end Alvoki.Storage.DiskSession
