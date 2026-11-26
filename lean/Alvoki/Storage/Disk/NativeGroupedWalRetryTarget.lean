import Alvoki.Storage.Disk.NativeRawUncertainWrite
import Alvoki.Storage.Disk.NativeWalFileFsyncEffects

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentCommit WalSegmentRepair
open WAL.Boundary (WalInodeImage)

/-- A returned failure at the file barrier leaves the same retry cutoff
for the live directory and for every joint surviving name and byte choice.
The old marker can ignore a surviving suffix of the attempted batch. -/
theorem NativeReadyState.groupedFailureAcceptsOldWal {heap image : Type} {state : NativeReadyState}
    (valid : state.Valid) {files : DiskTable.OpenSyncFiles}
    (cache : OpenSyncCacheRefs files state.session.directory.path) (view : OpenCloseHeapView heap image)
    (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap) (syncer : RawSyncCalls heap)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (inodes : heap → WalInodeImage) {runs : heap → RunUnlinkImage}
    (observe : ∀ heap, RunDirectoryInodeView state.session.directory (inodes heap) (runs heap))
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
    {rows : List (UInt64 × Option UInt64)} {batch : List WAL.Write} {table : PackedTable}
    (prepared : prepareBatch state.writer.installed.table rows = some (batch, table))
    (fits : state.writer.installed.walBytes + WAL.frameSize * rows.length < UInt64.size)
    {keeper oldMarker : Nat} {entry appended staged reached : heap} {cause : IO.Error} :
    let directory := state.session.directory
    let first := state.writer.installed.activeFirst
    let keeperPath := directory.file (.walSegment first)
    let markerPath := directory.file .walBoundary
    let priorBytes := state.writer.wal.active.bytes
    let oldMarkerBytes := WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64
    let bytes := WAL.encodeBatch batch
    let count := state.writer.installed.walBytes + WAL.frameSize * rows.length
    (observe entry).visible keeperPath = some keeper →
    (inodes entry).visible keeper = priorBytes →
    (observe entry).Stable markerPath oldMarker oldMarkerBytes →
    (∀ names ∈ (observe staged).crashBindings, names keeperPath = some keeper) →
    (observe entry).storageObservation.Frames (· = markerPath) (observe staged).storageObservation →
    (inodes staged).visible oldMarker = (inodes entry).visible oldMarker →
    appender.run cache.active keeperPath bytes entry = .ok () appended →
    stager.run cache.pending (directory.file .stagedWalBoundary) (WAL.Boundary.encode count.toUInt64)
      appended = .ok () staged →
    syncer.group directory.path cache.directory cache.active cache.pending
      #[keeperPath, directory.file .stagedWalBoundary] staged = .error cause reached →
    appender.KeeperEffects view cache.active keeperPath bytes entry appended
      (fun heap => (observe heap).visible) (fun heap => (inodes heap).visible) inode buffered keeper →
    ((observe appended).visible keeperPath = some keeper →
      stager.MarkerEffects cache view (WAL.Boundary.encode count.toUInt64) appended staged
        (fun heap => (observe heap).visible) (fun heap => (inodes heap).visible) inode buffered keeper) →
    (∀ {keeperHandle markerHandle},
      (observe appended).visible keeperPath = some keeper →
      inode keeperHandle = keeper →
      view.active appended cache.active = some (keeperPath, keeperHandle) →
      view.literalCacheAt staged cache.directory cache.active cache.pending =
        (view.literalCacheAt appended cache.directory cache.active cache.pending).remember
          (directory.file .stagedWalBoundary) markerHandle →
      syncer.GroupedFailureFileEffects cache view inodes observe first appended staged keeperHandle markerHandle
        keeper (inode markerHandle) oldMarker priorBytes) →
    let target := state.writer.target
    let accepts := fun (names : FilePath → Option Nat) (contents : Nat → ByteArray) =>
      target.pair.walBoundary = (names markerPath).map contents ∧ target.Accepts ((names keeperPath).map contents)
    commitBytesAt directory first bytes count (appender.run cache.active) (stager.run cache.pending)
      (syncer.group directory.path cache.directory cache.active cache.pending) rename entry = .error cause reached ∧
    BatchRetryTarget state.writer.history batch first target ∧
    accepts (observe reached).visible (inodes reached).visible ∧
    ∀ names ∈ (observe reached).crashBindings, ∀ contents,
      contents oldMarker ∈ (inodes reached).crashBytes oldMarker →
      contents keeper ∈ (inodes reached).crashBytes keeper → accepts names contents := by
  intro directory first keeperPath markerPath priorBytes oldMarkerBytes bytes count priorBinding priorVisible
    marker settledKeeper prefixMarker prefixKeepsMarker wrote stagedMarker grouped appendEffects stageEffects barrierEffects
    target accepts
  obtain ⟨failed, markerNamed, markerStored, markerLive, keeperNamed, keeperLive, _, keeperStored, survived⟩ :=
    syncer.groupedFailurePreservesSelection cache view appender stager rename inodes observe inode buffered
      priorBinding priorVisible marker.visibleBinding marker.crashBytes marker.visibleBytes marker.crashBinding
      settledKeeper prefixMarker prefixKeepsMarker wrote stagedMarker grouped appendEffects stageEffects barrierEffects
  have keeperFirst : first = state.writer.wal.active.first := valid.retained.resumed.keeper.trans valid.retained.active
  have oldCount : target.pair.walBoundary = some oldMarkerBytes := by
    have selected := congrArg DirectoryPublication.Bindings.walBoundary valid.retained.resumed.ready.selected
    exact selected.symm.trans (congrArg Publication.Image.active valid.retained.resumed.markerImage)
  have batchFits : (WAL.encode (state.writer.history ++ batch)).size < UInt64.size := by
    rw [WAL.encode_size, List.length_append, Nat.mul_add, (prepareBatch_spec prepared).1,
      ← WAL.encode_size, ← valid.retained.resumed.bytes]
    exact fits
  have oldTarget : BatchRetryTarget state.writer.history batch first target :=
    ⟨valid.retained.resumed.keeper.symm, state.writer.history, .inl rfl, oldCount,
      valid.retained.resumed.through, valid.retained.resumed.contents.trans
        (congrArg (fun index => WAL.encode (state.writer.history.drop index)) valid.retained.resumed.keeper.symm)⟩
  have select (names : FilePath → Option Nat) (contents : Nat → ByteArray)
      (marked : names markerPath = some oldMarker) (bound : names keeperPath = some keeper)
      (oldBytes : contents oldMarker = oldMarkerBytes) (kept : ∃ tail, contents keeper = priorBytes ++ tail) :
      accepts names contents := by
    have boundActive : names (directory.file (.walSegment state.writer.wal.active.first)) = some keeper := by
      simpa only [keeperPath, keeperFirst] using bound
    obtain ⟨selected, allowed, pair, acceptsKeeper⟩ :=
      NativeReadyState.selectsWriteWal valid batchFits names contents marked boundActive (.inl ⟨oldBytes, kept⟩)
    have samePair : selected.pair = target.pair := by
      rw [pair, marked, Option.map_some, oldBytes, ← oldCount]
    have sameTarget : selected = target :=
      BatchRetryTarget.unique allowed (keeperFirst ▸ oldTarget) samePair
    refine ⟨by rw [marked, Option.map_some, oldBytes, oldCount], ?_⟩
    simpa only [sameTarget, keeperPath, keeperFirst] using acceptsKeeper
  refine ⟨failed, oldTarget, select _ _ markerNamed keeperNamed markerLive ⟨bytes, keeperLive⟩, ?_⟩
  intro names nameSurvives contents markerSurvives keeperSurvives
  obtain ⟨marked, bound⟩ := survived names nameSurvives
  exact select names contents marked bound (List.mem_singleton.mp (markerStored ▸ markerSurvives))
    (keeperStored _ keeperSurvives)

end Alvoki.Storage.DiskSession
