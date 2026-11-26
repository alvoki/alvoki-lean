import Alvoki.Storage.Disk.NativeRawUncertainWrite
import Alvoki.Storage.Disk.NativeWalFileFsyncEffects

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentCommit WalSegmentRepair
open WAL.Boundary (WalInodeImage)

/-- The reached grouped error keeps the old repair target. The live
keeper may include the attempted batch. A reboot samples the protected
manifest and the old marker and keeper from the same surviving map,
where the keeper may contain only part of the attempted batch. -/
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
    {initial entry appended staged reached : heap} {cause : IO.Error} :
    let directory := state.session.directory
    let first := state.writer.installed.activeFirst
    let keeperPath := directory.file (.walSegment first)
    let markerPath := directory.file .walBoundary
    let priorBytes := state.writer.wal.active.bytes
    let oldMarkerBytes := WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64
    let bytes := WAL.encodeBatch batch
    let count := state.writer.installed.walBytes + WAL.frameSize * rows.length
    let storage := fun heap => (observe heap).storageObservation
    NativeReadyStorage state (storage initial) →
    (storage initial).Frames (fun path => path = markerPath ∨ path = keeperPath) (storage entry) →
    (storage initial).Frames state.writeFramePath (storage reached) →
    (∀ keeper, (observe entry).visible keeperPath = some keeper → (inodes entry).visible keeper = priorBytes) →
    (∀ oldMarker, (observe entry).visible markerPath = some oldMarker → (inodes entry).visible oldMarker = oldMarkerBytes) →
    (∀ names ∈ (observe staged).crashBindings, names keeperPath = (observe entry).visible keeperPath) →
    (storage entry).Frames (· = markerPath) (storage staged) →
    (∀ oldMarker, (observe entry).visible markerPath = some oldMarker →
      (inodes staged).visible oldMarker = (inodes entry).visible oldMarker) →
    appender.run cache.active keeperPath bytes entry = .ok () appended →
    stager.run cache.pending (directory.file .stagedWalBoundary) (WAL.Boundary.encode count.toUInt64)
      appended = .ok () staged →
    syncer.group directory.path cache.directory cache.active cache.pending
      #[keeperPath, directory.file .stagedWalBoundary] staged = .error cause reached →
    (∀ keeper, (observe entry).visible keeperPath = some keeper →
      appender.KeeperEffects view cache.active keeperPath bytes entry appended
        (fun heap => (observe heap).visible) (fun heap => (inodes heap).visible) inode buffered keeper) →
    (∀ keeper, (observe appended).visible keeperPath = some keeper →
      stager.MarkerEffects cache view (WAL.Boundary.encode count.toUInt64) appended staged
        (fun heap => (observe heap).visible) (fun heap => (inodes heap).visible) inode buffered keeper) →
    (∀ {keeper oldMarker keeperHandle markerHandle},
      (observe entry).visible markerPath = some oldMarker →
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
    BatchRetryTarget state.writer.history batch state.writer.wal.active.first target ∧
    accepts (observe reached).visible (inodes reached).visible ∧
    ∀ names ∈ (storage reached).crashNames, ∀ contents,
      (∀ path inode,
        (path = directory.file .manifest ∨ path = markerPath ∨ path = keeperPath) →
        names path = some inode → contents inode ∈ (storage reached).files.bytes inode) →
      target.pair = ⟨(names (directory.file .manifest)).map contents, (names markerPath).map contents⟩ ∧
      target.Accepts ((names (directory.file (.walSegment state.writer.wal.active.first))).map contents) := by
  intro directory first keeperPath markerPath priorBytes oldMarkerBytes bytes count storage old startFrame
    protectedFrame keeperVisible markerVisible stagedNames prefixMarker prefixKeepsMarker wrote stagedMarker grouped
    appendEffects stageEffects barrierEffects target accepts
  have keeperFirst : first = state.writer.wal.active.first := valid.retained.resumed.keeper.trans valid.retained.active
  have initialKeeper : (storage initial).files.Stored keeperPath priorBytes := by
    simpa only [keeperPath, keeperFirst] using old.keeper
  obtain ⟨keeper, priorBinding, _⟩ := startFrame.visible.stored (.inr rfl) initialKeeper
  obtain ⟨oldMarker, markerBinding, markerBytes⟩ := startFrame.visible.stored (.inl rfl) old.marker
  have startMarker := startFrame.weaken (scope := (· = markerPath)) fun _ retained => .inl retained
  have markerCrash := startMarker.settledFrom (fun names survives path retained =>
    old.settled names survives path (NativeReadyState.crashPath_iff_write.mpr (.inl retained)))
  have settledMarker (names : FilePath → Option Nat) (survives : names ∈ (observe entry).crashBindings) :
      names markerPath = some oldMarker := (markerCrash names survives markerPath rfl).trans markerBinding
  obtain ⟨failed, markerNamed, markerStored, markerLive, keeperNamed, keeperLive, _, keeperStored, survived⟩ :=
    syncer.groupedFailurePreservesSelection cache view appender stager rename inodes observe inode buffered
      priorBinding (keeperVisible keeper priorBinding) markerBinding markerBytes (markerVisible oldMarker markerBinding)
      settledMarker (fun names survives => (stagedNames names survives).trans priorBinding)
      prefixMarker (prefixKeepsMarker oldMarker markerBinding) wrote stagedMarker grouped (appendEffects keeper priorBinding)
      (stageEffects keeper) (barrierEffects markerBinding)
  have oldCount : target.pair.walBoundary = some oldMarkerBytes := by
    have selected := congrArg DirectoryPublication.Bindings.walBoundary valid.retained.resumed.ready.selected
    exact selected.symm.trans (congrArg Publication.Image.active valid.retained.resumed.markerImage)
  have batchFits : (WAL.encode (state.writer.history ++ batch)).size < UInt64.size :=
    (NativeReadyState.preparedWalCount valid prepared).symm ▸ fits
  have oldTarget : BatchRetryTarget state.writer.history batch state.writer.wal.active.first target :=
    ⟨valid.retained.active, state.writer.history, .inl rfl, oldCount, valid.retained.resumed.through,
      valid.retained.resumed.contents.trans
        (congrArg (fun index => WAL.encode (state.writer.history.drop index)) valid.retained.active)⟩
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
      BatchRetryTarget.unique allowed oldTarget samePair
    refine ⟨by rw [marked, Option.map_some, oldBytes, oldCount], ?_⟩
    simpa only [sameTarget, keeperPath, keeperFirst] using acceptsKeeper
  refine ⟨failed, oldTarget, select _ _ markerNamed keeperNamed markerLive ⟨bytes, keeperLive⟩, ?_⟩
  intro names nameSurvives contents sample
  obtain ⟨marked, bound⟩ := survived names nameSurvives
  have markerSurvives := sample markerPath oldMarker (.inr (.inl rfl)) marked
  have keeperSurvives := sample keeperPath keeper (.inr (.inr rfl)) bound
  obtain ⟨boundary, keeperAccepted⟩ := select names contents marked bound
    (List.mem_singleton.mp (markerStored ▸ markerSurvives)) (keeperStored _ keeperSurvives)
  have manifest := old.selectedWriteManifest protectedFrame names nameSurvives contents (fun inode => sample _ inode (.inl rfl))
  refine ⟨?_, ?_⟩
  · rw [manifest, ← boundary]
  · simpa only [keeperPath, keeperFirst] using keeperAccepted

end Alvoki.Storage.DiskSession
