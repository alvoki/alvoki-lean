import Alvoki.Storage.Disk.Proofs.Write.NativeRawUncertainWrite
import Alvoki.Storage.Disk.NativeWalFileFsyncEffects

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentCommit WalSegmentRepair
open WAL.Boundary (WalInodeImage)

/-- A later map keeps the named keeper from an earlier map. Each
surviving byte choice at that inode extends an earlier choice. This
allows a failed write, flush or release to have a partial effect. -/
structure WalKeeperPrefixFrame (path : FilePath) (keeper : Nat)
    (entry reached : CheckpointStorageObservation) : Prop where
  names : ∀ chosen ∈ reached.crashNames, ∃ prior ∈ entry.crashNames, chosen path = prior path
  bytes : ∀ contents ∈ reached.files.bytes keeper,
    ∃ prior ∈ entry.files.bytes keeper, ∃ tail, contents = prior ++ tail

theorem WalKeeperPrefixFrame.refl (path : FilePath) (keeper : Nat) (atHeap : CheckpointStorageObservation) :
    WalKeeperPrefixFrame path keeper atHeap atHeap :=
  ⟨fun names chosen => ⟨names, chosen, rfl⟩,
    fun contents chosen => ⟨contents, chosen, ByteArray.empty, by simp⟩⟩

theorem WalKeeperPrefixFrame.trans {path : FilePath} {keeper : Nat}
    {entry middle reached : CheckpointStorageObservation}
    (first : WalKeeperPrefixFrame path keeper entry middle)
    (last : WalKeeperPrefixFrame path keeper middle reached) : WalKeeperPrefixFrame path keeper entry reached := by
  constructor
  · intro names chosen
    obtain ⟨mid, midChosen, latest⟩ := last.names names chosen
    obtain ⟨prior, priorChosen, earliest⟩ := first.names mid midChosen
    exact ⟨prior, priorChosen, latest.trans earliest⟩
  · intro contents chosen
    obtain ⟨mid, midChosen, tail, rfl⟩ := last.bytes contents chosen
    obtain ⟨prior, priorChosen, earlierTail, rfl⟩ := first.bytes mid midChosen
    exact ⟨prior, priorChosen, earlierTail ++ tail, ByteArray.append_assoc ..⟩

/-- A callback that leaves the keeper's bytes unchanged preserves the
prefix without any new tail. -/
theorem WalKeeperPrefixFrame.ofFileFrame {path : FilePath} {keeper : Nat}
    {entry reached : CheckpointStorageObservation}
    (frame : entry.Frames (· = path) reached) (named : entry.files.names path = some keeper) :
    WalKeeperPrefixFrame path keeper entry reached := by
  refine ⟨fun names chosen => ?_, fun contents chosen => ?_⟩
  · obtain ⟨prior, possible, same⟩ := frame.survivors names chosen
    exact ⟨prior, possible, same path rfl⟩
  · rw [(frame.visible path rfl).2 keeper named] at chosen
    exact ⟨contents, chosen, ByteArray.empty, by simp⟩

/-- The old marker selects exactly the original target regardless of
how much of the attempted batch survives after its keeper prefix. -/
theorem NativeReadyState.selectsPriorWriteWal {state : NativeReadyState} (valid : state.Valid)
    (batch : List WAL.Write) {observedMarker observedKeeper : Option ByteArray}
    (marker : observedMarker = some (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64))
    (keeper : ∃ tail, observedKeeper = some (state.writer.wal.active.bytes ++ tail)) :
    BatchRetryTarget state.writer.history batch state.writer.wal.active.first state.writer.target ∧
    state.writer.target.pair.walBoundary = observedMarker ∧ state.writer.target.Accepts observedKeeper := by
  have selected := congrArg DirectoryPublication.Bindings.walBoundary valid.retained.resumed.ready.selected
  have oldMarker : state.writer.target.pair.walBoundary = some (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64) :=
    selected.symm.trans (congrArg Publication.Image.active valid.retained.resumed.markerImage)
  have prefixBytes : state.writer.target.trimmed = WAL.encode (state.writer.history.drop state.writer.wal.active.first) :=
    valid.retained.resumed.contents.trans
      (congrArg (fun index => WAL.encode (state.writer.history.drop index)) valid.retained.active)
  obtain ⟨tail, appended⟩ := keeper
  refine ⟨⟨valid.retained.active, state.writer.history, .inl rfl, oldMarker,
    valid.retained.resumed.through, prefixBytes⟩, oldMarker.trans marker.symm, tail, ?_⟩
  exact appended.trans (congrArg (fun bytes => some (bytes ++ tail))
    (valid.retained.layout.activeBytes.trans prefixBytes.symm))

/-- Before marker publication, the marker frame and keeper-prefix
frame independently constrain the chosen replica of the same map. -/
theorem NativeReadyState.priorWriteTargetOfSample {state : NativeReadyState} (valid : state.Valid)
    (batch : List WAL.Write) {entry reached : CheckpointStorageObservation}
    (old : NativeReadyStorage state entry)
    (protectedFrame : entry.Frames state.writeFramePath reached) :
    let directory := state.session.directory
    let keeperPath := directory.file (.walSegment state.writer.wal.active.first)
    let markerPath := directory.file .walBoundary
    entry.Frames (· = markerPath) reached →
    (∀ keeper, entry.files.names keeperPath = some keeper → WalKeeperPrefixFrame keeperPath keeper entry reached) →
    ∀ names ∈ reached.crashNames, ∀ contents : Nat → ByteArray,
      (∀ path inode, (path = directory.file .manifest ∨ path = markerPath ∨ path = keeperPath) →
        names path = some inode → contents inode ∈ reached.files.bytes inode) →
      BatchRetryTarget state.writer.history batch state.writer.wal.active.first state.writer.target ∧
      state.writer.target.pair = ⟨(names (directory.file .manifest)).map contents, (names markerPath).map contents⟩ ∧
      state.writer.target.Accepts ((names keeperPath).map contents) := by
  intro directory keeperPath markerPath markerFrame keeperFrames names chosen contents sample
  obtain ⟨marker, markerNamed, markerStored⟩ := markerFrame.visible.stored rfl old.marker
  have settledMarker := markerFrame.settledFrom (fun names survives path retained =>
    old.settled names survives path (NativeReadyState.crashPath_iff_write.mpr (.inl retained)))
  have marked := (settledMarker names chosen markerPath rfl).trans markerNamed
  have markerContents := List.mem_singleton.mp (markerStored ▸ sample _ _ (.inr (.inl rfl)) marked)
  obtain ⟨keeper, keeperNamed, keeperStored⟩ := old.keeper
  have keeperFrame := keeperFrames keeper keeperNamed
  obtain ⟨prior, priorChosen, sameKeeper⟩ := keeperFrame.names names chosen
  have bound := sameKeeper.trans ((old.settled prior priorChosen keeperPath
    (NativeReadyState.crashPath_iff_write.mpr (.inr (.inl rfl)))).trans keeperNamed)
  obtain ⟨earlier, survived, tail, appended⟩ := keeperFrame.bytes _ (sample _ _ (.inr (.inr rfl)) bound)
  have known := List.mem_singleton.mp (keeperStored ▸ survived)
  obtain ⟨admitted, boundary, accepted⟩ := NativeReadyState.selectsPriorWriteWal valid batch
    (observedMarker := (names markerPath).map contents) (observedKeeper := (names keeperPath).map contents)
    (by rw [marked, Option.map_some, markerContents])
    ⟨tail, by rw [bound, Option.map_some, appended, known]⟩
  have manifest := old.selectedWriteManifest protectedFrame names chosen contents (fun inode => sample _ inode (.inl rfl))
  exact ⟨admitted, by rw [manifest, ← boundary], accepted⟩

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
    {rows : List (UInt64 × Option UInt64)} {batch : List WAL.Write}
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
  have select (names : FilePath → Option Nat) (contents : Nat → ByteArray)
      (marked : names markerPath = some oldMarker) (bound : names keeperPath = some keeper)
      (oldBytes : contents oldMarker = oldMarkerBytes) (kept : ∃ tail, contents keeper = priorBytes ++ tail) :
      BatchRetryTarget state.writer.history batch state.writer.wal.active.first target ∧ accepts names contents := by
    obtain ⟨tail, appended⟩ := kept
    exact NativeReadyState.selectsPriorWriteWal valid batch (by rw [marked, Option.map_some, oldBytes])
      ⟨tail, by rw [bound, Option.map_some, appended]⟩
  obtain ⟨oldTarget, live⟩ := select _ _ markerNamed keeperNamed markerLive ⟨bytes, keeperLive⟩
  refine ⟨failed, oldTarget, live, ?_⟩
  intro names nameSurvives contents sample
  obtain ⟨marked, bound⟩ := survived names nameSurvives
  have markerSurvives := sample markerPath oldMarker (.inr (.inl rfl)) marked
  have keeperSurvives := sample keeperPath keeper (.inr (.inr rfl)) bound
  obtain ⟨_, boundary, keeperAccepted⟩ := select names contents marked bound
    (List.mem_singleton.mp (markerStored ▸ markerSurvives)) (keeperStored _ keeperSurvives)
  have manifest := old.selectedWriteManifest protectedFrame names nameSurvives contents (fun inode => sample _ inode (.inl rfl))
  refine ⟨?_, ?_⟩
  · rw [manifest, ← boundary]
  · simpa only [keeperPath, keeperFirst] using keeperAccepted

end Alvoki.Storage.DiskSession
