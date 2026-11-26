import Alvoki.Storage.Disk.NativeClassifiedWriteAck
import Alvoki.Storage.Disk.NativeRawWriteCustody
import Alvoki.Storage.Disk.NativeOpenedPosition
import Alvoki.Storage.Disk.NativeWalFileFsyncEffects
import Alvoki.Storage.Disk.NativeRawUncertainWrite

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WalSegmentCommit SyncHandleRouting CheckpointPublication
open WAL.Boundary (WalInodeImage)

/-- Preserve the selected checkpoint and seals independently of WAL
publication. The ready phase update frames the entire reached footprint
and preserves the common crash-name choice. -/
theorem NativeReadyStorage.afterPublishedWrite {before : NativeReadyState} {writer : SegmentedWriterState}
    {cache : CensusDirectoryCache} (custody : NativePendingWriteCensus before cache)
    (sameManifest : writer.target.pair.manifest = before.writer.target.pair.manifest)
    (sameRuns : writer.published.durable = before.writer.published.durable)
    (sameSeals : writer.wal.sealed = before.writer.wal.sealed)
    (sameKeeper : writer.wal.active.first = before.writer.wal.active.first)
    {entry published returned : CheckpointStorageObservation} (old : NativeReadyStorage before entry)
    (framed : entry.Frames before.writeFramePath published)
    (restored : published.Frames before.crashPath returned)
    (keeper : published.files.Stored (before.session.directory.file (.walSegment before.writer.wal.active.first)) writer.wal.active.bytes)
    (marker : published.files.Stored (before.session.directory.file .walBoundary)
      (WAL.Boundary.encode (WAL.encode writer.history).size.toUInt64))
    (settled : ∀ names ∈ published.crashNames,
      names (before.session.directory.file (.walSegment before.writer.wal.active.first)) =
        published.files.names (before.session.directory.file (.walSegment before.writer.wal.active.first)) ∧
      names (before.session.directory.file .walBoundary) = published.files.names (before.session.directory.file .walBoundary)) :
    NativeReadyStorage (before.afterWrite writer cache custody) returned := by
  let next := before.afterWrite writer cache custody
  have paths (path) : next.writeFramePath path ↔ before.writeFramePath path := by
    simp only [NativeReadyState.writeFramePath, NativeReadyState.afterWrite, next, sameManifest, sameSeals]
  have stable : ∀ names ∈ published.crashNames, ∀ path, before.crashPath path → names path = published.files.names path := by
    intro names allowed path selected
    rcases NativeReadyState.crashPath_iff_write.mp selected with rfl | rfl | kept
    · exact (settled names allowed).2
    · exact (settled names allowed).1
    · exact framed.settledFrom (fun prior possible path keep =>
        old.settled prior possible path (NativeReadyState.crashPath_iff_write.mpr (.inr (.inr keep)))) names allowed path kept
  have protectedFrame := framed.trans (restored.weaken fun _ kept =>
    NativeReadyState.crashPath_iff_write.mpr (.inr (.inr kept)))
  have retained := old.toNativeReadyProtectedStorage.frame protectedFrame.visible
  have keptFiles : NativeReadyProtectedStorage next returned.files := by
    refine ⟨retained.directoryBound.trans (congrArg some custody.sameDirectory.symm),
      retained.lockBound.trans (congrArg some custody.lockInode.symm), ?_, ?_, ?_⟩
    · change (match writer.target.pair.manifest with | none => _ | some _ => _)
      rw [sameManifest]
      exact retained.manifest
    · intro segment member
      exact retained.sealedFiles segment (sameSeals ▸ member)
    · intro payload metadata selected decoded index within runBytes known
      change writer.target.pair.manifest = some payload at selected
      rw [sameManifest] at selected
      exact retained.runs _ _ selected decoded _ within _ (sameRuns ▸ known)
  have keeperPath := NativeReadyState.crashPath_iff_write (state := before) |>.mpr (.inr (.inl rfl))
  have markerPath := NativeReadyState.crashPath_iff_write (state := before) |>.mpr (.inl rfl)
  refine ⟨keptFiles, restored.visible.stored markerPath marker, ?_, ?_⟩
  · change returned.files.Stored (before.session.directory.file (.walSegment writer.wal.active.first)) writer.wal.active.bytes
    rw [sameKeeper]
    exact restored.visible.stored keeperPath keeper
  · intro names allowed path selected
    apply restored.settledFrom stable names allowed path
    apply NativeReadyState.crashPath_iff_write.mpr
    rcases NativeReadyState.crashPath_iff_write.mp selected with markerName | keeperName | kept
    · exact .inl markerName
    · exact .inr (.inl (keeperName.trans (congrArg (fun first =>
        before.session.directory.file (.walSegment first)) sameKeeper)))
    · exact .inr (.inr ((paths path).mp kept))

/-- The shared physical entry of a raw write on an already opened
handle. Each field refers to the same reached heap and actual cache. -/
structure NativeOpenedPosition.WriteStorageEntry {heap image : Type} {opened : NativeOpenedHandle heap}
    (current : NativeOpenedPosition opened) (view : OpenCloseHeapView heap image)
    (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)
    (storage : CheckpointStorageObservation) (visible : Nat → ByteArray) : Prop where
  census : view.descriptors current.reached = current.current.ready.state.census
  cacheAt : view.cacheAt current.reached cache.directory cache.active cache.pending = current.current.ready.state.cache
  physical : NativeReadyStorage current.current.ready.state storage
  keeper : ∀ inode, storage.files.names (current.current.ready.state.session.directory.file
    (.walSegment current.current.ready.state.writer.wal.active.first)) = some inode →
    visible inode = current.current.ready.state.writer.wal.active.bytes
  root : ∀ literal, view.directory current.reached cache.directory = some literal →
    storage.files.names current.current.ready.state.session.directory.path =
      some ((view.handle current.reached literal).1.inode (view.handle current.reached literal).2.1.description)

private def observedStorage {heap : Type} {directory : DiskDirectory}
    {inodes : heap → WalInodeImage} {runs : heap → RunUnlinkImage}
    (observe : ∀ heap, RunDirectoryInodeView directory (inodes heap) (runs heap))
    (atHeap : heap) : CheckpointStorageObservation :=
  (observe atHeap).storageObservation

private def keepsVisibleBytes {heap : Type} (path : FilePath)
    (names : heap → FilePath → Option Nat) (inodes : heap → WalInodeImage) (entry after : heap) : Prop :=
  ∀ inode, names entry path = some inode → (inodes after).visible inode = (inodes entry).visible inode

section RawWrite

variable {heap image : Type} {opened : NativeOpenedHandle heap}
  (current : NativeOpenedPosition opened)
  (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap) (syncer : RawSyncCalls heap)
  (view : OpenCloseHeapView heap image)
  (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)
  (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
  (observe : ∀ heap, RunDirectoryInodeView current.current.ready.state.session.directory (inodes heap) (runs heap))

local notation "before" => current.current.ready.state
local notation "dir" => current.current.ready.state.session.directory
local notation "oldInstalled" => current.current.ready.state.writer.installed
local notation "append" => appender.run cache.active
local notation "stage" => stager.run cache.pending
local notation "sync" => syncer.group current.current.ready.state.session.directory.path cache.directory cache.active cache.pending

local notation "storage" => observedStorage observe
local notation "keeperPath" => current.current.ready.state.session.directory.file
  (DiskFile.walSegment current.current.ready.state.writer.installed.activeFirst)
local notation "keepsVisibleKeeper" => keepsVisibleBytes keeperPath
  (fun atHeap => RunDirectoryInodeView.visible (observe atHeap)) inodes

/-- Physical effects at the individual callbacks of a published write.
The contract mentions only the reached primitives and their observations. -/
structure NativeOpenedPosition.PublishedWriteEffects
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
    (request : WriteRequest) (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) (batch : List WAL.Write) : Prop where
  guardEffect : ∀ {after}, checkActiveSegmentWith dir oldInstalled lookup current.reached = .ok () after →
      (storage current.reached).Frames (before).crashPath (storage after) ∧
        view.writeAuthorityAt before cache.directory after = view.writeAuthorityAt before cache.directory current.reached ∧
        keepsVisibleKeeper current.reached after
  phaseEffect : ∀ {value entry after}, opened.set opened.phase value entry = .ok () after →
      opened.contents after opened.phase = some value ∧ (storage entry).Frames (before).crashPath (storage after) ∧
        view.writeAuthorityAt before cache.directory after = view.writeAuthorityAt before cache.directory entry ∧
        keepsVisibleKeeper entry after
  appendFrame : let frame := view.framesWrite before cache.directory storage
      ∀ entry, frame entry (reachedState (append ((dir).file (.walSegment (oldInstalled).activeFirst))
        (WAL.encodeBatch batch) entry))
  stageFrame : let frame := view.framesWrite before cache.directory storage
      ∀ entry, frame entry (reachedState (stage ((dir).file .stagedWalBoundary)
        (WAL.Boundary.encode ((oldInstalled).walBytes + WAL.frameSize * request.rows.length).toUInt64) entry))
  groupFrame : let frame := view.framesWrite before cache.directory storage
      ∀ entry, frame entry (reachedState (sync
        #[(dir).file (.walSegment (oldInstalled).activeFirst), (dir).file .stagedWalBoundary] entry))
  renameFrame : let frame := view.framesWrite before cache.directory storage
      ∀ entry, frame entry (reachedState (rename ((dir).file .stagedWalBoundary) ((dir).file .walBoundary) entry))
  rootFrame : let frame := view.framesWrite before cache.directory storage
      ∀ entry, frame entry (reachedState (sync #[(dir).path] entry))
  appendEffects : let bytes := WAL.encodeBatch batch
      ∀ {entry appended keeper},
        append keeperPath bytes entry = .ok () appended →
        (observe entry).visible keeperPath = some keeper →
        appender.KeeperEffects view cache.active keeperPath bytes entry appended
          (fun heap => (observe heap).visible) (fun heap => (inodes heap).visible) inode buffered keeper
  stageEffects : let mark := WAL.Boundary.encode ((oldInstalled).walBytes + WAL.frameSize * request.rows.length).toUInt64
      ∀ {appended staged keeper},
        (observe appended).visible keeperPath = some keeper →
        stage ((dir).file .stagedWalBoundary) mark appended = .ok () staged →
        stager.MarkerEffects cache view mark appended staged
          (fun heap => (observe heap).visible) (fun heap => (inodes heap).visible) inode buffered keeper
  barrierEffects : ∀ {appended staged grouped keeper keeperHandle markerHandle},
      sync #[ keeperPath, (dir).file .stagedWalBoundary ] staged = .ok () grouped →
      (observe appended).visible keeperPath = some keeper →
      inode keeperHandle = keeper →
      view.active appended cache.active = some (keeperPath, keeperHandle) →
      view.literalCacheAt staged cache.directory cache.active cache.pending =
        (view.literalCacheAt appended cache.directory cache.active cache.pending).remember
          ((dir).file .stagedWalBoundary) markerHandle →
      ∃ consumed, syncer.GroupedFileEffects cache view inodes observe (oldInstalled).activeFirst
        appended staged consumed grouped keeperHandle markerHandle keeper (inode markerHandle)
  renameEffect : ∀ {entry after}, rename ((dir).file .stagedWalBoundary) ((dir).file .walBoundary) entry = .ok () after →
      ∀ inode, (storage entry).files.names ((dir).file .stagedWalBoundary) = some inode →
        (storage after).files.names ((dir).file .walBoundary) = some inode ∧
        (storage after).files.names ((dir).file .stagedWalBoundary) = none ∧
        (storage after).files.bytes inode = (storage entry).files.bytes inode
  stagedPrivate : ∀ {entry after}, rename ((dir).file .stagedWalBoundary) ((dir).file .walBoundary) entry = .ok () after →
      ∀ inode, (storage entry).files.names ((dir).file .stagedWalBoundary) = some inode →
        (storage entry).files.names ((dir).file .walBoundary) ≠ some inode
  renameFiles : ∀ {entry after}, rename ((dir).file .stagedWalBoundary) ((dir).file .walBoundary) entry = .ok () after →
      (storage entry).files.Frames (fun path => path ≠ (dir).file .stagedWalBoundary ∧ path ≠ (dir).file .walBoundary)
        (storage after).files ∧ keepsVisibleKeeper entry after
  loadEffect : ∀ {entry after handle}, syncer.readDirectory cache.directory entry = .ok (some handle) after →
      RawFsyncTarget view entry after handle ∧
      (storage entry).files.names (dir).path = some ((view.handle entry handle).1.inode
        (view.handle entry handle).2.1.description) ∧
      (storage entry).files.Frames (fun path => path = (dir).path ∨ ∃ file, path = (dir).file file)
        (storage after).files ∧ keepsVisibleKeeper entry after
  syncEffect : ∀ {issued after handle}, syncer.fsync handle issued = .ok () after →
      (view.handle issued handle).2.1 ∈ (view.descriptors issued).slots →
      (storage issued).files.names (dir).path = some ((view.descriptors issued).inode (view.handle issued handle).2.1.description) →
      (storage issued).files.Frames (fun path => path = (dir).path ∨ ∃ file, path = (dir).file file)
        (storage after).files ∧ keepsVisibleKeeper issued after ∧ (storage after).crashNames ≠ [] ∧
      ∀ names ∈ (storage after).crashNames, ∀ file, names ((dir).file file) = (storage after).files.names ((dir).file file)

/-- One acknowledged raw call supplies the next retained writer and its
prior read ledger. The committed storage is observed at the last
publication barrier, and the original phase setter carries it to the
actual returned heap. The append and staging effects determine the
payloads recorded by the file barriers. The returned writer supplies
the physical entry for another write using the same cache references. -/
theorem NativeOpenedPosition.acknowledgesPublishedWrite
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
    (request : WriteRequest)
    (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {sequence : UInt64} {reached : heap}
    (nonempty : request.rows ≠ [])
    (returned : request.runOnRawOpenPhase dir lookup append stage sync rename
      opened.phase opened.get opened.set current.reached = .ok sequence reached)
    (entry : current.WriteStorageEntry view cache (storage current.reached) (inodes current.reached).visible)
    (effects : ∀ {batch table}, prepareBatch (oldInstalled).table request.rows = some (batch, table) →
      current.PublishedWriteEffects appender stager syncer view cache inodes runs observe
        inode buffered request lookup rename batch) :
    opened.table.UsesOpenWriteSchedules dir opened.files opened.phase ∧
    ∃ (batch : List WAL.Write) (table : PackedTable) (next : NativeOpenedPosition opened)
      (sameDirectory : next.current.ready.state.session.directory = dir),
      prepareBatch (oldInstalled).table request.rows = some (batch, table) ∧
      sequence = table.committed ∧ next.reached = reached ∧ next.pins = current.pins ∧
      current.current.LedgerSuffix [.acknowledged request batch] next.current ∧
      next.WriteStorageEntry view
        ⟨cache.directory, cache.active, cache.pending, cache.references,
          (congrArg DiskDirectory.path sameDirectory).symm ▸ cache.atRoot⟩
        (storage next.reached) (inodes next.reached).visible ∧
      next.current.ready.state.writer.wal.segments.map WalSegment.first =
        (before).writer.wal.segments.map WalSegment.first := by
  obtain ⟨entryCensus, entryCache, old, entryKeeper, root⟩ := entry
  obtain ⟨valid, history, _⟩ := current.current.ready.readPrefix.refines
  have loaded := opened.phaseEffects.reads current.reached opened.phase _ (current.stored.trans (congrArg some valid.phase))
  obtain ⟨batch, table, prepared, fits⟩ := request.runOnRawOpenPhase_prepared dir lookup append stage sync rename
    opened.phase opened.get opened.set loaded nonempty (by rw [returned]; trivial)
  obtain ⟨guardEffect, phaseEffect, appendFrame, stageFrame, groupFrame, renameFrame, rootFrame,
    appendEffects, stageEffects, barrierEffects, renameEffect, stagedPrivate, renameFiles, loadEffect, syncEffect⟩ := effects prepared
  obtain ⟨guarded, poisoned, settled, guard, excluded, committed, installed, number, _, _⟩ :=
    request.runOnRawOpenPhase_acknowledges dir lookup append stage sync rename opened.phase opened.get opened.set
      loaded nonempty prepared fits returned
  obtain ⟨guardFrame, guardAuthority, guardVisible⟩ := guardEffect guard
  obtain ⟨_, excludeFrame, excludeAuthority, excludeVisible⟩ := phaseEffect excluded
  obtain ⟨stored, restored, restoreAuthority, restoreVisible⟩ := phaseEffect installed
  have first : (oldInstalled).activeFirst = (before).writer.wal.active.first :=
    valid.retained.resumed.keeper.trans valid.retained.active
  have selectedKeeper : keeperPath = (dir).file (.walSegment (before).writer.wal.active.first) :=
    congrArg (dir).file (congrArg DiskFile.walSegment first)
  have keeperLive : ∀ inode, (observe current.reached).visible keeperPath = some inode →
      (inodes current.reached).visible inode = (before).writer.wal.active.bytes := by
    simpa only [observedStorage, RunDirectoryInodeView.storageObservation, selectedKeeper] using entryKeeper
  have selectedPath : (before).crashPath keeperPath :=
    NativeReadyState.crashPath_iff_write.mpr (.inr (.inl selectedKeeper))
  obtain ⟨keeperInode, keeperBound, _⟩ := old.keeper
  rw [← selectedKeeper] at keeperBound
  have atGuard := ((guardFrame.visible keeperPath selectedPath).1).trans keeperBound
  have atPoison := ((excludeFrame.visible keeperPath selectedPath).1).trans atGuard
  have keeperAtPoison := (excludeVisible keeperInode atGuard).trans
    ((guardVisible keeperInode keeperBound).trans (keeperLive keeperInode keeperBound))
  let count := (oldInstalled).walBytes + WAL.frameSize * request.rows.length
  have frameId (entry : heap) : view.framesWrite before cache.directory storage entry entry :=
    ⟨rfl, .refl _ _⟩
  have frameTrans {entry mid after : heap}
      (first : view.framesWrite before cache.directory storage entry mid)
      (last : view.framesWrite before cache.directory storage mid after) :
      view.framesWrite before cache.directory storage entry after :=
    ⟨last.1.trans first.1, first.2.trans last.2⟩
  have committedFrame := commitBytesAt_frames (view.framesWrite before cache.directory storage) frameId frameTrans dir
    (oldInstalled).activeFirst (WAL.encodeBatch batch) count append stage sync rename
    poisoned (appendFrame poisoned) stageFrame groupFrame renameFrame rootFrame
  rw [committed] at committedFrame
  have authority := restoreAuthority.trans (committedFrame.1.trans (excludeAuthority.trans guardAuthority))
  have startFrame := (guardFrame.trans excludeFrame).weaken
    (scope := (before).writeFramePath) fun _ kept => NativeReadyState.crashPath_iff_write.mpr (.inr (.inr kept))
  obtain ⟨appended, staged, grouped, renamed, issued, directoryHandle, wrote, stagedMarker, filesSynced, moved,
    loadedRoot, syncedRoot⟩ := syncer.publicationReturned cache appender stager rename committed
  obtain ⟨keeperGrouped, markerGrouped, keeperName, keeperBytesAtGroup, _⟩ := syncer.groupedStorageFromPublication
    cache view appender stager inodes observe inode buffered atPoison keeperAtPoison wrote stagedMarker filesSynced
    (appendEffects wrote atPoison) (fun named => stageEffects named stagedMarker) (barrierEffects filesSynced)
  obtain ⟨target, rootBound, loadedFiles, loadVisible⟩ := loadEffect loadedRoot
  have issuedRoot := (loadedFiles (dir).path (.inl rfl)).1.trans rootBound
  rw [← target.inode] at issuedRoot
  obtain ⟨syncedFiles, syncVisible, crashNonempty, crashSettled⟩ := syncEffect syncedRoot target.live issuedRoot
  obtain ⟨renamedFiles, renameVisible⟩ := renameFiles moved
  obtain ⟨keeper, marker, _, settledNames⟩ := syncer.publishedStorage cache view rename storage moved loadedRoot syncedRoot
    target rootBound keeperGrouped markerGrouped (stagedPrivate moved)
    (fun renamed inode named _ => renameEffect renamed inode named) (fun _ => renamedFiles) (fun _ => loadedFiles)
    (fun _ _ _ => ⟨syncedFiles, crashNonempty, crashSettled⟩)
  have separate : keeperPath ≠ (dir).file .stagedWalBoundary ∧ keeperPath ≠ (dir).file .walBoundary := by
    constructor <;> intro equal <;>
      obtain ⟨_, collision⟩ := DiskDirectory.walSegment_exclusive equal.symm <;> cases collision
  have child : keeperPath = (dir).path ∨ ∃ file, keeperPath = (dir).file file := .inr ⟨_, rfl⟩
  have renameName := (renamedFiles _ separate).1
  have loadName := (loadedFiles _ child).1
  have syncName := (syncedFiles _ child).1
  have exactKeeper := syncer.publishedKeeperVisible cache rename opened.set
    (fun heap => (observe heap).visible) (fun heap => (inodes heap).visible)
    keeperName keeperBytesAtGroup moved loadedRoot syncedRoot installed
    (fun _ => ⟨renameName, renameVisible _ keeperName⟩)
    (fun _ => ⟨loadName, loadVisible _ (renameName.trans keeperName)⟩)
    (fun _ => ⟨syncName, syncVisible _ (loadName.trans (renameName.trans keeperName))⟩)
    (fun _ => ⟨(restored.visible _ selectedPath).1,
      restoreVisible _ (syncName.trans (loadName.trans (renameName.trans keeperName)))⟩)
  rw [first] at keeper settledNames
  have commitFrame := startFrame.trans committedFrame.2
  let custody := NativePendingWriteCensus.ofRawAuthority view cache valid entryCensus entryCache authority
    old.toNativeReadyProtectedStorage root (commitFrame.trans
      (restored.weaken fun _ kept => NativeReadyState.crashPath_iff_write.mpr (.inr (.inr kept)))).visible
  let nextInstalled : Installed := { oldInstalled with table, walBytes := count }
  let keeperBytes := (before).writer.wal.active.bytes ++ WAL.encodeBatch batch
  let markerBytes := WAL.Boundary.encode count.toUInt64
  let written := WAL.Boundary.WriteFiles.ofPublishedPayloads (before).writer.wal.active.bytes keeperBytes markerBytes
  obtain ⟨target, selected, _, nextKeeper, retained⟩ :=
    valid.retained.advancePublished prepared fits (keeperBytes := keeperBytes) (markerBytes := markerBytes) rfl rfl
  let writer := (before).writer.afterAppend nextInstalled batch written target
  let state := (before).afterWrite writer (view.cacheAt reached cache.directory cache.active cache.pending) custody
  have stateReady : state.Valid :=
    ⟨rfl, valid.owner, custody.ownerLive, custody.directoryLive, ⟨custody.cachedAt, custody.cachedDirectory⟩, retained⟩
  have extended : writer.history = current.current.history ++ batch := congrArg (· ++ batch) history
  let position := current.current.ready.afterAcknowledgedWrite state stateReady extended
  let next : NativeOpenedPosition opened :=
    ⟨⟨current.current.history ++ batch, current.current.submissions ++ [.acknowledgedBatch batch], position⟩,
      reached, current.directory, stored, current.pins⟩
  have sameManifest : writer.target.pair.manifest = (before).writer.target.pair.manifest := by
    change target.pair.manifest = _
    rw [selected]
  have afterStorage : NativeReadyStorage state (storage reached) := by
    apply old.afterPublishedWrite (writer := writer) custody sameManifest rfl rfl rfl
      commitFrame restored
    · rw [nextKeeper]
      exact keeper
    · rw [← retained.resumed.bytes]
      exact marker
    · exact fun names member => ⟨(settledNames names member).1, (settledNames names member).2.1⟩
  have ledger : current.current.LedgerSuffix [.acknowledged request batch] next.current := by
    refine ⟨?_, rfl, ?_, ?_⟩
    · simp [next, NativeExecutionEvent.writes]
    · simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, NativeExecutionEvent.reads]
        using (show next.current.ready.reads = current.current.ready.reads from rfl)
    · intro event member
      obtain rfl := List.mem_singleton.mp member
      trivial
  refine ⟨current.uses.writeSchedules, batch, table, next, rfl, prepared, number, rfl, rfl, ledger, ?_, ?_⟩
  · refine ⟨rfl, rfl, afterStorage, ?_, ?_⟩
    · intro namedInode named
      change (observe reached).visible ((dir).file (.walSegment (before).writer.wal.active.first)) = some namedInode at named
      rw [← selectedKeeper] at named
      obtain rfl := Option.some.inj (named.symm.trans exactKeeper.1)
      exact exactKeeper.2.trans nextKeeper.symm
    · intro literal found
      have cached := custody.cachedDirectory
      change (view.directory reached cache.directory).map (view.handle reached) =
        some (custody.cachedAt, (before).directorySlot, 0) at cached
      rw [found] at cached
      rw [Option.some.inj cached, custody.directoryInode]
      exact afterStorage.directoryBound
  · exact (before).writer.wal.appendSelectedView_starts writer.wal.directory.active writer.history

end RawWrite

/-- A particular observed success and the local laws of its callbacks.
The storage view is a projection of the same observation at every heap. -/
def NativeOpenedPosition.ObservesPublishedWrite
    {heap image : Type} {opened : NativeOpenedHandle heap} (start : NativeOpenedPosition opened)
    (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap) (syncer : RawSyncCalls heap)
    (view : OpenCloseHeapView heap image)
    (cache : OpenSyncCacheRefs opened.files start.current.ready.state.session.directory.path)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : heap → CheckpointStorageObservation)
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
    (request : WriteRequest) (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) (sequence : UInt64) (reached : heap) : Prop :=
  let dir := start.current.ready.state.session.directory
  ∃ files : ∀ atHeap, RunDirectoryInodeView dir (inodes atHeap) (runs atHeap),
    (∀ atHeap, (files atHeap).storageObservation = observe atHeap) ∧
    request.runOnRawOpenPhase dir lookup (appender.run cache.active) (stager.run cache.pending)
      (syncer.group dir.path cache.directory cache.active cache.pending)
      rename opened.phase opened.get opened.set start.reached = .ok sequence reached ∧
    (∀ {batch table}, prepareBatch start.current.ready.state.writer.installed.table request.rows = some (batch, table) →
      start.PublishedWriteEffects appender stager syncer view cache inodes runs files
        inode buffered request lookup rename batch)

/-- Interpret the successful source return from the shared physical
observation. The next writer uses that same observation and cache. When
the reached callbacks frame canonical names, it also keeps the incoming
WAL namespace guarantee for any prospective next write. -/
theorem NativeOpenedPosition.acknowledgesObservedWrite
    {heap image : Type} {opened : NativeOpenedHandle heap} (start : NativeOpenedPosition opened)
    (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap) (syncer : RawSyncCalls heap)
    (view : OpenCloseHeapView heap image)
    (cache : OpenSyncCacheRefs opened.files start.current.ready.state.session.directory.path)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : heap → CheckpointStorageObservation)
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
    (request : WriteRequest) (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) {sequence : UInt64} {reached : heap}
    (nonempty : request.rows ≠ [])
    (entry : start.WriteStorageEntry view cache (observe start.reached) (inodes start.reached).visible)
    (seen : start.ObservesPublishedWrite appender stager syncer view cache inodes runs observe
      inode buffered request lookup rename sequence reached) :
    let directory := start.current.ready.state.session.directory
    opened.table.UsesOpenWriteSchedules directory opened.files opened.phase ∧
    request.runOnRawOpenPhase directory lookup (appender.run cache.active) (stager.run cache.pending)
      (syncer.group directory.path cache.directory cache.active cache.pending)
      rename opened.phase opened.get opened.set start.reached = .ok sequence reached ∧
    ∃ (batch : List WAL.Write) (table : PackedTable) (next : NativeOpenedPosition opened)
      (sameDirectory : next.current.ready.state.session.directory = directory),
      prepareBatch start.current.ready.state.writer.installed.table request.rows = some (batch, table) ∧
      sequence = table.committed ∧ next.reached = reached ∧ next.pins = start.pins ∧
      start.current.LedgerSuffix [.acknowledged request batch] next.current ∧
      next.WriteStorageEntry view
        ⟨cache.directory, cache.active, cache.pending, cache.references,
          (congrArg DiskDirectory.path sameDirectory).symm ▸ cache.atRoot⟩
        (observe next.reached) (inodes next.reached).visible ∧
      ∀ {firstOffset through : Nat},
        (∀ offset ∈ start.current.ready.state.writer.wal.segments.map WalSegment.first, firstOffset ≤ offset) →
        start.current.ready.state.writer.wal.SettledNamespaceWindow directory firstOffset through (observe start.reached) →
        start.WalNameEffects appender stager syncer cache request lookup rename observe firstOffset through →
        (∀ {settled value}, opened.set opened.phase (.ready value) settled = .ok () reached →
          WalNamePresenceFrame directory firstOffset through (observe settled) (observe reached)) →
        (∀ offset ∈ next.current.ready.state.writer.wal.segments.map WalSegment.first, firstOffset ≤ offset) ∧
        next.current.ready.state.writer.wal.SettledNamespaceWindow
          next.current.ready.state.session.directory firstOffset through (observe next.reached) := by
  obtain ⟨files, sameStorage, returned, effects⟩ := seen
  have atWrite : start.WriteStorageEntry view cache
      (files start.reached).storageObservation (inodes start.reached).visible := by
    rw [sameStorage start.reached]
    exact entry

  obtain ⟨schedule, batch, table, next, sameDirectory, prepared, committed, nextHeap, pins, ledger, physical, sameStarts⟩ :=
    start.acknowledgesPublishedWrite appender stager syncer view cache inodes runs files inode buffered
      request lookup rename nonempty returned atWrite effects
  refine ⟨schedule, returned, batch, table, next, sameDirectory, prepared, committed, nextHeap, pins, ledger, ?_, ?_⟩
  · rwa [← sameStorage next.reached]
  · intro firstOffset through covers initial nameEffects restore
    refine ⟨sameStarts.symm ▸ covers, ?_⟩
    have framed := start.preservesWalNamesAfterAcknowledgement appender stager syncer cache request lookup rename
      nonempty returned nameEffects restore
    obtain ⟨live, crash⟩ := framed.preservesNamespaceWindow initial
    rw [sameDirectory, nextHeap]
    exact ⟨fun offset low high => sameStarts.symm ▸ live offset low high,
      fun names survives offset low high => sameStarts.symm ▸ crash names survives offset low high⟩

end Alvoki.Storage.DiskSession
