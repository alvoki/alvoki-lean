import Alvoki.Storage.Disk.NativeClassifiedWriteAck
import Alvoki.Storage.Disk.NativeRawWriteCustody
import Alvoki.Storage.Disk.NativeOpenedPosition
import Alvoki.Storage.Disk.NativeWalFileFsyncEffects

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WalSegmentCommit SyncHandleRouting

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

/-- A WAL primitive may change its own files and descriptors. Its
authority and other selected file observations have independent frames. -/
def OpenCloseHeapView.framesWrite {heap image : Type} (view : OpenCloseHeapView heap image) (state : NativeReadyState)
    (directoryRef : IO.Ref (Option IO.FS.Handle)) (storage : heap → CheckpointStorageObservation)
    (first last : heap) : Prop :=
  view.writeAuthorityAt state directoryRef last = view.writeAuthorityAt state directoryRef first ∧
    (storage first).Frames state.writeFramePath (storage last)

section RawWrite

variable {heap image : Type} {opened : NativeOpenedHandle heap}
  (current : NativeOpenedPosition opened)
  (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap) (syncer : RawSyncCalls heap)
  (view : OpenCloseHeapView heap image)
  (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)

local notation "before" => current.current.ready.state
local notation "dir" => current.current.ready.state.session.directory
local notation "oldInstalled" => current.current.ready.state.writer.installed
local notation "append" => appender.run cache.active
local notation "stage" => stager.run cache.pending
local notation "sync" => syncer.group current.current.ready.state.session.directory.path cache.directory cache.active cache.pending

/-- One acknowledged raw call supplies the next retained writer and its
prior read ledger. The committed storage is observed at the last
publication barrier, and the original phase setter carries it to the
actual returned heap. Only the prepared request and its selected
payloads enter the logical writer proof. -/
theorem NativeOpenedPosition.acknowledgesPublishedWrite
    (request : WriteRequest)
    (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {batch : List WAL.Write} {table : PackedTable} {sequence : UInt64} {reached : heap}
    (nonempty : request.rows ≠ [])
    (prepared : prepareBatch (oldInstalled).table request.rows = some (batch, table))
    (fits : (oldInstalled).walBytes + WAL.frameSize * request.rows.length < UInt64.size)
    (returned : request.runOnRawOpenPhase dir lookup append stage sync rename
      opened.phase opened.get opened.set current.reached = .ok sequence reached)
    (entryCensus : view.descriptors current.reached = (before).census)
    (entryCache : view.cacheAt current.reached cache.directory cache.active cache.pending = (before).cache)
    (storage : heap → CheckpointStorageObservation) (old : NativeReadyStorage before (storage current.reached))
    (root : ∀ literal, view.directory current.reached cache.directory = some literal →
      (storage current.reached).files.names (dir).path = some ((view.handle current.reached literal).1.inode
        (view.handle current.reached literal).2.1.description))
    (guardEffect : ∀ {after}, checkActiveSegmentWith dir oldInstalled lookup current.reached = .ok () after →
      (storage current.reached).Frames (before).crashPath (storage after) ∧
        view.writeAuthorityAt before cache.directory after = view.writeAuthorityAt before cache.directory current.reached)
    (phaseEffect : ∀ {value entry after}, opened.set opened.phase value entry = .ok () after →
      opened.contents after opened.phase = some value ∧ (storage entry).Frames (before).crashPath (storage after) ∧
        view.writeAuthorityAt before cache.directory after = view.writeAuthorityAt before cache.directory entry)
    (appendFrame : let frame := view.framesWrite before cache.directory storage
      ∀ entry, frame entry (reachedState (append ((dir).file (.walSegment (oldInstalled).activeFirst))
        (WAL.encodeBatch batch) entry)))
    (stageFrame : let frame := view.framesWrite before cache.directory storage
      ∀ entry, frame entry (reachedState (stage ((dir).file .stagedWalBoundary)
        (WAL.Boundary.encode ((oldInstalled).walBytes + WAL.frameSize * request.rows.length).toUInt64) entry)))
    (groupFrame : let frame := view.framesWrite before cache.directory storage
      ∀ entry, frame entry (reachedState (sync
        #[(dir).file (.walSegment (oldInstalled).activeFirst), (dir).file .stagedWalBoundary] entry)))
    (renameFrame : let frame := view.framesWrite before cache.directory storage
      ∀ entry, frame entry (reachedState (rename ((dir).file .stagedWalBoundary) ((dir).file .walBoundary) entry)))
    (rootFrame : let frame := view.framesWrite before cache.directory storage
      ∀ entry, frame entry (reachedState (sync #[(dir).path] entry)))
    (groupPayloads : let first := (oldInstalled).activeFirst
      let bytes := WAL.encodeBatch batch
      let mark := WAL.Boundary.encode ((oldInstalled).walBytes + WAL.frameSize * request.rows.length).toUInt64
      ∀ {entry appended staged grouped},
        append ((dir).file (.walSegment first)) bytes entry = .ok () appended →
        stage ((dir).file .stagedWalBoundary) mark appended = .ok () staged →
        sync #[ (dir).file (.walSegment first), (dir).file .stagedWalBoundary ] staged = .ok () grouped →
        (storage grouped).files.Stored ((dir).file (.walSegment first)) ((before).writer.wal.active.bytes ++ bytes) ∧
        (storage grouped).files.Stored ((dir).file .stagedWalBoundary) mark)
    (renameEffect : ∀ {entry after}, rename ((dir).file .stagedWalBoundary) ((dir).file .walBoundary) entry = .ok () after →
      ∀ inode, (storage entry).files.names ((dir).file .stagedWalBoundary) = some inode →
        (storage after).files.names ((dir).file .walBoundary) = some inode ∧
        (storage after).files.names ((dir).file .stagedWalBoundary) = none ∧
        (storage after).files.bytes inode = (storage entry).files.bytes inode)
    (stagedPrivate : ∀ {entry after}, rename ((dir).file .stagedWalBoundary) ((dir).file .walBoundary) entry = .ok () after →
      ∀ inode, (storage entry).files.names ((dir).file .stagedWalBoundary) = some inode →
        (storage entry).files.names ((dir).file .walBoundary) ≠ some inode)
    (renameFiles : ∀ {entry after}, rename ((dir).file .stagedWalBoundary) ((dir).file .walBoundary) entry = .ok () after →
      (storage entry).files.Frames (fun path => path ≠ (dir).file .stagedWalBoundary ∧ path ≠ (dir).file .walBoundary)
        (storage after).files)
    (loadEffect : ∀ {entry after handle}, syncer.readDirectory cache.directory entry = .ok (some handle) after →
      RawFsyncTarget view entry after handle ∧
      (storage entry).files.names (dir).path = some ((view.handle entry handle).1.inode
        (view.handle entry handle).2.1.description) ∧
      (storage entry).files.Frames (fun path => path = (dir).path ∨ ∃ file, path = (dir).file file)
        (storage after).files)
    (syncEffect : ∀ {issued after handle}, syncer.fsync handle issued = .ok () after →
      (view.handle issued handle).2.1 ∈ (view.descriptors issued).slots →
      (storage issued).files.names (dir).path = some ((view.descriptors issued).inode (view.handle issued handle).2.1.description) →
      (storage issued).files.Frames (fun path => path = (dir).path ∨ ∃ file, path = (dir).file file)
        (storage after).files ∧ (storage after).crashNames ≠ [] ∧
      ∀ names ∈ (storage after).crashNames, ∀ file, names ((dir).file file) = (storage after).files.names ((dir).file file)) :
    opened.table.UsesOpenWriteSchedules dir opened.files opened.phase ∧ sequence = table.committed ∧
    ∃ next : NativeOpenedPosition opened,
      next.reached = reached ∧ next.pins = current.pins ∧
      next.current.history = current.current.history ++ batch ∧
      next.current.submissions = current.current.submissions ++ [.acknowledgedBatch batch] ∧
      next.current.ready.reads = current.current.ready.reads ∧
      next.current.ready.state.census = view.descriptors reached ∧
      next.current.ready.state.cache = view.cacheAt reached cache.directory cache.active cache.pending ∧
      NativeReadyStorage next.current.ready.state (storage reached) := by
  obtain ⟨valid, history, _⟩ := current.current.ready.readPrefix.refines
  have loaded := opened.phaseEffects.reads current.reached opened.phase _ (current.stored.trans (congrArg some valid.phase))
  obtain ⟨guarded, poisoned, settled, guard, excluded, committed, installed, number, _, _⟩ :=
    request.runOnRawOpenPhase_acknowledges dir lookup append stage sync rename opened.phase opened.get opened.set
      loaded nonempty prepared fits returned
  obtain ⟨guardFrame, guardAuthority⟩ := guardEffect guard
  obtain ⟨_, excludeFrame, excludeAuthority⟩ := phaseEffect excluded
  obtain ⟨stored, restored, restoreAuthority⟩ := phaseEffect installed
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
    appendFrame stageFrame groupFrame renameFrame rootFrame poisoned
  rw [committed] at committedFrame
  have authority := restoreAuthority.trans (committedFrame.1.trans (excludeAuthority.trans guardAuthority))
  have startFrame := (guardFrame.trans excludeFrame).weaken
    (scope := (before).writeFramePath) fun _ kept => NativeReadyState.crashPath_iff_write.mpr (.inr (.inr kept))
  obtain ⟨appended, staged, grouped, renamed, issued, directoryHandle, wrote, stagedMarker, filesSynced, moved,
    loadedRoot, syncedRoot⟩ := syncer.publicationReturned cache appender stager rename committed
  obtain ⟨keeperGrouped, markerGrouped⟩ := groupPayloads wrote stagedMarker filesSynced
  obtain ⟨target, rootBound, loadedFiles⟩ := loadEffect loadedRoot
  obtain ⟨keeper, marker, _, settledNames⟩ := syncer.publishedStorage cache view rename storage moved loadedRoot syncedRoot
    target rootBound keeperGrouped markerGrouped (stagedPrivate moved)
    (fun renamed inode named _ => renameEffect renamed inode named) renameFiles (fun _ => loadedFiles) syncEffect
  have first : (oldInstalled).activeFirst = (before).writer.wal.active.first :=
    valid.retained.resumed.keeper.trans valid.retained.active
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
  exact ⟨current.uses.writeSchedules, number, next, rfl, rfl, rfl, rfl, rfl, rfl, rfl, afterStorage⟩

end RawWrite

end Alvoki.Storage.DiskSession
