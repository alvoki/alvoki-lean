import Alvoki.Storage.Disk.NativeClassifiedWriteAck
import Alvoki.Storage.Disk.NativeRawWriteCustody
import Alvoki.Storage.Disk.NativeOpenedPosition

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

section RawWrite

variable {heap image : Type} {opened : NativeOpenedHandle heap}
  (current : NativeOpenedPosition opened)

local notation "before" => current.current.ready.state
local notation "dir" => current.current.ready.state.session.directory
local notation "oldInstalled" => current.current.ready.state.writer.installed

/-- One acknowledged raw call supplies the next retained writer and its
prior read ledger. The committed storage is observed at the last
publication barrier, and the original phase setter carries it to the
actual returned heap. Only the prepared request and its selected
payloads enter the logical writer proof. -/
theorem NativeOpenedPosition.acknowledgesPublishedWrite
    (request : WriteRequest)
    (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (append stage : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {batch : List WAL.Write} {table : PackedTable} {sequence : UInt64} {reached : heap}
    (nonempty : request.rows ≠ [])
    (prepared : prepareBatch (oldInstalled).table request.rows = some (batch, table))
    (fits : (oldInstalled).walBytes + WAL.frameSize * request.rows.length < UInt64.size)
    (returned : request.runOnRawOpenPhase dir lookup append stage sync rename
      opened.phase opened.get opened.set current.reached = .ok sequence reached)
    (view : OpenCloseHeapView heap image) (cache : OpenSyncCacheRefs opened.files (dir).path)
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
    (appendAuthority : let authority := view.writeAuthorityAt before cache.directory
      ∀ entry, authority (reachedState (append ((dir).file (.walSegment (oldInstalled).activeFirst))
        (WAL.encodeBatch batch) entry)) = authority entry)
    (stageAuthority : let authority := view.writeAuthorityAt before cache.directory
      ∀ entry, authority (reachedState (stage ((dir).file .stagedWalBoundary)
        (WAL.Boundary.encode ((oldInstalled).walBytes + WAL.frameSize * request.rows.length).toUInt64) entry)) = authority entry)
    (groupAuthority : let authority := view.writeAuthorityAt before cache.directory
      ∀ entry, authority (reachedState (sync
        #[(dir).file (.walSegment (oldInstalled).activeFirst), (dir).file .stagedWalBoundary] entry)) = authority entry)
    (renameAuthority : let authority := view.writeAuthorityAt before cache.directory
      ∀ entry, authority (reachedState (rename ((dir).file .stagedWalBoundary) ((dir).file .walBoundary) entry)) = authority entry)
    (rootAuthority : let authority := view.writeAuthorityAt before cache.directory
      ∀ entry, authority (reachedState (sync #[(dir).path] entry)) = authority entry)
    (published : ∀ {entry after}, commitBytesAt dir (oldInstalled).activeFirst (WAL.encodeBatch batch)
      ((oldInstalled).walBytes + WAL.frameSize * request.rows.length) append stage sync rename entry = .ok () after →
      (storage entry).Frames (before).writeFramePath (storage after) ∧
      (storage after).files.Stored ((dir).file (.walSegment (before).writer.wal.active.first))
        ((before).writer.wal.active.bytes ++ WAL.encodeBatch batch) ∧
      (storage after).files.Stored ((dir).file .walBoundary)
        (WAL.Boundary.encode ((oldInstalled).walBytes + WAL.frameSize * request.rows.length).toUInt64) ∧
      ∀ names ∈ (storage after).crashNames,
        names ((dir).file (.walSegment (before).writer.wal.active.first)) =
          (storage after).files.names ((dir).file (.walSegment (before).writer.wal.active.first)) ∧
        names ((dir).file .walBoundary) = (storage after).files.names ((dir).file .walBoundary)) :
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
  have commitAuthority := commitBytesAt_keepsAuthority (view.writeAuthorityAt before cache.directory) dir
    (oldInstalled).activeFirst (WAL.encodeBatch batch) count append stage sync rename
    appendAuthority stageAuthority groupAuthority renameAuthority rootAuthority poisoned
  rw [committed] at commitAuthority
  have authority := restoreAuthority.trans (commitAuthority.trans (excludeAuthority.trans guardAuthority))
  have startFrame := (guardFrame.trans excludeFrame).weaken
    (scope := (before).writeFramePath) fun _ kept => NativeReadyState.crashPath_iff_write.mpr (.inr (.inr kept))
  obtain ⟨frame, keeper, marker, settledNames⟩ := published committed
  have commitFrame := startFrame.trans frame
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
    · exact settledNames
  exact ⟨current.uses.writeSchedules, number, next, rfl, rfl, rfl, rfl, rfl, rfl, rfl, afterStorage⟩

end RawWrite

end Alvoki.Storage.DiskSession
