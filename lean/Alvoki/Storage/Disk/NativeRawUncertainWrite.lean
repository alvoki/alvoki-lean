import Alvoki.Storage.Disk.NativeOpenWrite
import Alvoki.Storage.Disk.NativeOpenedPosition
import Alvoki.Storage.Disk.NativeRawWriteCustody
import Alvoki.Storage.Disk.NativeWalStage

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentCommit WalSegmentRepair

/-- File callbacks preserve the original phase cell independently of
their WAL effects. Keep authority and the protected files through the
same reached-state frame as for an acknowledged write. -/
def NativeOpenedPosition.framesRawWrite {heap image : Type} {opened : NativeOpenedHandle heap}
    (current : NativeOpenedPosition opened) (view : OpenCloseHeapView heap image)
    (directoryRef : IO.Ref (Option IO.FS.Handle)) (storage : heap → CheckpointStorageObservation)
    (entry reached : heap) : Prop :=
  view.framesWrite current.current.ready.state directoryRef storage entry reached ∧
    opened.contents reached opened.phase = opened.contents entry opened.phase

section

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

/-- An ordinary uncertain write returns on the original opened phase
and cache. Follow the reached guard, poison assignment and failed
commit to obtain the still-held authority and the exact protected-file
frame. The returned heap can supply a later release or crash observation. -/
theorem NativeOpenedPosition.returnsCommitUnknown
    (request : WriteRequest)
    (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {cause : IO.Error} {reached : heap}
    (nonempty : request.rows ≠ [])
    (returned : request.runOnRawOpenPhase dir lookup append stage sync rename
      opened.phase opened.get opened.set current.reached = .error (.commitUnknown cause) reached)
    (entryCensus : view.descriptors current.reached = (before).census)
    (entryCache : view.cacheAt current.reached cache.directory cache.active cache.pending = (before).cache)
    (storage : heap → CheckpointStorageObservation)
    (old : NativeReadyProtectedStorage before (storage current.reached).files)
    (root : ∀ literal, view.directory current.reached cache.directory = some literal →
      (storage current.reached).files.names (dir).path = some ((view.handle current.reached literal).1.inode
        (view.handle current.reached literal).2.1.description))
    (guardFrame : ∀ {guarded}, checkActiveSegmentWith dir oldInstalled lookup current.reached = .ok () guarded →
      current.framesRawWrite view cache.directory storage current.reached guarded)
    (poisonFrame : ∀ {guarded poisoned}, opened.set opened.phase .poisoned guarded = .ok () poisoned →
      view.framesWrite before cache.directory storage guarded poisoned)
    (appendFrame : let frame := current.framesRawWrite view cache.directory storage
      ∀ batch table, prepareBatch (oldInstalled).table request.rows = some (batch, table) →
      ∀ entry, frame entry (reachedState (append ((dir).file (.walSegment (oldInstalled).activeFirst))
        (WAL.encodeBatch batch) entry)))
    (stageFrame : let frame := current.framesRawWrite view cache.directory storage
      ∀ entry, frame entry (reachedState (stage ((dir).file .stagedWalBoundary)
        (WAL.Boundary.encode ((oldInstalled).walBytes + WAL.frameSize * request.rows.length).toUInt64) entry)))
    (groupFrame : let frame := current.framesRawWrite view cache.directory storage
      ∀ entry, frame entry (reachedState (sync
        #[(dir).file (.walSegment (oldInstalled).activeFirst), (dir).file .stagedWalBoundary] entry)))
    (renameFrame : let frame := current.framesRawWrite view cache.directory storage
      ∀ entry, frame entry (reachedState (rename ((dir).file .stagedWalBoundary) ((dir).file .walBoundary) entry)))
    (rootFrame : let frame := current.framesRawWrite view cache.directory storage
      ∀ entry, frame entry (reachedState (sync #[(dir).path] entry))) :
    opened.table.UsesOpenWriteSchedules dir opened.files opened.phase ∧
    opened.contents reached opened.phase = some .poisoned ∧
    (storage current.reached).Frames (before).writeFramePath (storage reached) ∧
    (∃ custody : NativePendingWriteCensus before (view.cacheAt reached cache.directory cache.active cache.pending),
      custody.reached = view.descriptors reached ∧ custody.bindings = (storage reached).files.names) ∧
    ∃ batch table guarded poisoned,
      prepareBatch (oldInstalled).table request.rows = some (batch, table) ∧
      (oldInstalled).walBytes + WAL.frameSize * request.rows.length < UInt64.size ∧
      checkActiveSegmentWith dir oldInstalled lookup current.reached = .ok () guarded ∧
      opened.set opened.phase .poisoned guarded = .ok () poisoned ∧
      syncer.PublicationOutcome cache appender stager rename (oldInstalled).activeFirst
        ((oldInstalled).walBytes + WAL.frameSize * request.rows.length) (WAL.encodeBatch batch) poisoned
        (.error cause reached) := by
  have valid := current.current.ready.readPrefix.refines.1
  have loaded := opened.phaseEffects.reads current.reached opened.phase _ (current.stored.trans (congrArg some valid.phase))
  obtain ⟨batch, table, prepared, fits⟩ := request.runOnRawOpenPhase_prepared dir lookup
    append stage sync rename opened.phase opened.get opened.set loaded nonempty (by rw [returned]; trivial)
  obtain ⟨guarded, poisoned, guard, excluded, failed, _, _⟩ :=
    request.runOnRawOpenPhase_commitUnknown dir lookup append stage sync rename opened.phase opened.get opened.set
      loaded nonempty prepared fits returned
  have afterGuard := guardFrame guard
  have present := afterGuard.2.trans current.stored
  obtain ⟨actual, assigned, stored⟩ := opened.phaseEffects.writes guarded opened.phase _ .poisoned present
  have samePoisoned := (EStateM.Result.ok.inj (assigned.symm.trans excluded)).2
  have atPoisoned : opened.contents poisoned opened.phase = some .poisoned := samePoisoned ▸ stored
  let frame := current.framesRawWrite view cache.directory storage
  have frameId (entry : heap) : frame entry entry := ⟨⟨rfl, .refl _ _⟩, rfl⟩
  have frameTrans {entry mid after : heap} (first : frame entry mid) (last : frame mid after) : frame entry after :=
    ⟨⟨last.1.1.trans first.1.1, first.1.2.trans last.1.2⟩, last.2.trans first.2⟩
  have afterCommit := commitBytesAt_frames frame frameId frameTrans dir (oldInstalled).activeFirst
    (WAL.encodeBatch batch) ((oldInstalled).walBytes + WAL.frameSize * request.rows.length)
    append stage sync rename (appendFrame batch table prepared) stageFrame groupFrame renameFrame rootFrame poisoned
  rw [failed, reachedState] at afterCommit
  have afterPoison := poisonFrame excluded
  have authority := afterCommit.1.1.trans (afterPoison.1.trans afterGuard.1.1)
  have protectedFrame := afterGuard.1.2.trans (afterPoison.2.trans afterCommit.1.2)
  let custody := NativePendingWriteCensus.ofRawAuthority view cache valid entryCensus entryCache authority
    old root protectedFrame.visible
  have outcome := syncer.publicationOutcome cache appender stager rename (first := (oldInstalled).activeFirst)
    (count := (oldInstalled).walBytes + WAL.frameSize * request.rows.length) (bytes := WAL.encodeBatch batch) poisoned
  rw [failed] at outcome
  exact ⟨current.uses.writeSchedules, afterCommit.2.trans atPoisoned, protectedFrame, ⟨custody, rfl, rfl⟩,
    batch, table, guarded, poisoned, prepared, fits, guard, excluded, outcome⟩

end

/-- Read the marker and keeper from one namespace and inode-byte choice.
The checkpoint binding is supplied separately by the protected-file frame. -/
theorem NativeReadyState.selectsWriteWal {state : NativeReadyState} (valid : state.Valid)
    {batch : List WAL.Write} (fits : (WAL.encode (state.writer.history ++ batch)).size < UInt64.size)
    (names : FilePath → Option Nat) (contents : Nat → ByteArray) {marker keeper : Nat}
    (marked : names (state.session.directory.file .walBoundary) = some marker)
    (bound : names (state.session.directory.file (.walSegment state.writer.wal.active.first)) = some keeper)
    (selected :
      (contents marker = WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64 ∧
        ∃ tail, contents keeper = state.writer.wal.active.bytes ++ tail) ∨
      (contents marker = WAL.Boundary.encode (WAL.encode (state.writer.history ++ batch)).size.toUInt64 ∧
        contents keeper = state.writer.wal.active.bytes ++ WAL.encode batch)) :
    ∃ target, BatchRetryTarget state.writer.history batch state.writer.wal.active.first target ∧
      target.pair = ⟨state.writer.target.pair.manifest, (names (state.session.directory.file .walBoundary)).map contents⟩ ∧
      target.Accepts ((names (state.session.directory.file (.walSegment state.writer.wal.active.first))).map contents) := by
  have starts := valid.retained.layout.forward state.writer.wal.active (by simp [WalSegmentImage.segments])
  rw [valid.retained.layout.activeEnd] at starts
  rw [valid.retained.layout.activeBytes] at selected
  obtain ⟨history, allowed, markerBytes, keeperBytes⟩ := selectSegment_atBatchBoundary starts fits selected
  obtain ⟨checkpoint, covered, _⟩ := state.writer.target.pair.walRange_accounting state.writer.target.decoded
  have covers : state.writer.target.range.watermark ≤ state.writer.history.length :=
    valid.retained.resumed.through ▸ covered
  let pair : DirectoryPublication.Bindings :=
    ⟨state.writer.target.pair.manifest, (names (state.session.directory.file .walBoundary)).map contents⟩
  have markerCount : pair.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64) := by
    simp only [pair, marked, Option.map_some, markerBytes]
  obtain ⟨target, authorized, same, _, _, _, accepts⟩ :=
    BatchRetryTarget.ofSelected starts covers fits (pair := pair) checkpoint allowed markerCount keeperBytes
  exact ⟨target, authorized, same, by simpa only [bound, Option.map_some] using accepts⟩

end Alvoki.Storage.DiskSession
