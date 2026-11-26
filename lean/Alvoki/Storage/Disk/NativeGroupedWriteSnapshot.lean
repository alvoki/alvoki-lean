import Alvoki.Storage.Disk.NativeGroupedWriteRecovery
import Alvoki.Storage.Disk.NativeAlignedWriteRecovery
import Alvoki.Storage.Disk.NativePublishedWriteSnapshot

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)
open Sequential (SnapshotTable)

section

variable {heap stream : Type} {opened : NativeOpenedHandle heap}
  (current : NativeOpenedPosition opened) (view : OpenCloseHeapView heap FileImage)
  (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)
  (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap) (syncer : RawSyncCalls heap)
  (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
  (observe : ∀ atHeap, RunDirectoryInodeView current.current.ready.state.session.directory (inodes atHeap) (runs atHeap))

local notation "ready" => current.current.ready
local notation "state" => current.current.ready.state
local notation "dir" => current.current.ready.state.session.directory
local notation "installed" => current.current.ready.state.writer.installed
local notation "storage" => fun atHeap => RunDirectoryInodeView.storageObservation (observe atHeap)
local notation "names" => fun atHeap => CheckpointSurvivingFiles.names (CheckpointStorageObservation.files (storage atHeap))
local notation "visible" => fun atHeap => WalInodeImage.visible (inodes atHeap)

/-- Interpret the reported group error and retry calls on the same physical
observation, then check the next observed write and snapshot on the table
returned by recovery. A different fault stage is classified separately. -/
theorem NativeOpenedPosition.groupedRetryAndReads
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
    (request : WriteRequest) (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {failed rebooted reached : heap} {cause : IO.Error}
    (nonempty : request.rows ≠ [])
    (returned : request.runOnRawOpenPhase dir lookup (appender.run cache.active) (stager.run cache.pending)
      (syncer.group (dir).path cache.directory cache.active cache.pending)
      rename opened.phase opened.get opened.set current.reached = .error (.commitUnknown cause) failed)
    (initial : NativeReadyStorage state (storage current.reached))
    (groupEffects : current.GroupedErrorEffects view cache appender stager syncer inodes observe inode buffered
      request lookup failed cause)
    (reboot : RawWriteRebootEntry state view storage names visible failed rebooted)
    (reset : reboot.DurableReset)
    (later : ∀ ordinal ∈ (view.files rebooted).image.later.visible, (state).writer.target.range.through < ordinal)
    (source : RawMarkedOpenInterpreter heap stream) {input : FilePath} {returns : List (FilePath × IO.Error)}
    (retry : ∃ attempts : source.FailedCalls rebooted returns reached,
      returns ≠ [] ∧
      RawOpenRetryTrace.SelectedEffects view source rebooted (state).writer.target
        (fun atHeap => ⟨names atHeap, fun inode => [visible atHeap inode]⟩) (state).selectedRetryPath
        (fun atHeap => RawOpenRetryTrace.KeeperAt view dir (state).writer.target names visible atHeap ∧
          (state).SelectedRetryDurability (state).writer.target (storage atHeap)) attempts)
    (vacant : TryLockObserves (view.files reached).owners dir (.ok true))
    (exactKeeper : (view.files reached).image.keeper.active = some (state).writer.target.trimmed)
    (noLater : (view.files reached).image.later.visible = [])
    {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
    (healthy : ∀ {batch table}, prepareBatch (installed).table request.rows = some (batch, table) →
      (ready).ObservesHealthyWriteRetry (input := input) (view := view) (batch := batch)
        (target := (state).writer.target) (reached := reached)
        (phaseIdentity := phaseIdentity) (tokenIdentity := tokenIdentity) source names vacant)
    (aligned : ∀ {batch table}, prepareBatch (installed).table request.rows = some (batch, table) →
      NativeReadPosition.AlignedRetryEffects (current := ready) (batch := batch) (target := (state).writer.target)
        (input := input) (view := view) (reached := reached) (vacant := vacant) (source := source)
        (phaseIdentity := phaseIdentity) (tokenIdentity := tokenIdentity) storage visible)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (phase : OpenPhaseCellEffects view.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)
    (nextRequest : WriteRequest) (nextSequence : UInt64) (writeHeap : heap) (nextNonempty : nextRequest.rows ≠ [])
    (read : SnapshotReadRequest α)
    (nextCall : ∀ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle)
      (nextCache : OpenSyncCacheRefs handle.files start.current.ready.state.session.directory.path),
      source.openTable input reached = .ok handle.table start.reached →
      start.current.history = current.current.history →
      start.WriteStorageEntry view nextCache (storage start.reached) (visible start.reached) →
      start.ObservesPublishedWrite appender stager syncer view nextCache inodes runs storage
        inode buffered nextRequest lookup rename nextSequence writeHeap ∧ handle.ObservesSnapshotToken writeHeap) :
    opened.table.UsesOpenWriteSchedules dir opened.files opened.phase ∧
    source.FailedCalls rebooted returns reached ∧ returns ≠ [] ∧
    ∃ batch table guarded poisoned,
      prepareBatch (installed).table request.rows = some (batch, table) ∧
      checkActiveSegmentWith dir installed lookup current.reached = .ok () guarded ∧
      opened.set opened.phase .poisoned guarded = .ok () poisoned ∧
      let keeperPath := (dir).file (.walSegment (installed).activeFirst)
      let staging := (dir).file .stagedWalBoundary
      let groupFailed := ∃ appended staged,
        appender.run cache.active keeperPath (WAL.encodeBatch batch) poisoned = .ok () appended ∧
        stager.run cache.pending staging
          (WAL.Boundary.encode ((installed).walBytes + WAL.frameSize * request.rows.length).toUInt64) appended =
            .ok () staged ∧
        syncer.group (dir).path cache.directory cache.active cache.pending #[keeperPath, staging] staged =
          .error cause failed
      ¬ groupFailed ∨
      (groupFailed ∧
        ∃ (handle : NativeOpenedHandle heap) (start written last : NativeOpenedPosition handle)
          (nextCache : OpenSyncCacheRefs handle.files start.current.ready.state.session.directory.path)
          (nextBatch : List WAL.Write) (events : List NativeExecutionEvent) (reference : SnapshotTable UInt64),
          let directory := start.current.ready.state.session.directory
          source.openTable input reached = .ok handle.table start.reached ∧
          handle.table.UsesOpenWriteSchedules directory handle.files handle.phase ∧
          nextRequest.runOnRawOpenPhase directory lookup (appender.run nextCache.active)
            (stager.run nextCache.pending)
            (syncer.group directory.path nextCache.directory nextCache.active nextCache.pending)
            rename handle.phase handle.get handle.set start.reached = .ok nextSequence writeHeap ∧
          written.reached = writeHeap ∧
          NativeOpenedTrace written [.acquire, .readAt written.pins.length read] events last ∧
          current.current.LedgerSuffix
            (.uncertainWriteCrashRecovered request input cause batch [] :: .acknowledged nextRequest nextBatch :: events)
            last.current ∧
          SnapshotWalReplay .empty (current.current.history ++ nextBatch) reference ∧
          (∀ observation ∈ last.current.ready.reads, observation.agrees reference)) := by
  obtain ⟨attempts, retried, retryEffects⟩ := retry
  obtain ⟨schedules, batch, table, guarded, poisoned, prepared, fits, guard, assigned, classified⟩ :=
    current.selectsAfterGroupedError view cache appender stager syncer inodes observe inode buffered request lookup rename
      nonempty returned initial groupEffects reboot later
  refine ⟨schedules, attempts, retried, batch, table, guarded, poisoned, prepared, guard, assigned, ?_⟩
  rcases classified with ⟨group, admitted, selected, _, _⟩ | elsewhere
  · refine .inr ⟨group, ?_⟩
    obtain ⟨plan, handle, start, nextCache, retained, opened, history, recoveredLedger, _, physical⟩ :=
      (ready).opensReadyAfterAlignedRetries storage visible request cause prepared fits admitted retryEffects selected
        (reboot.startsDurableRetry reset selected).2 exactKeeper noLater (healthy prepared) phase ptrEq (aligned prepared)
    have old := history.trans plan.oldHistory
    have appended : start.current.history = current.current.history ++ retained := by
      simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, NativeExecutionEvent.writes] using
        recoveredLedger.history
    have omitted : retained = [] := List.append_cancel_left (by
      simpa only [List.append_nil] using appended.symm.trans old)
    obtain ⟨write, token⟩ := nextCall handle start nextCache opened old physical
    obtain ⟨schedules, writeReturn, nextBatch, _, written, last, reference, events, _, _, reachedWrite, snapshots,
      wrote, replay, agrees⟩ :=
      start.acknowledgesAndReadsLatest appender stager syncer view nextCache inodes runs storage inode buffered
        nextRequest lookup rename recoveredLedger nextNonempty physical write read token
    rw [omitted] at wrote
    exact ⟨handle, start, written, last, nextCache, nextBatch, events, reference, opened, schedules,
      writeReturn, reachedWrite, snapshots, wrote, old ▸ replay, agrees⟩
  · exact .inl elsewhere

end

end Alvoki.Storage.DiskSession
