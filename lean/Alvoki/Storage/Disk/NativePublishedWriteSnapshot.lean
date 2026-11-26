import Alvoki.Storage.Disk.NativeReadyWriteStorage
import Alvoki.Storage.Disk.NativeOpenSnapshotTrace
import Alvoki.Storage.Disk.NativeSourceLedger

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)
open Sequential (SnapshotTable)

/-- The acknowledged batch and a subsequent snapshot are observations on
one table. The write's reached position supplies the phase and token that
the snapshot calls actually use. -/
theorem NativeOpenedPosition.acknowledgesAndReadsLatest
    {heap image : Type} {opened : NativeOpenedHandle heap} (current : NativeOpenedPosition opened)
    (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap) (syncer : RawSyncCalls heap)
    (view : OpenCloseHeapView heap image)
    (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : heap → CheckpointStorageObservation)
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
    (request : WriteRequest) (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {sequence : UInt64} {reached : heap}
    (nonempty : request.rows ≠ [])
    (entry : current.WriteStorageEntry view cache (observe current.reached) (inodes current.reached).visible)
    (seen : current.ObservesPublishedWrite appender stager syncer view cache inodes runs observe
      inode buffered request lookup rename sequence reached)
    (read : SnapshotReadRequest α)
    (token : ∀ (written : NativeOpenedPosition opened), written.reached = reached →
      ∀ {event after}, (NativeOpenedReport.acquire (start := written)).Reached event after →
        opened.ptrEq opened.token opened.token after.reached = .ok true after.reached) :
    let directory := current.current.ready.state.session.directory
    opened.table.UsesOpenWriteSchedules directory opened.files opened.phase ∧
    request.runOnRawOpenPhase directory lookup (appender.run cache.active) (stager.run cache.pending)
      (syncer.group directory.path cache.directory cache.active cache.pending)
      rename opened.phase opened.get opened.set current.reached = .ok sequence reached ∧
    ∃ (batch : List WAL.Write) (table : PackedTable) (written last : NativeOpenedPosition opened) (reference : SnapshotTable UInt64)
      (events : List NativeExecutionEvent),
      prepareBatch current.current.ready.state.writer.installed.table request.rows = some (batch, table) ∧
      sequence = table.committed ∧ written.reached = reached ∧
      NativeOpenedTrace written [.acquire, .readAt written.pins.length read] events last ∧
      current.current.LedgerSuffix (.acknowledged request batch :: events) last.current ∧
      SnapshotWalReplay .empty (current.current.history ++ batch) reference ∧
      (∀ observation ∈ last.current.ready.reads, observation.agrees reference) := by
  obtain ⟨schedule, returned, batch, table, written, _, prepared, number, reachedWrite, _, wrote, _⟩ :=
    current.acknowledgesObservedWrite appender stager syncer view cache inodes runs observe inode buffered
      request lookup rename nonempty entry seen
  obtain ⟨pin, acquired, last, reference, issued, compared, acquireReturned, readReturned, calls, _, replay, agrees⟩ :=
    written.acquiresAndReadsLatest read (token written reachedWrite)
  have history : written.current.history = current.current.history ++ batch := by
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, NativeExecutionEvent.writes] using wrote.history
  exact ⟨schedule, returned, batch, table, written, last, reference, _, prepared, number, reachedWrite, calls,
    wrote.append calls.common.ledgerSuffix, history ▸ replay, agrees⟩

/-- The snapshot uses the returned handle's own token at the heap
reached by its acquire call. -/
def NativeOpenedHandle.ObservesSnapshotToken {heap : Type}
    (opened : NativeOpenedHandle heap) (writeHeap : heap) : Prop :=
  ∀ (written : NativeOpenedPosition opened), written.reached = writeHeap →
    ∀ {event after}, (NativeOpenedReport.acquire (start := written)).Reached event after →
      opened.ptrEq opened.token opened.token after.reached = .ok true after.reached

/-- Compose the old-target open ledger with the actual observed write
and reads on its returned handle. The next-call assumptions describe
the return and physical effects at the native callbacks. -/
theorem NativeReadPosition.SelectedWritePlan.acknowledgesAndReadsAfterOldTarget
    {heap stream : Type} {input : FilePath} {view : OpenCloseHeapView heap FileImage}
    {history : List WAL.Write} {log : List DatabaseSubmissions}
    {current : NativeReadPosition history log} {batch : List WAL.Write}
    {source : RawMarkedOpenInterpreter heap stream} {entry : heap} {inventory : DescriptorInventory}
    {vacant : TryLockObserves (view.files entry).owners current.state.session.directory (.ok true)}
    {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
    (plan : current.SelectedWritePlan batch current.state.writer.target (view.files entry).image)
    {opening : MarkedReadyOpenObservations input current.state.session.directory inventory (view.files entry) plan.layout
      current.state.writer.published vacant plan.selected}
    {raw : RawHealthyMarkedOpenEffects opening view source.calls source.init entry phaseIdentity tokenIdentity
      source.allocatePhase source.allocateToken stream source.remove source.stage source.rename}
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    {observe : heap → CheckpointStorageObservation}
    (first : WriteRequest) (cause : IO.Error)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (ready : raw.ReadyWriterReturn (log ++ [.uncertainBatch batch]) current.reads
      (fun _ => source.openTable input entry) get set observe (fun heap => (inodes heap).visible))
    (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap) (syncer : RawSyncCalls heap)
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
    (request : WriteRequest) (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (sequence : UInt64) (writeHeap : heap) (nonempty : request.rows ≠ [])
    (read : SnapshotReadRequest α)
    (nextCall : ∀ (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle)
      (cache : OpenSyncCacheRefs handle.files start.current.ready.state.session.directory.path),
      source.openTable input entry = .ok handle.table start.reached →
      start.current.history = history →
      start.WriteStorageEntry view cache (observe start.reached) (inodes start.reached).visible →
      start.ObservesPublishedWrite appender stager syncer view cache inodes runs observe
        inode buffered request lookup rename sequence writeHeap ∧ handle.ObservesSnapshotToken writeHeap) :
    ∃ (handle : NativeOpenedHandle heap) (start written last : NativeOpenedPosition handle)
      (cache : OpenSyncCacheRefs handle.files start.current.ready.state.session.directory.path)
      (writtenBatch : List WAL.Write) (events : List NativeExecutionEvent) (reference : SnapshotTable UInt64),
      let dir := start.current.ready.state.session.directory
      source.openTable input entry = .ok handle.table start.reached ∧
      handle.table.UsesOpenWriteSchedules dir handle.files handle.phase ∧
      request.runOnRawOpenPhase dir lookup (appender.run cache.active) (stager.run cache.pending)
        (syncer.group dir.path cache.directory cache.active cache.pending)
        rename handle.phase handle.get handle.set start.reached = .ok sequence writeHeap ∧
      written.reached = writeHeap ∧
      NativeOpenedTrace written [.acquire, .readAt written.pins.length read] events last ∧
      (⟨history, log, current⟩ : NativeExecutionPosition).LedgerSuffix
        (.uncertainWriteCrashRecovered first input cause batch [] :: .acknowledged request writtenBatch :: events)
        last.current ∧
      SnapshotWalReplay .empty (history ++ writtenBatch) reference ∧
      (∀ observation ∈ last.current.ready.reads, observation.agrees reference) := by
  obtain ⟨handle, start, cache, retained, returned, selected, recovered, _, physical⟩ :=
    plan.ledgerAtReadyWriter ready first cause
  have old := selected.trans plan.oldHistory
  have appended : start.current.history = history ++ retained := by
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, NativeExecutionEvent.writes] using recovered.history
  have omitted : retained = [] := List.append_cancel_left (by
    simpa only [List.append_nil] using appended.symm.trans old)
  obtain ⟨write, token⟩ := nextCall handle start cache returned old physical
  obtain ⟨schedules, writeReturn, writtenBatch, _, written, last, reference, events, _, _, reachedWrite, snapshots,
    wrote, replay, agrees⟩ :=
    start.acknowledgesAndReadsLatest appender stager syncer view cache inodes runs observe inode buffered
      request lookup rename nonempty physical write read token
  have ledger := recovered.append wrote
  rw [omitted] at ledger
  exact ⟨handle, start, written, last, cache, writtenBatch, events, reference, returned, schedules,
    writeReturn, reachedWrite, snapshots, ledger, old ▸ replay, agrees⟩

end Alvoki.Storage.DiskSession
