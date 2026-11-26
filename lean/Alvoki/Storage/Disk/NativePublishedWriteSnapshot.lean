import Alvoki.Storage.Disk.NativeReadyWriteStorage
import Alvoki.Storage.Disk.NativeOpenSnapshotTrace

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

end Alvoki.Storage.DiskSession
