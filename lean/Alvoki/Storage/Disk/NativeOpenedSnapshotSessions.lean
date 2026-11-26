import Alvoki.Storage.Disk.NativeOpenSnapshotTrace
import Alvoki.Storage.Disk.NativeOpenedRestartSessions

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open Sequential (SnapshotPin SnapshotTable)

variable {heap : Type} {view : OpenCloseHeapView heap FileImage}
  {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}

/-- After the reported run fsync or first directory fsync interruption, the
same raw returned table acquires a fresh pin and reads at its latest
sequence. The token comparison is reported at the heap reached by that
acquisition. The recorded response agrees with the replay of the history
before the checkpoint, including a successful lookup of a missing key. -/
theorem NativeOpenedSessionTrace.stopsCheckpointEarlyAndReadsLatest
    (prior : NativeOpenedSessionTrace view names bytes start actions events before)
    (seen : NativeOpenedEarlyCheckpointReport before.position input view names bytes)
    (request : SnapshotReadRequest α)
    (compareIssuedToken : ∀ {handle : NativeOpenedHandle heap} {opened : NativeOpenedPosition handle}, seen.Returned opened →
      handle.ObservesSnapshotToken opened.reached) :
    ∃ (reached : NativeOpenedSessionPoint heap) (pin : NativeOpenedPin reached.handle)
      (acquired last : NativeOpenedPosition reached.handle)
      (reference : SnapshotTable UInt64)
      (issued : acquired.pins[reached.position.pins.length]? = some pin)
      (sameToken : reached.handle.ptrEq reached.handle.token reached.handle.token acquired.reached = .ok true acquired.reached),
      let sequence := reached.position.current.ready.state.writer.installed.table.committed
      let acquireEvent := NativeExecutionEvent.snapshotControl .acquire
        (.ok (reached.position.current.ready.state.session.sessionRef, pin.localPin))
      let value := request.replay reference sequence
      let readEvent := NativeExecutionEvent.snapshotHandleRead acquired.current.ready.state.session.sessionRef
        pin.localPin.handle request (some value) (request.record sequence value)
      seen.Returned reached.position ∧
      (NativeOpenedReport.acquire (start := reached.position)).Returns acquireEvent acquired ∧
      (NativeOpenedReport.readAt reached.position.pins.length request pin issued sameToken).Returns readEvent last ∧
      NativeOpenedSessionTrace view names bytes start
        (actions ++ [.stoppedCheckpointEarlyReboot seen.recovery.stage input,
          .calls [.acquire, .readAt reached.position.pins.length request]])
        (events ++ [seen.event, acquireEvent, readEvent]) ⟨reached.handle, last⟩ ∧
      last.current.ready.reads = before.position.current.ready.reads ++ [request.record sequence value] ∧
      SnapshotWalReplay .empty before.position.current.history reference ∧
      (∀ read ∈ last.current.ready.reads, read.agrees reference) := by
  obtain ⟨handle, opened, returned⟩ := seen.reaches
  let reached : NativeOpenedSessionPoint heap := ⟨handle, opened⟩
  obtain ⟨issuer⟩ := handle.hasLatestIssuer
  obtain ⟨pin, acquired, last, reference, issued, compared, acquireReturned, readReturned, calls, reads, wal, agrees, _⟩ :=
    opened.acquiresAndReadsLatest issuer rfl request (compareIssuedToken returned)
  have reopened : NativeOpenedSessionTrace view names bytes start _ _ reached :=
    .step prior (.stoppedCheckpointEarly seen returned)
  have continued := NativeOpenedSessionTrace.step reopened (.calls calls)
  have noChanges : seen.event.writes = [] ∧ seen.event.reads = [] := by
    unfold NativeOpenedEarlyCheckpointReport.event
    cases seen.recovery <;> exact ⟨rfl, rfl⟩
  obtain ⟨oldHistory, _, oldReads⟩ := returned.common.ledgers
  rw [noChanges.1, List.append_nil] at oldHistory
  rw [noChanges.2, List.append_nil] at oldReads
  refine ⟨reached, pin, acquired, last, reference, issued, compared, returned, acquireReturned, readReturned,
    ?_, reads.trans (congrArg (· ++ [_]) oldReads), ?_, agrees⟩
  · simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using continued
  · exact oldHistory ▸ wal

end Alvoki.Storage.DiskSession
