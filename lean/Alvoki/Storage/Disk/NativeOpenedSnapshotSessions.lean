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
      ∀ {event after}, (NativeOpenedReport.acquire (start := opened)).Reached event after →
        handle.ptrEq handle.token handle.token after.reached = .ok true after.reached) :
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
  obtain ⟨acquireEvent, acquired, atAcquired⟩ := (NativeOpenedReport.acquire (start := reached.position)).reaches
  have compared := compareIssuedToken returned atAcquired
  obtain ⟨_, pin, table, _, _, _, _, _, registered, pinState, _, _, active, event, pins, priorHistory, _, priorReads⟩ :=
    atAcquired.returned
  subst acquireEvent
  have issued : acquired.pins[reached.position.pins.length]? = some pin := by simp [pins]
  have found : acquired.current.ready.state.writer.installed.table.pins.find pin.localPin.handle = some pin.localPin := by
    rw [pinState]
    exact table.pins.find_of_mem active
  let observation : NativeSnapshotHandleObservation acquired.current.ready.state.session :=
    ⟨pin.localPin.handle, acquired.current.ready.state.session.sessionRef, true, by simp⟩
  obtain ⟨source, response, recorded, next, read, raw, replay⟩ :=
    acquired.current.ready.readsOpenPin reached.handle.table acquired.uses pin.issued
      (fun value => reached.handle.phaseEffects.reads acquired.reached reached.handle.phase value)
      acquired.stored reached.handle.ptrEq compared request
  have positive : response.isSome = true := by
    cases response with
    | none =>
      have denied := (request.handleDenied_iff _ _).mp read.result.returned
      simp [NativeSnapshotHandleObservation.reader, ObservedSnapshotReader.guard,
        SnapshotReadGuard.rejects, found] at denied
    | some => rfl
  obtain ⟨value, rfl⟩ := Option.isSome_iff_exists.mp positive
  obtain ⟨selected, foundSelected, readRecord⟩ := read.result.records
  have samePin : selected = pin.localPin := Option.some.inj (foundSelected.symm.trans found)
  subst selected
  have sequence := (PackedTable.acquireAt_spec registered).sequence
  rw [sequence] at readRecord
  subst recorded
  obtain ⟨reference, wal, _, _, _, agrees, _⟩ := replay
  have agreesRead := agrees (request.record reached.position.current.ready.state.writer.installed.table.committed value)
    (by rw [read.reads]; simp)
  have replayValue : value = request.replay reference reached.position.current.ready.state.writer.installed.table.committed := by
    cases request <;> exact agreesRead
  subst value
  let last : NativeOpenedPosition reached.handle :=
    ⟨⟨acquired.current.history, acquired.current.submissions, next⟩, acquired.reached,
      read.state.symm ▸ acquired.directory, read.state.symm ▸ acquired.stored, acquired.pins⟩
  let readReport := NativeOpenedReport.readAt reached.position.pins.length request pin issued compared
  let sequence := reached.position.current.ready.state.writer.installed.table.committed
  let value := request.replay reference sequence
  let readEvent := NativeExecutionEvent.snapshotHandleRead acquired.current.ready.state.session.sessionRef
    pin.localPin.handle request (some value) (request.record sequence value)
  have atRead : readReport.Reached readEvent last := by
    refine ⟨NativeExecutionStep.snapshotHandleRead acquired.current observation request _ _ next read, ?_, _, _, raw, rfl, rfl, rfl⟩
    cases request <;> exact source
  have calls := NativeOpenedTrace.step (NativeOpenedTrace.step .empty .acquire atAcquired) readReport atRead
  have reopened : NativeOpenedSessionTrace view names bytes start _ _ reached :=
    .step prior (.stoppedCheckpointEarly seen returned)
  have continued := NativeOpenedSessionTrace.step reopened (.calls calls)
  have noChanges : seen.event.writes = [] ∧ seen.event.reads = [] := by
    unfold NativeOpenedEarlyCheckpointReport.event
    cases seen.recovery <;> exact ⟨rfl, rfl⟩
  obtain ⟨oldHistory, _, oldReads⟩ := returned.common.ledgers
  rw [noChanges.1, List.append_nil] at oldHistory
  rw [noChanges.2, List.append_nil] at oldReads
  refine ⟨reached, pin, acquired, last, reference, issued, compared, returned, atAcquired.returned, atRead.returned,
    ?_, read.reads.trans (congrArg (· ++ [_]) (priorReads.trans oldReads)), ?_, agrees⟩
  · simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using continued
  · exact (priorHistory.trans oldHistory) ▸ wal

/-- Derive finite snapshot and run rewrite blocks at their reached
tables. Reopen steps retain their own local survivor or close reports,
so each later block starts at the exact new table and phase heap. -/
theorem NativeOpenedSessionTrace.executesSnapshotsAndRewrites
    (start : NativeOpenedSessionPoint heap) (actions : List NativeOpenedSessionAction)
    (observe : ∀ completed events reached action remaining,
      actions = completed ++ action :: remaining →
      NativeOpenedSessionTrace view names bytes start completed events reached →
      match action with
      | .calls instructions => NativeOpenedTrace.SnapshotAndRewriteOperands reached.position instructions
      | .quietRestart input => Nonempty (NativeQuietRestartReport reached input view names bytes)
      | .closeAndReopen input => Nonempty (NativeOpenedAlignedCloseReport reached.position input view)
      | .stoppedCheckpointEarlyReboot stage input => ∃ (report : NativeOpenedEarlyCheckpointReport reached.position input view names bytes),
          report.recovery.stage = stage
      | .processExitAndReopen _ | .closeRetriesAndReopen _ _ | .checkpointRenameReboot _ | .stoppedCheckpointReboot _
      | .uncertainWriteReboot _ _ | .uncertainWriteExitAndReopen _ _
      | .stoppedWalWriteReboot _ _ | .stoppedFirstAppendExit _ _
      | .stoppedFirstAppendExitRetries _ _ _ | .stoppedFirstAppendContendedRetries _ _ _ _ | .stoppedObsoleteRunUnlink _ _ => False) :
    ∃ events next, NativeOpenedSessionTrace view names bytes start actions events next ∧
      NativeExecutionTrace start.position.current events next.position.current ∧
      InstalledClientReplay next.position.current.submissions next.position.current.ready.reads next.position.current.history
        next.position.current.ready.state.writer.installed next.position.current.ready.state.session := by
  apply executes start actions
  intro completed events reached action remaining ordered prior
  have seen := observe completed events reached action remaining ordered prior
  cases action with
  | calls instructions =>
    exact ⟨.calls instructions (NativeOpenedTrace.reportsSnapshotsAndRewrites seen)⟩
  | quietRestart input =>
    obtain ⟨reported⟩ := seen
    exact ⟨.quiet input reported⟩
  | closeAndReopen input =>
    obtain ⟨reported⟩ := seen
    exact ⟨.close input reported⟩
  | stoppedCheckpointEarlyReboot stage input =>
    obtain ⟨reported, rfl⟩ := seen
    exact ⟨.stoppedCheckpointEarly input reported⟩
  | processExitAndReopen _ | closeRetriesAndReopen _ _ | checkpointRenameReboot _ | stoppedCheckpointReboot _
  | uncertainWriteReboot _ _ | uncertainWriteExitAndReopen _ _
  | stoppedWalWriteReboot _ _ | stoppedFirstAppendExit _ _
  | stoppedFirstAppendExitRetries _ _ _ | stoppedFirstAppendContendedRetries _ _ _ _ | stoppedObsoleteRunUnlink _ _ => exact False.elim seen

end Alvoki.Storage.DiskSession
