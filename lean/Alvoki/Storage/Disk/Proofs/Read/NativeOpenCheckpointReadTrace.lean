import Alvoki.Storage.Disk.NativeOpenCheckpoint
import Alvoki.Storage.Disk.Proofs.Read.NativeOpenReadTrace

namespace Alvoki.Storage.DiskSession

open System
open Sequential (SnapshotPin)

/-- Use the writer already justified by the raw return for the standard
checkpoint edge and its reached ready position. -/
theorem NativeExecutionPosition.checkpointAtWriter (start : NativeExecutionPosition)
    {image : Type} {attempt : SegmentedCheckpointReport start.ready.state.session.directory start.ready.state.writer}
    {reports : CheckpointCompletionReports (CensusDirectoryCache × image) attempt}
    (observed : NativeReadyCheckpoint start.ready.state reports) (writer : SegmentedWriterState)
    (completed : observed.Completed writer) (history : writer.history = start.history) :
    ∃ next : NativeReadPosition start.history start.submissions,
      NativeExecutionStep start .checkpoint ⟨start.history, start.submissions, next⟩ ∧
      next.state = observed.next writer ∧ next.reads = start.ready.reads :=
  ⟨_, .checkpoint start observed writer completed history, rfl, rfl⟩

/-- The successful public checkpoint supplies the actual returned heap
and the exact writer of the common trace edge. Acquire the next pin
from that heap and follow the issued token into a lookup or range read. -/
theorem NativeExecutionPosition.checkpointsThenReadsOpenPin {heap α image : Type}
    (start : NativeExecutionPosition) (db : DiskTable)
    {lock : IO.FS.Handle} {files : DiskTable.OpenSyncFiles} {phase : IO.Ref (Phase Installed)} {token : IO.Ref Unit}
    (uses : db.UsesOpenReferences start.ready.state.session.directory lock files phase token)
    {contents : heap → IO.Ref (Phase Installed) → Option (Phase Installed)}
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects contents get set) {entry : heap}
    (stored : contents entry phase = some start.ready.state.session.phase)
    {attempt : SegmentedCheckpointReport start.ready.state.session.directory start.ready.state.writer}
    {reports : CheckpointCompletionReports (CensusDirectoryCache × image) attempt}
    (observed : NativeReadyCheckpoint start.ready.state reports)
    {snapshot : UInt64} {pin : SnapshotPin} {table : PackedTable}
    (acquired : attempt.prepared.table.acquireAt snapshot = some (pin, table))
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)
    (compared : ∀ reached, ptrEq token token reached = .ok true reached)
    (request : SnapshotReadRequest α) :
    db.UsesOpenCheckpointSchedule start.ready.state.session.directory files phase ∧
    ∃ (writer : SegmentedWriterState) (checkpointed : NativeReadPosition start.history start.submissions)
      (afterCheckpoint : heap),
      observed.Completed writer ∧ checkpointed.state = observed.next writer ∧ checkpointed.reads = start.ready.reads ∧
      db.UsesOpenReferences checkpointed.state.session.directory lock files phase token ∧
      observed.ReturnsOnOpenPhase phase get set entry afterCheckpoint ∧
      contents afterCheckpoint phase = some checkpointed.state.session.phase ∧
      ∃ (issue : SnapshotPin → DiskSnapshotPin) (afterRead : heap) (response : Option α)
        (recorded : RecordedSnapshotRead) (last : NativeReadPosition start.history start.submissions),
        (issue pin).UsesOpenToken token pin ∧
        db.acquireAt snapshot =
          acquireSnapshotWith (m := IO) (do (← phase.get).installed) phase.set issue snapshot ∧
        acquireSnapshotWith (m := EStateM IO.Error heap) (do (← get phase).installed) (set phase)
          issue snapshot afterCheckpoint = .ok (some (issue pin)) afterRead ∧
        (match request with
          | .lookup key => db.lookup (issue pin).handle key = readSnapshotWith (m := IO)
              (do (← phase.get).installed) (token.ptrEq token) (fun table => table.lookup pin.handle key)
          | .range lo hi => db.range (issue pin).handle lo hi = readSnapshotWith (m := IO)
              (do (← phase.get).installed) (token.ptrEq token) (fun table => table.range pin.handle lo hi)) ∧
        readSnapshotWith (m := EStateM IO.Error heap) (do (← get phase).installed) (ptrEq token token)
          (request.read pin.handle) afterRead = .ok response afterRead ∧
        contents afterRead phase = some last.state.session.phase ∧
        NativeExecutionTrace start
          [.checkpoint,
            .snapshotControl (.acquireAt snapshot) (.ok (some (checkpointed.state.session.sessionRef, pin))),
            .snapshotHandleRead checkpointed.state.session.sessionRef pin.handle request response recorded]
          ⟨start.history, start.submissions, last⟩ ∧
        InstalledClientReplay start.submissions last.reads start.history last.state.writer.installed last.state.session := by
  obtain ⟨source, writer, _, afterCheckpoint, _, _, _, _, storedAfter, raw, completed, history, sameRefs, _⟩ :=
    start.ready.checkpointsViaOpenReferences db uses effects stored observed
  obtain ⟨checkpointed, checkpointStep, sameState, priorReads⟩ :=
    start.checkpointAtWriter observed writer completed history
  let reached : NativeExecutionPosition := ⟨start.history, start.submissions, checkpointed⟩
  have afterPhase : contents afterCheckpoint phase = some checkpointed.state.session.phase := sameState.symm ▸ storedAfter
  have carries : db.UsesOpenReferences checkpointed.state.session.directory lock files phase token := sameState.symm ▸ sameRefs
  have acquire : reached.ready.state.writer.installed.table.acquireAt snapshot = some (pin, table) := by
    change checkpointed.state.writer.installed.table.acquireAt snapshot = some (pin, table)
    rw [sameState]
    exact completed.installed.symm ▸ acquired
  obtain ⟨issue, afterRead, response, recorded, last, pinToken, acquireSource, actualAcquire, readSource,
    actualRead, afterReadPhase, trace, replay⟩ :=
    reached.acquiresAndReadsOpenPin db carries effects afterPhase acquire ptrEq compared request
  exact ⟨source, writer, checkpointed, afterCheckpoint, completed, sameState, priorReads, carries, raw, afterPhase,
    issue, afterRead, response, recorded, last, pinToken, acquireSource, actualAcquire, readSource, actualRead,
    afterReadPhase, trace.prepend checkpointStep, replay⟩

end Alvoki.Storage.DiskSession
