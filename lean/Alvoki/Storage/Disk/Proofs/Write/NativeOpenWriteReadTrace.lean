import Alvoki.Storage.Disk.Proofs.Write.NativeOpenWrite
import Alvoki.Storage.Disk.NativeOpenReadTrace

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open Sequential (SnapshotPin)

/-- The same acknowledged write witness supplies the raw return and the
common trace edge. The following acquisition starts on its returned
heap and reads through the exact snapshot token it issues. -/
theorem NativeExecutionPosition.writesThenReadsOpenPin {heap α : Type}
    (start : NativeExecutionPosition) (db : DiskTable)
    {lock : IO.FS.Handle} {files : DiskTable.OpenSyncFiles} {phase : IO.Ref (Phase Installed)} {token : IO.Ref Unit}
    (uses : db.UsesOpenReferences start.ready.state.session.directory lock files phase token)
    {contents : heap → IO.Ref (Phase Installed) → Option (Phase Installed)}
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects contents get set) {entry : heap}
    (stored : contents entry phase = some start.ready.state.session.phase)
    {prepared : NativeReadyWritePreparation start.ready.state} (seen : NativeReadyWriteReport prepared)
    (write : WriteRequest) (rows : write.rows = prepared.rows)
    {snapshot : UInt64} {pin : SnapshotPin} {table : PackedTable}
    (acquired : seen.publication.nextInstalled.table.acquireAt snapshot = some (pin, table))
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)
    (compared : ∀ reached, ptrEq token token reached = .ok true reached)
    (request : SnapshotReadRequest α) :
    let history := start.history ++ prepared.batch
    let log := start.submissions ++ [.acknowledgedBatch prepared.batch]
    db.UsesOpenWriteSchedules start.ready.state.session.directory files phase ∧
    ∃ (written : NativeReadPosition history log) (afterWrite : heap) (target : Target),
      written.state = seen.next target ∧ written.reads = start.ready.reads ∧
      db.UsesOpenReferences written.state.session.directory lock files phase token ∧
      seen.ReturnsOnOpenPhase write phase get set entry afterWrite ∧
      contents afterWrite phase = some written.state.session.phase ∧
      ∃ (issue : SnapshotPin → DiskSnapshotPin) (afterRead : heap) (response : Option α)
        (recorded : RecordedSnapshotRead) (last : NativeReadPosition history log),
        (issue pin).UsesOpenToken token pin ∧
        db.acquireAt snapshot =
          acquireSnapshotWith (m := IO) (do (← phase.get).installed) phase.set issue snapshot ∧
        acquireSnapshotWith (m := EStateM IO.Error heap) (do (← get phase).installed) (set phase)
          issue snapshot afterWrite = .ok (some (issue pin)) afterRead ∧
        (match request with
          | .lookup key => db.lookup (issue pin).handle key = readSnapshotWith (m := IO)
              (do (← phase.get).installed) (token.ptrEq token) (fun table => table.lookup pin.handle key)
          | .range lo hi => db.range (issue pin).handle lo hi = readSnapshotWith (m := IO)
              (do (← phase.get).installed) (token.ptrEq token) (fun table => table.range pin.handle lo hi)) ∧
        readSnapshotWith (m := EStateM IO.Error heap) (do (← get phase).installed) (ptrEq token token)
          (request.read pin.handle) afterRead = .ok response afterRead ∧
        contents afterRead phase = some last.state.session.phase ∧
        NativeExecutionTrace start
          [.acknowledged write prepared.batch,
            .snapshotControl (.acquireAt snapshot) (.ok (some (written.state.session.sessionRef, pin))),
            .snapshotHandleRead written.state.session.sessionRef pin.handle request response recorded]
          ⟨history, log, last⟩ ∧
        InstalledClientReplay log last.reads history last.state.writer.installed last.state.session := by
  intro history log
  obtain ⟨source, _, afterWrite, target, written, _, _, _, _, afterPhase, rawWrite, returned, sameState, initial,
    seed, reads, sameRefs, _⟩ := start.ready.acknowledgesViaOpenReferences db uses effects stored seen write rows
  let reached : NativeExecutionPosition := ⟨history, log, written⟩
  have writeStep : NativeExecutionStep start (.acknowledged write prepared.batch) reached :=
    .acknowledged start seen write rows target written returned sameState initial seed reads
  have acquire : reached.ready.state.writer.installed.table.acquireAt snapshot = some (pin, table) := by
    change written.state.writer.installed.table.acquireAt snapshot = some (pin, table)
    rw [sameState]
    exact acquired
  obtain ⟨issue, afterRead, response, recorded, last, pinToken, acquireSource, actualAcquire, readSource,
    actualRead, afterReadPhase, trace, replay⟩ :=
    reached.acquiresAndReadsOpenPin db sameRefs effects afterPhase acquire ptrEq compared request
  exact ⟨source, written, afterWrite, target, sameState, reads, sameRefs, rawWrite, afterPhase, issue, afterRead, response,
    recorded, last, pinToken, acquireSource, actualAcquire, readSource, actualRead, afterReadPhase,
    trace.prepend writeStep, replay⟩

end Alvoki.Storage.DiskSession
