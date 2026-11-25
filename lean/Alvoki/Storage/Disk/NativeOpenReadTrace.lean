import Alvoki.Storage.Disk.NativeOpenAcquire
import Alvoki.Storage.Disk.NativeOpenPinRead
import Alvoki.Storage.Disk.NativeExecutionTrace

namespace Alvoki.Storage.DiskSession

open System
open Sequential (SnapshotPin)

/-- Start acquisition with the reached phase cell, then use the exact
issued pin and the resulting heap for the public lookup or range.
The two reported calls produce the corresponding common trace. -/
theorem NativeExecutionPosition.acquiresAndReadsOpenPin {heap α : Type}
    (start : NativeExecutionPosition) (db : DiskTable)
    {lock : IO.FS.Handle} {files : DiskTable.OpenSyncFiles} {phase : IO.Ref (Phase Installed)} {token : IO.Ref Unit}
    (uses : db.UsesOpenReferences start.ready.state.session.directory lock files phase token)
    {contents : heap → IO.Ref (Phase Installed) → Option (Phase Installed)}
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects contents get set) {before : heap}
    (stored : contents before phase = some start.ready.state.session.phase)
    {snapshot : UInt64} {pin : SnapshotPin} {table : PackedTable}
    (acquired : start.ready.state.writer.installed.table.acquireAt snapshot = some (pin, table))
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)
    (compared : ∀ reached, ptrEq token token reached = .ok true reached)
    (request : SnapshotReadRequest α) :
    ∃ (issue : SnapshotPin → DiskSnapshotPin) (after : heap) (response : Option α)
      (recorded : RecordedSnapshotRead) (last : NativeReadPosition start.history start.submissions),
      (issue pin).UsesOpenToken token pin ∧
      db.acquireAt snapshot =
        acquireSnapshotWith (m := IO) (do (← phase.get).installed) phase.set issue snapshot ∧
      acquireSnapshotWith (m := EStateM IO.Error heap) (do (← get phase).installed) (set phase)
        issue snapshot before = .ok (some (issue pin)) after ∧
      (match request with
        | .lookup key => db.lookup (issue pin).handle key = readSnapshotWith (m := IO)
            (do (← phase.get).installed) (token.ptrEq token) (fun table => table.lookup pin.handle key)
        | .range lo hi => db.range (issue pin).handle lo hi = readSnapshotWith (m := IO)
            (do (← phase.get).installed) (token.ptrEq token) (fun table => table.range pin.handle lo hi)) ∧
      readSnapshotWith (m := EStateM IO.Error heap) (do (← get phase).installed) (ptrEq token token)
        (request.read pin.handle) after = .ok response after ∧
      contents after phase = some last.state.session.phase ∧
      NativeExecutionTrace start
        [.snapshotControl (.acquireAt snapshot) (.ok (some (start.ready.state.session.sessionRef, pin))),
          .snapshotHandleRead start.ready.state.session.sessionRef pin.handle request response recorded]
        ⟨start.history, start.submissions, last⟩ ∧
      InstalledClientReplay start.submissions last.reads start.history last.state.writer.installed last.state.session := by
  obtain ⟨issue, reached, result, after, tokenKept, source, control, returned, executed, contentsAfter, _⟩ :=
    start.ready.acquiresViaOpenReferences db uses effects stored snapshot
  have valid := start.ready.readPrefix.refines.1
  have resultExact := (EStateM.Result.ok.inj (returned.symm.trans (valid.acquireReturns acquired))).1
  subst result
  have reachedState := control.reached
  simp only [NativeSnapshotUpdateObservation.update, SnapshotUpdate.outcome, valid.phase, acquired] at reachedState
  have sameDirectory : reached.state.session.directory = start.ready.state.session.directory := by
    rw [reachedState]
    rfl
  have carries : db.UsesOpenReferences reached.state.session.directory lock files phase token :=
    sameDirectory.symm ▸ uses
  obtain ⟨readSource, response, recorded, last, read, readExecuted, replay⟩ :=
    reached.readsOpenPin db carries (tokenKept pin)
      (fun value => effects.reads after phase value) contentsAfter ptrEq (compared after) request
  have first := NativeExecutionStep.snapshotControl start (.acquireAt snapshot) reached control
  simp only [NativeSnapshotUpdateObservation.update, SnapshotUpdate.outcome, valid.phase, acquired] at first
  have second := NativeExecutionStep.snapshotHandleRead ⟨start.history, start.submissions, reached⟩
    ⟨pin.handle, reached.state.session.sessionRef, true, by simp⟩ request response recorded last read
  change NativeExecutionStep ⟨start.history, start.submissions, reached⟩
    (.snapshotHandleRead reached.state.session.sessionRef pin.handle request response recorded)
    ⟨start.history, start.submissions, last⟩ at second
  rw [control.sessionRef] at second
  refine ⟨issue, after, response, recorded, last, tokenKept pin, source, executed, ?_, readExecuted,
    read.state.symm ▸ contentsAfter, .step (.step .empty first) second, replay⟩
  cases request <;> exact readSource

end Alvoki.Storage.DiskSession
