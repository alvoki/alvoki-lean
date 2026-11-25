import Alvoki.Storage.Disk.NativeOpenReadyTrace

namespace Alvoki.Storage.DiskSession

open Sequential (SnapshotTable)

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- For a snapshot call, only the operand selection and the comparison
of the original live token need a report. The ready phase supplies the
guards, result and next state. -/
def NativeOpenedInstruction.SnapshotOperands (instruction : NativeOpenedInstruction)
    (start : NativeOpenedPosition opened) : Prop :=
  match instruction with
  | .acquire | .acquireAt _ | .advanceFloor _ => True
  | .releaseAt index | .readAt index _ =>
    index < start.pins.length ∧ opened.ptrEq opened.token opened.token start.reached = .ok true start.reached
  | .write _ | .checkpoint | .rotateWal | .rewriteRun _ | .readSupplied _ _ | .releaseSupplied _
  | .planWalCollection | .collectCoveredWal | .collectObsoleteRuns _ => False

theorem NativeOpenedInstruction.observesSnapshot
    (instruction : NativeOpenedInstruction) (start : NativeOpenedPosition opened)
    (operands : instruction.SnapshotOperands start) :
    Nonempty (NativeOpenedReport start instruction) := by
  cases instruction with
  | write | checkpoint | rotateWal | rewriteRun | readSupplied | releaseSupplied
  | planWalCollection | collectCoveredWal | collectObsoleteRuns _ => exact False.elim operands
  | acquire => exact ⟨.acquire⟩
  | acquireAt sequence =>
    cases acquired : start.current.ready.state.writer.installed.table.acquireAt sequence with
    | none => exact ⟨.acquireAtUnavailable sequence acquired⟩
    | some found =>
      obtain ⟨pin, table⟩ := found
      exact ⟨.acquireAt sequence acquired⟩
  | advanceFloor floor => exact ⟨.advanceFloor floor⟩
  | releaseAt index =>
    obtain ⟨inBounds, compared⟩ := operands
    let pin := start.pins[index]'inBounds
    exact ⟨.releaseAt index pin (List.getElem?_eq_getElem inBounds) compared⟩
  | readAt index request =>
    obtain ⟨inBounds, compared⟩ := operands
    let pin := start.pins[index]'inBounds
    exact ⟨.readAt index request pin (List.getElem?_eq_getElem inBounds) compared⟩

/-- A snapshot and run rewrite block needs only selected pin operands
and token comparisons at the reached reads and releases. -/
def NativeOpenedTrace.SnapshotAndRewriteOperands
    (start : NativeOpenedPosition opened) (instructions : List NativeOpenedInstruction) : Prop :=
  ∀ issued events reached instruction remaining,
    instructions = issued ++ instruction :: remaining →
    NativeOpenedTrace start issued events reached →
    match instruction with
    | .rewriteRun _ => True
    | instruction => instruction.SnapshotOperands reached

theorem NativeOpenedTrace.reportsSnapshotsAndRewrites
    {start : NativeOpenedPosition opened} {instructions : List NativeOpenedInstruction}
    (operands : SnapshotAndRewriteOperands start instructions) : Reports start instructions := by
  intro issued events reached instruction remaining ordered previous
  have reported := operands issued events reached instruction remaining ordered previous
  cases instruction with
  | rewriteRun request => exact ⟨.rewriteRun request⟩
  | _ => exact NativeOpenedInstruction.observesSnapshot _ reached reported

/-- Acquire and read on any reached ready table. Only the live-token
comparison at the heap reached by the acquire is supplied. -/
theorem NativeOpenedPosition.acquiresAndReadsLatest
    (start : NativeOpenedPosition opened)
    (request : SnapshotReadRequest α)
    (compareIssuedToken : ∀ {event after}, (NativeOpenedReport.acquire (start := start)).Reached event after →
      opened.ptrEq opened.token opened.token after.reached = .ok true after.reached) :
    ∃ (pin : NativeOpenedPin opened) (acquired last : NativeOpenedPosition opened)
      (reference : SnapshotTable UInt64)
      (issued : acquired.pins[start.pins.length]? = some pin)
      (sameToken : opened.ptrEq opened.token opened.token acquired.reached = .ok true acquired.reached),
      let sequence := start.current.ready.state.writer.installed.table.committed
      let acquireEvent := NativeExecutionEvent.snapshotControl .acquire
        (.ok (start.current.ready.state.session.sessionRef, pin.localPin))
      let value := request.replay reference sequence
      let readEvent := NativeExecutionEvent.snapshotHandleRead acquired.current.ready.state.session.sessionRef
        pin.localPin.handle request (some value) (request.record sequence value)
      (NativeOpenedReport.acquire (start := start)).Returns acquireEvent acquired ∧
      (NativeOpenedReport.readAt start.pins.length request pin issued sameToken).Returns readEvent last ∧
      NativeOpenedTrace start [.acquire, .readAt start.pins.length request] [acquireEvent, readEvent] last ∧
      last.current.ready.reads = start.current.ready.reads ++ [request.record sequence value] ∧
      SnapshotWalReplay .empty start.current.history reference ∧
      (∀ read ∈ last.current.ready.reads, read.agrees reference) := by
  obtain ⟨acquireEvent, acquired, atAcquired⟩ := (NativeOpenedReport.acquire (start := start)).reaches
  have compared := compareIssuedToken atAcquired
  obtain ⟨_, pin, table, _, _, _, _, _, registered, pinState, _, _, active, event, pins, priorHistory, _, priorReads⟩ :=
    atAcquired.returned
  subst acquireEvent
  have issued : acquired.pins[start.pins.length]? = some pin := by simp [pins]
  have found : acquired.current.ready.state.writer.installed.table.pins.find pin.localPin.handle = some pin.localPin := by
    rw [pinState]
    exact table.pins.find_of_mem active
  let observation : NativeSnapshotHandleObservation acquired.current.ready.state.session :=
    ⟨pin.localPin.handle, acquired.current.ready.state.session.sessionRef, true, by simp⟩
  obtain ⟨source, response, recorded, next, read, raw, replay⟩ :=
    acquired.current.ready.readsOpenPin opened.table acquired.uses pin.issued
      (fun value => opened.phaseEffects.reads acquired.reached opened.phase value)
      acquired.stored opened.ptrEq compared request
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
  have agreesRead := agrees (request.record start.current.ready.state.writer.installed.table.committed value)
    (by rw [read.reads]; simp)
  have replayValue : value = request.replay reference start.current.ready.state.writer.installed.table.committed := by
    cases request <;> exact agreesRead
  subst value
  let last : NativeOpenedPosition opened :=
    ⟨⟨acquired.current.history, acquired.current.submissions, next⟩, acquired.reached,
      read.state.symm ▸ acquired.directory, read.state.symm ▸ acquired.stored, acquired.pins⟩
  let readReport := NativeOpenedReport.readAt start.pins.length request pin issued compared
  let sequence := start.current.ready.state.writer.installed.table.committed
  let value := request.replay reference sequence
  let readEvent := NativeExecutionEvent.snapshotHandleRead acquired.current.ready.state.session.sessionRef
    pin.localPin.handle request (some value) (request.record sequence value)
  have atRead : readReport.Reached readEvent last := by
    refine ⟨NativeExecutionStep.snapshotHandleRead acquired.current observation request _ _ next read, ?_, _, _, raw, rfl, rfl, rfl⟩
    cases request <;> exact source
  have calls := NativeOpenedTrace.step (NativeOpenedTrace.step .empty .acquire atAcquired) readReport atRead
  exact ⟨pin, acquired, last, reference, issued, compared, atAcquired.returned, atRead.returned,
    calls, read.reads.trans (congrArg (· ++ [_]) priorReads), priorHistory ▸ wal, agrees⟩

end Alvoki.Storage.DiskSession
