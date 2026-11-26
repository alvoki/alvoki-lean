import Alvoki.Storage.Disk.NativeOpenReadyTrace

namespace Alvoki.Storage.DiskSession

open Sequential (SnapshotPin SnapshotTable)

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

abbrev NativeOpenedHandle.acquireLatestRaw {heap : Type} (opened : NativeOpenedHandle heap)
    (issue : SnapshotPin → DiskSnapshotPin) : EStateM IO.Error heap DiskSnapshotPin :=
  let load : EStateM IO.Error heap Installed := do (← opened.get opened.phase).installed
  acquireLatestWith load (acquireSnapshotWith load (opened.set opened.phase) issue)

abbrev NativeOpenedHandle.readPinRaw {heap : Type} (opened : NativeOpenedHandle heap)
    (pin : NativeOpenedPin opened) (request : SnapshotReadRequest α) :
    EStateM IO.Error heap (Option α) :=
  readSnapshotWith (do (← opened.get opened.phase).installed)
    (opened.ptrEq opened.token opened.token) (request.read pin.localPin.handle)

/-- The token comparison is observed after the actual acquisition call
on this handle's phase cell. -/
def NativeOpenedHandle.ObservesSnapshotToken {heap : Type}
    (opened : NativeOpenedHandle heap) (start : heap) : Prop :=
  ∀ (issue : SnapshotPin → DiskSnapshotPin),
    opened.table.acquire = acquireLatestWith (m := IO) (do (← opened.phase.get).installed)
      (acquireSnapshotWith (do (← opened.phase.get).installed) opened.phase.set issue) →
    ∀ {pin : DiskSnapshotPin} {reached : heap},
      opened.acquireLatestRaw issue start = .ok pin reached →
      opened.ptrEq opened.token opened.token reached = .ok true reached

/-- A present answer from the actual read identifies the successful
token comparison on its reached heap. The loaded phase and the presented
pin determine the same response in the client read step. -/
theorem NativeOpenedPosition.refinesReturnedPin
    (start : NativeOpenedPosition opened) (pin : NativeOpenedPin opened) (request : SnapshotReadRequest α)
    {value : α} {reached : heap}
    (returned : opened.readPinRaw pin request start.reached = .ok (some value) reached) :
    opened.ptrEq opened.token opened.token start.reached = .ok true reached ∧
    ∃ recorded next,
      NativeSnapshotHandleRead start.current.ready
        ⟨pin.localPin.handle, start.current.ready.state.session.sessionRef, true, by simp⟩
        request (some value) recorded next := by
  let current := start.current.ready
  have valid := current.readPrefix.refines.1
  have loaded := opened.phaseEffects.reads start.reached opened.phase current.state.session.phase start.stored
  simp only [NativeOpenedHandle.readPinRaw, readSnapshotWith, withLocalHandle, Bind.bind, EStateM.bind,
    loaded, valid.phase, Phase.installed, Pure.pure, EStateM.pure] at returned
  have read : opened.ptrEq opened.token opened.token start.reached = .ok true reached ∧
      request.read pin.localPin.handle current.state.writer.installed.table = some value := by
    cases compared : opened.ptrEq opened.token opened.token start.reached with
    | error cause atError =>
      simp [compared] at returned
    | ok localToken readHeap =>
      cases localToken <;> simp [compared, EStateM.pure] at returned ⊢
      exact ⟨returned.2, returned.1⟩
  refine ⟨read.1, ?_⟩
  let observation : NativeSnapshotHandleObservation current.state.session :=
    ⟨pin.localPin.handle, current.state.session.sessionRef, true, by simp⟩
  obtain ⟨response, recorded, next, modeled⟩ := current.readsHandle observation request
  have computed := (observation.reader valid).readResult (request.read pin.localPin.handle)
  have same : response = some value := by
    have equal := (EStateM.Result.ok.inj (modeled.result.returned.symm.trans computed)).1
    simpa only [observation, NativeSnapshotHandleObservation.reader, ↓reduceIte, read.2] using equal
  subst response
  exact ⟨recorded, next, modeled⟩

/-- Acquire and read on any reached ready table. Only the live-token
comparison at the heap reached by the acquire is supplied. -/
theorem NativeOpenedPosition.acquiresAndReadsLatest
    (start : NativeOpenedPosition opened)
    (request : SnapshotReadRequest α)
    (compareIssuedToken : opened.ObservesSnapshotToken start.reached) :
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
  obtain ⟨issue, pin, table, source, _, _, acquiredRaw, _, registered, pinState, _, _, active, event, pins,
    priorHistory, _, priorReads, _⟩ := atAcquired.returned
  have compared := compareIssuedToken issue source acquiredRaw
  subst acquireEvent
  have issued : acquired.pins[start.pins.length]? = some pin := by simp [pins]
  have found : acquired.current.ready.state.writer.installed.table.pins.find pin.localPin.handle = some pin.localPin := by
    rw [pinState]
    exact table.pins.find_of_mem active
  let observation : NativeSnapshotHandleObservation acquired.current.ready.state.session :=
    ⟨pin.localPin.handle, acquired.current.ready.state.session.sessionRef, true, by simp⟩
  let installed := acquired.current.ready.state.writer.installed
  have valid := acquired.current.ready.readPrefix.refines.1
  have loaded := opened.phaseEffects.reads acquired.reached opened.phase _ acquired.stored
  have raw : opened.readPinRaw pin request acquired.reached =
      .ok (request.read pin.localPin.handle installed.table) acquired.reached := by
    simp only [NativeOpenedHandle.readPinRaw, readSnapshotWith, withLocalHandle, Bind.bind, EStateM.bind,
      loaded, valid.phase, Phase.installed, Pure.pure, EStateM.pure, compared, ↓reduceIte, installed]
  have positive : (request.read pin.localPin.handle installed.table).isSome = true := by
    cases value : request.read pin.localPin.handle installed.table with
    | none =>
      dsimp only [installed] at value
      have returned := (observation.reader valid).readResult (request.read pin.localPin.handle)
      have missing : (observation.reader valid).session.runSnapshotRead (observation.reader valid).sameSession
          (request.read pin.localPin.handle) = .ok none (observation.reader valid).session := by
        simpa only [observation, NativeSnapshotHandleObservation.reader, ↓reduceIte, value] using returned
      have denied := (request.handleDenied_iff _ _).mp missing
      simp [observation, NativeSnapshotHandleObservation.reader, ObservedSnapshotReader.guard,
        SnapshotReadGuard.rejects, found] at denied
    | some => rfl
  obtain ⟨value, response⟩ := Option.isSome_iff_exists.mp positive
  rw [response] at raw
  obtain ⟨_, recorded, next, read⟩ := acquired.refinesReturnedPin pin request raw
  obtain ⟨selected, foundSelected, readRecord⟩ := read.result.records
  have samePin : selected = pin.localPin := Option.some.inj (foundSelected.symm.trans found)
  subst selected
  have sequence := (PackedTable.acquireAt_spec registered).sequence
  rw [sequence] at readRecord
  subst recorded
  obtain ⟨reference, wal, _, _, _, agrees, _⟩ := next.readPrefix.guardedReplay
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
    cases request with
    | lookup key => exact acquired.uses.lookupPin pin.issued key
    | range lo hi => exact acquired.uses.rangePin pin.issued lo hi
  have calls := NativeOpenedTrace.step (NativeOpenedTrace.step .empty .acquire atAcquired) readReport atRead
  exact ⟨pin, acquired, last, reference, issued, compared, atAcquired.returned, atRead.returned,
    calls, read.reads.trans (congrArg (· ++ [_]) priorReads), priorHistory ▸ wal, agrees⟩

end Alvoki.Storage.DiskSession
