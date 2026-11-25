import Alvoki.Storage.Disk.NativeClassifiedCheckpointPreflight
import Alvoki.Storage.Disk.NativeClassifiedCheckpointSuccess
import Alvoki.Storage.Disk.NativeClassifiedWritePreflight
import Alvoki.Storage.Disk.NativeClassifiedWriteAck
import Alvoki.Storage.Disk.NativeOpenSnapshotControls

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open Sequential (SnapshotPin)

variable {heap : Type} {opened : NativeOpenedHandle heap}

inductive NativeOpenedInstruction : Type 1 where
  | write (request : WriteRequest)
  | checkpoint
  | acquireAt (sequence : UInt64)
  | releaseAt (index : Nat)
  | advanceFloor (floor : UInt64)
  | readAt (index : Nat) (request : SnapshotReadRequest α)

/-- Per-call observations at the reached position. Reads and releases
address issued pins by index. The table tracks whether each pin is active. -/
inductive NativeOpenedReport (start : NativeOpenedPosition opened) : NativeOpenedInstruction → Type 1 where
  | write (request : WriteRequest) (nonempty : request.rows ≠ [])
      (calls : WriteRequest.Calls (DescriptorInventory × DescriptorSlot × Nat))
      (cache : calls.cache = start.current.ready.state.cache)
      (observe : ∀ checked : CheckedWriteRequest request start.current.ready.state.session.directory
          start.current.ready.state.writer.installed calls.lookup,
        Nonempty (WriteCallPublication calls checked))
      {sequence : UInt64} {returnedHeap : heap} {reached : OpenWriteFiles}
      (actual : request.runOnOpenPhase start.current.ready.state.session.directory calls opened.phase opened.get opened.set
        (start.reached, (WriteRequest.readyCall start.current.ready.state.writer start.current.ready.state.cache).2.image) =
          .ok sequence (returnedHeap, reached))
      (custody : NativePendingWriteCensus start.current.ready.state reached.1) :
      NativeOpenedReport start (.write request)
  | writePreflight (request : WriteRequest) (calls : WriteRequest.Calls (DescriptorInventory × DescriptorSlot × Nat))
      (cache : calls.cache = start.current.ready.state.cache)
      (preflight : calls.ReturnsPreflight request start.current.ready.state) :
      NativeOpenedReport start (.write request)
  | checkpoint {image : Type}
      {attempt : SegmentedCheckpointReport start.current.ready.state.session.directory start.current.ready.state.writer}
      {reports : CheckpointCompletionReports (CensusDirectoryCache × image) attempt}
      (reported : NativeReadyCheckpoint start.current.ready.state reports)
      {reached : heap} {after : CensusDirectoryCache × image}
      (returned : runCheckpointOnOpenPhase (reported.primitives.cached.perform start.current.ready.state.session.directory)
        opened.phase opened.get opened.set (start.reached, start.current.ready.state.cache, (reports.observed.atRun 0).2) =
          .ok () (reached, after)) :
      NativeOpenedReport start .checkpoint
  | checkpointPreflight {image : Type}
      (calls : CheckpointPrimitiveCalls CheckpointOpenHandle image) (atEntry : image)
      {cause : IO.Error} {reached : heap} {after : CensusDirectoryCache × image}
      (returned : runCheckpointOnOpenPhase (calls.cached.perform start.current.ready.state.session.directory)
        opened.phase opened.get opened.set (start.reached, start.current.ready.state.cache, atEntry) =
          .error cause (reached, after))
      (stillReady : opened.contents reached opened.phase = some start.current.ready.state.session.phase) :
      NativeOpenedReport start .checkpoint
  | acquireAt (sequence : UInt64) {pin : SnapshotPin} {table : PackedTable}
      (acquired : start.current.ready.state.writer.installed.table.acquireAt sequence = some (pin, table)) :
      NativeOpenedReport start (.acquireAt sequence)
  | acquireAtUnavailable (sequence : UInt64)
      (unavailable : start.current.ready.state.writer.installed.table.acquireAt sequence = none) :
      NativeOpenedReport start (.acquireAt sequence)
  | releaseAt (index : Nat) (pin : NativeOpenedPin opened)
      (issued : start.pins[index]? = some pin)
      (compared : opened.ptrEq opened.token opened.token start.reached = .ok true start.reached) :
      NativeOpenedReport start (.releaseAt index)
  | advanceFloor (floor : UInt64) :
      NativeOpenedReport start (.advanceFloor floor)
  | readAt (index : Nat) (request : SnapshotReadRequest α) (pin : NativeOpenedPin opened)
      (issued : start.pins[index]? = some pin)
      (compared : opened.ptrEq opened.token opened.token start.reached = .ok true start.reached) :
      NativeOpenedReport start (.readAt index request)

namespace NativeOpenedReport

variable {start : NativeOpenedPosition opened} {instruction : NativeOpenedInstruction}

/-- Each reported call retains its actual source schedule and the raw
return at this step's reached phase heap. The common edge certifies the
same returned writer, table, or read response. -/
def Returns (report : NativeOpenedReport start instruction) (event : NativeExecutionEvent)
    (next : NativeOpenedPosition opened) : Prop :=
  match report with
  | .write request _ calls _ _ (sequence := sequence) (reached := reached) _ custody =>
    let state := start.current.ready.state
    let before := WriteRequest.readyCall state.writer state.cache
    opened.table.UsesOpenWriteSchedules state.session.directory opened.files opened.phase ∧
    request.runOnOpenPhase state.session.directory calls opened.phase opened.get opened.set
      (start.reached, before.2.image) = .ok sequence (next.reached, reached) ∧
    ∃ ack : ClassifiedWriteAcknowledgement start.current.ready request calls sequence reached custody,
      next.current = ⟨start.current.history ++ ack.report.batch,
        start.current.submissions ++ [.acknowledgedBatch ack.report.batch], ack.next⟩ ∧
      event = .acknowledged request ack.report.batch ∧ next.pins = start.pins
  | .writePreflight request calls _ _ =>
    let state := start.current.ready.state
    let before := WriteRequest.readyCall state.writer state.cache
    opened.table.UsesOpenWriteSchedules state.session.directory opened.files opened.phase ∧
    ∃ seen : NativeWritePreflightObservation state request,
      seen.lookup = calls.lookup ∧
      calls.run request state.session.directory state.writer = seen.resultAt before ∧
      request.runOnOpenPhase state.session.directory calls opened.phase opened.get opened.set (start.reached, before.2.image) =
        seen.resultAt (next.reached, before.2.image) ∧
      event = .writePreflight request seen.response ∧ next = start
  | .checkpoint (reports := reports) reported _ =>
    opened.table.UsesOpenCheckpointSchedule start.current.ready.state.session.directory opened.files opened.phase ∧
    runCheckpointOnOpenPhase (reported.primitives.cached.perform start.current.ready.state.session.directory)
      opened.phase opened.get opened.set (start.reached, start.current.ready.state.cache, (reports.observed.atRun 0).2) =
        .ok () (next.reached, reports.observed.completed) ∧
    (∃ writer, reported.Completed writer ∧ next.current.ready.state = reported.next writer) ∧
    event = .checkpoint ∧ next.pins = start.pins
  | .checkpointPreflight calls atEntry (cause := cause) _ _ =>
    let state := start.current.ready.state
    opened.table.UsesOpenCheckpointSchedule state.session.directory opened.files opened.phase ∧
    runCheckpointOnOpenPhase (calls.cached.perform state.session.directory)
      opened.phase opened.get opened.set (start.reached, state.cache, atEntry) =
        .error cause (next.reached, state.cache, atEntry) ∧
    CheckpointPreflight (.ready state.writer.installed) (.error cause) ∧
    event = .checkpointRejected cause ∧ next = start
  | .acquireAt sequence (pin := pin) _ =>
    ∃ issue : SnapshotPin → DiskSnapshotPin, ∃ returned : NativeOpenedPin opened,
      opened.table.acquireAt sequence = acquireSnapshotWith (m := IO)
        (do (← opened.phase.get).installed) opened.phase.set issue sequence ∧
      acquireSnapshotWith (m := EStateM IO.Error heap) (do (← opened.get opened.phase).installed)
        (opened.set opened.phase) issue sequence start.reached = .ok (some returned.raw) next.reached ∧
      returned.raw = issue pin ∧ returned.localPin = pin ∧ next.pins = start.pins ++ [returned] ∧
      event = .snapshotControl (.acquireAt sequence) (.ok (some (start.current.ready.state.session.sessionRef, pin)))
  | .acquireAtUnavailable sequence _ =>
    ∃ issue : SnapshotPin → DiskSnapshotPin,
      opened.table.acquireAt sequence = acquireSnapshotWith (m := IO)
        (do (← opened.phase.get).installed) opened.phase.set issue sequence ∧
      acquireSnapshotWith (m := EStateM IO.Error heap) (do (← opened.get opened.phase).installed)
        (opened.set opened.phase) issue sequence start.reached = .ok none next.reached ∧
      event = .snapshotControl (.acquireAt sequence) (.ok none) ∧
      next.reached = start.reached ∧ next.current.ready.state = start.current.ready.state ∧ next.pins = start.pins
  | .releaseAt _ pin _ _ =>
    opened.table.release pin.raw.handle = releaseSnapshotWith (m := IO)
      (do (← opened.phase.get).installed) (opened.token.ptrEq opened.token) opened.phase.set pin.localPin.handle ∧
    releaseSnapshotWith (m := EStateM IO.Error heap) (do (← opened.get opened.phase).installed)
      (opened.ptrEq opened.token opened.token) (opened.set opened.phase) pin.localPin.handle start.reached =
        .ok () next.reached ∧
    opened.set opened.phase next.current.ready.state.session.phase start.reached = .ok () next.reached ∧
    event = .snapshotControl (.release start.current.ready.state.session.sessionRef pin.localPin.handle) (.ok ()) ∧
    next.pins = start.pins
  | .advanceFloor floor =>
    opened.table.advanceFloor floor = advanceFloorWith (m := IO)
      (do (← opened.phase.get).installed) opened.phase.set floor ∧
    ∃ accepted : Bool,
      advanceFloorWith (m := EStateM IO.Error heap) (do (← opened.get opened.phase).installed)
        (opened.set opened.phase) floor start.reached = .ok accepted next.reached ∧
      (accepted = false → next.reached = start.reached) ∧
      (accepted = true →
        opened.set opened.phase next.current.ready.state.session.phase start.reached = .ok () next.reached) ∧
      event = .snapshotControl (.advanceFloor floor) (.ok accepted) ∧ next.pins = start.pins
  | .readAt _ request pin _ _ =>
    (match request with
      | .lookup key => opened.table.lookup pin.raw.handle key = readSnapshotWith (m := IO)
          (do (← opened.phase.get).installed) (opened.token.ptrEq opened.token)
          (fun table => table.lookup pin.localPin.handle key)
      | .range lo hi => opened.table.range pin.raw.handle lo hi = readSnapshotWith (m := IO)
          (do (← opened.phase.get).installed) (opened.token.ptrEq opened.token)
          (fun table => table.range pin.localPin.handle lo hi)) ∧
    ∃ response recorded,
      readSnapshotWith (m := EStateM IO.Error heap) (do (← opened.get opened.phase).installed)
        (opened.ptrEq opened.token opened.token) (request.read pin.localPin.handle) start.reached =
          .ok response next.reached ∧
      event = .snapshotHandleRead start.current.ready.state.session.sessionRef pin.localPin.handle
        request response recorded ∧
      next.reached = start.reached ∧ next.pins = start.pins

structure Reached (report : NativeOpenedReport start instruction) (event : NativeExecutionEvent)
    (next : NativeOpenedPosition opened) : Prop where
  common : NativeExecutionStep start.current event next.current
  returned : report.Returns event next

private theorem reachesSnapshotControl {current : NativeExecutionPosition}
    {observed : NativeSnapshotUpdateObservation current.ready.state α}
    {next : NativeReadPosition current.history current.submissions} {value : α}
    (transition : NativeSnapshotUpdateContinuation current.ready observed next)
    (returned : observed.run = .ok value next.state.session) :
    NativeExecutionStep current (.snapshotControl observed.update (.ok value))
      ⟨current.history, current.submissions, next⟩ ∧
    next.state.session.directory = current.ready.state.session.directory := by
  have step := NativeExecutionStep.snapshotControl current observed next transition
  have response := transition.returned.symm.trans returned
  have state := transition.reached
  generalize observed.update.outcome current.ready.state.session = outcome at step response state
  cases outcome
  case failed => cases response
  all_goals
    have same := (EStateM.Result.ok.inj response).1
    subst value
    have directory := congrArg (fun value : NativeReadyState => value.session.directory) state
    exact ⟨step, directory⟩

/-- Derive the next common step and the exact raw phase interpretation
from the local report. The step acquires its next position here. -/
theorem reaches (report : NativeOpenedReport start instruction) :
    ∃ event next, report.Reached event next := by
  cases report with
  | @write request nonempty calls cache observe sequence returnedHeap reached actual custody =>
    obtain ⟨ack, stored, _⟩ := start.current.ready.acknowledgesClassifiedWrite opened.table start.uses
      opened.phaseEffects start.stored request nonempty calls cache observe actual custody
    have directory : ack.next.state.session.directory = opened.directory := by
      rw [ack.exactState]
      exact start.directory
    let nextPosition : NativeOpenedPosition opened :=
      ⟨⟨start.current.history ++ ack.report.batch, start.current.submissions ++ [.acknowledgedBatch ack.report.batch],
        ack.next⟩, returnedHeap, directory, stored, start.pins⟩
    exact ⟨_, nextPosition, .acknowledgedClassified start.current ack, start.uses.writeSchedules,
      actual, ack, rfl, rfl, rfl⟩
  | writePreflight request calls cache preflight =>
    obtain ⟨source, seen, lookup, normalized, raw, continuation⟩ :=
      start.current.ready.preflightsClassifiedWriteOnOpenPhase opened.table start.uses opened.phaseEffects start.stored
        request calls cache preflight
    exact ⟨_, start, .writePreflight start.current seen continuation, source, seen, lookup, normalized, raw, rfl, rfl⟩
  | @checkpoint _ _ reports reported _ _ returned =>
    obtain ⟨source, writer, next, completed, reached, after, state, step, _, _, _, pins⟩ :=
      start.checkpointsFromReturn reported.primitives (reports.observed.atRun 0).2 reported rfl rfl returned
    exact ⟨_, next, step, source, by simpa only [reached, ← after] using returned,
      ⟨writer, completed, state⟩, rfl, pins⟩
  | checkpointPreflight calls atEntry returned stillReady =>
    obtain ⟨source, reached, after, preflight, _, step⟩ :=
      start.rejectsCheckpointFromReturn calls atEntry returned stillReady
    exact ⟨_, start, step, source, by simpa only [reached, after] using returned, preflight, rfl, rfl⟩
  | @acquireAt sequence pin table acquired =>
    obtain ⟨issue, next, result, reached, issued, source, transition, returned, raw, stored, _⟩ :=
      start.current.ready.acquiresViaOpenReferences opened.table start.uses opened.phaseEffects start.stored sequence
    have valid := start.current.ready.readPrefix.refines.1
    have exactPin := (EStateM.Result.ok.inj (returned.symm.trans (valid.acquireReturns acquired))).1
    subst result
    have state := transition.reached
    simp only [NativeSnapshotUpdateObservation.update, SnapshotUpdate.outcome, valid.phase, acquired] at state
    have directory : next.state.session.directory = opened.directory := by
      rw [state]
      exact start.directory
    let actualPin : NativeOpenedPin opened := ⟨issue pin, pin, issued pin⟩
    let nextPosition : NativeOpenedPosition opened :=
      ⟨⟨start.current.history, start.current.submissions, next⟩, reached, directory, stored, start.pins ++ [actualPin]⟩
    have common := NativeExecutionStep.snapshotControl start.current (.acquireAt sequence) next transition
    simp only [NativeSnapshotUpdateObservation.update, SnapshotUpdate.outcome, valid.phase, acquired] at common
    exact ⟨_, nextPosition, common, issue, actualPin, source, raw, rfl, rfl, rfl, rfl⟩
  | acquireAtUnavailable sequence unavailable =>
    obtain ⟨issue, next, result, reached, _, source, transition, returned, raw, stored, keepsHeap⟩ :=
      start.current.ready.acquiresViaOpenReferences opened.table start.uses opened.phaseEffects start.stored sequence
    have ready := start.current.ready.readPrefix.refines.1.phase
    have noneReturned : start.current.ready.state.session.runAcquireAt sequence = .ok none next.state.session := by
      simpa only [NativeSnapshotUpdateObservation.run, NativeSnapshotUpdateObservation.update, SnapshotUpdate.outcome,
        ready, unavailable] using transition.returned
    have sameResult := (EStateM.Result.ok.inj (returned.symm.trans noneReturned)).1
    subst result
    have state : next.state = start.current.ready.state := by
      simpa only [NativeSnapshotUpdateObservation.update, SnapshotUpdate.outcome, ready, unavailable] using transition.reached
    obtain ⟨step, directory⟩ := reachesSnapshotControl transition noneReturned
    let position : NativeOpenedPosition opened :=
      ⟨⟨start.current.history, start.current.submissions, next⟩, reached, directory.trans start.directory,
        stored, start.pins⟩
    exact ⟨_, position, step, issue, source, raw, rfl, keepsHeap rfl, state, rfl⟩
  | releaseAt _ pin _ compared =>
    obtain ⟨source, next, reached, transition, returned, raw, stored, _, setter⟩ :=
      start.current.ready.releasesViaOpenReferences opened.table start.uses pin.issued
        opened.phaseEffects start.stored opened.ptrEq start.current.ready.state.session.sessionRef true (by simp) compared
    obtain ⟨step, directory⟩ := reachesSnapshotControl transition returned
    let position : NativeOpenedPosition opened :=
      ⟨⟨start.current.history, start.current.submissions, next⟩, reached, directory.trans start.directory,
        stored, start.pins⟩
    exact ⟨_, position, step, source, raw, setter rfl, rfl, rfl⟩
  | advanceFloor floor =>
    obtain ⟨source, next, reached, accepted, transition, returned, raw, stored, refused, setter⟩ :=
      start.current.ready.advancesFloorViaOpenReferences opened.table start.uses opened.phaseEffects start.stored floor
    obtain ⟨step, directory⟩ := reachesSnapshotControl transition returned
    let position : NativeOpenedPosition opened :=
      ⟨⟨start.current.history, start.current.submissions, next⟩, reached, directory.trans start.directory,
        stored, start.pins⟩
    exact ⟨_, position, step, source, accepted, raw, refused, setter, rfl, rfl⟩
  | readAt _ request pin _ compared =>
    obtain ⟨source, response, recorded, next, observed, raw, _⟩ :=
      start.current.ready.readsOpenPin opened.table start.uses pin.issued
        (fun value => opened.phaseEffects.reads start.reached opened.phase value) start.stored opened.ptrEq compared request
    let nextPosition : NativeOpenedPosition opened :=
      ⟨⟨start.current.history, start.current.submissions, next⟩, start.reached,
        observed.state.symm ▸ start.directory, observed.state.symm ▸ start.stored, start.pins⟩
    have common := NativeExecutionStep.snapshotHandleRead start.current
      ⟨pin.localPin.handle, start.current.ready.state.session.sessionRef, true, by simp⟩ request response recorded next observed
    refine ⟨_, nextPosition, common, ?_, response, recorded, raw, rfl, rfl, rfl⟩
    cases request <;> exact source

end NativeOpenedReport

/-- A finite prefix on one handle. The raw reports and the common
execution share every intermediate position. -/
inductive NativeOpenedTrace (start : NativeOpenedPosition opened) :
    List NativeOpenedInstruction → List NativeExecutionEvent → NativeOpenedPosition opened → Prop where
  | empty : NativeOpenedTrace start [] [] start
  | step (prior : NativeOpenedTrace start instructions events current)
      (report : NativeOpenedReport current instruction) (next : report.Reached event reached) :
      NativeOpenedTrace start (instructions ++ [instruction]) (events ++ [event]) reached

namespace NativeOpenedTrace

variable {start last : NativeOpenedPosition opened}

theorem common (trace : NativeOpenedTrace start instructions events last) :
    NativeExecutionTrace start.current events last.current := by
  induction trace with
  | empty => exact .empty
  | step _ _ next prior => exact .step prior next.common

/-- Supply a local report for the next prescribed instruction only at
positions reached by earlier returned operations on this handle. -/
def Reports (start : NativeOpenedPosition opened) (instructions : List NativeOpenedInstruction) : Prop :=
  ∀ issued events reached instruction remaining,
    instructions = issued ++ instruction :: remaining →
    NativeOpenedTrace start issued events reached → Nonempty (NativeOpenedReport reached instruction)

/-- A ready suffix can begin with previously tracked pins. Use
`NativeOpenedPosition.fromOpen` to start immediately after opening. -/
theorem executes (start : NativeOpenedPosition opened) (instructions : List NativeOpenedInstruction)
    (reports : Reports start instructions) :
    ∃ events last, NativeOpenedTrace start instructions events last ∧
      NativeExecutionTrace start.current events last.current ∧
      InstalledClientReplay last.current.submissions last.current.ready.reads last.current.history
        last.current.ready.state.writer.installed last.current.ready.state.session := by
  have finish (remaining : List NativeOpenedInstruction) : ∀ issued events current,
      instructions = issued ++ remaining → NativeOpenedTrace start issued events current →
      ∃ events last, NativeOpenedTrace start instructions events last := by
    induction remaining with
    | nil =>
      intro issued events current ordered trace
      exact ⟨events, current, by simpa [ordered] using trace⟩
    | cons instruction remaining earlier =>
      intro issued events current ordered trace
      obtain ⟨report⟩ := reports issued events current instruction remaining ordered trace
      obtain ⟨event, next, reached⟩ := report.reaches
      have follows : instructions = (issued ++ [instruction]) ++ remaining := by
        simpa [List.append_assoc] using ordered
      exact earlier (issued ++ [instruction]) (events ++ [event]) next follows (.step trace report reached)
  obtain ⟨events, last, trace⟩ := finish instructions [] [] start (by simp) .empty
  exact ⟨events, last, trace, trace.common, trace.common.keyValueRefinement.2.2.2⟩

end NativeOpenedTrace
end Alvoki.Storage.DiskSession
