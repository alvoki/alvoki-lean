import Alvoki.Storage.Disk.NativeOpenCheckpointReadTrace
import Alvoki.Storage.Disk.NativeClassifiedWritePreflight

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open Sequential (SnapshotPin)

-- The interpreted callbacks track the phase heap. File and cache effects
-- remain in the reached native execution position.
structure NativeOpenedHandle (heap : Type) where
  table : DiskTable
  directory : DiskDirectory
  lock : IO.FS.Handle
  files : DiskTable.OpenSyncFiles
  phase : IO.Ref (Phase Installed)
  token : IO.Ref Unit
  uses : table.UsesOpenReferences directory lock files phase token
  contents : heap → IO.Ref (Phase Installed) → Option (Phase Installed)
  get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)
  set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit
  phaseEffects : OpenPhaseCellEffects contents get set
  ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- Keep the actual issued pin alongside its model handle and sequence. -/
structure NativeOpenedPin (opened : NativeOpenedHandle heap) where
  raw : DiskSnapshotPin
  localPin : SnapshotPin
  issued : raw.UsesOpenToken opened.token localPin

/-- The same opened handle supplies the phase cell at every reached
position. The common position carries the exact modeled file state,
synchronization cache and owner. -/
structure NativeOpenedPosition (opened : NativeOpenedHandle heap) where
  current : NativeExecutionPosition
  reached : heap
  directory : current.ready.state.session.directory = opened.directory
  stored : opened.contents reached opened.phase = some current.ready.state.session.phase
  pins : List (NativeOpenedPin opened)

/-- Seed a trace from a reached ready open before any snapshot pin has
been issued. Later reads then use pins issued inside the trace. -/
def NativeOpenedPosition.fromOpen (opened : NativeOpenedHandle heap) (start : NativeExecutionPosition)
    (reached : heap) (directory : start.ready.state.session.directory = opened.directory)
    (stored : opened.contents reached opened.phase = some start.ready.state.session.phase) :
    NativeOpenedPosition opened :=
  ⟨start, reached, directory, stored, []⟩

theorem NativeOpenedPosition.uses (position : NativeOpenedPosition opened) :
    opened.table.UsesOpenReferences position.current.ready.state.session.directory opened.lock opened.files
      opened.phase opened.token :=
  position.directory.symm ▸ opened.uses

inductive NativeOpenedInstruction : Type 1 where
  | write (request : WriteRequest)
  | checkpoint
  | acquireAt (sequence : UInt64)
  | readAt (index : Nat) (request : SnapshotReadRequest α)

/-- Per-call observations at the reached position. A read gets its pin
by index from the reached list of tracked and newly issued pins. -/
inductive NativeOpenedReport (start : NativeOpenedPosition opened) : NativeOpenedInstruction → Type 1 where
  | write (request : WriteRequest) {prepared : NativeReadyWritePreparation start.current.ready.state}
      (reported : NativeReadyWriteReport prepared) (rows : request.rows = prepared.rows) :
      NativeOpenedReport start (.write request)
  | writePreflight (request : WriteRequest) (calls : WriteRequest.Calls (DescriptorInventory × DescriptorSlot × Nat))
      (cache : calls.cache = start.current.ready.state.cache)
      (preflight : calls.ReturnsPreflight request start.current.ready.state) :
      NativeOpenedReport start (.write request)
  | checkpoint {image : Type}
      {attempt : SegmentedCheckpointReport start.current.ready.state.session.directory start.current.ready.state.writer}
      {reports : CheckpointCompletionReports (CensusDirectoryCache × image) attempt}
      (reported : NativeReadyCheckpoint start.current.ready.state reports) :
      NativeOpenedReport start .checkpoint
  | acquireAt (sequence : UInt64) {pin : SnapshotPin} {table : PackedTable}
      (acquired : start.current.ready.state.writer.installed.table.acquireAt sequence = some (pin, table)) :
      NativeOpenedReport start (.acquireAt sequence)
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
  | .write request (prepared := prepared) reported _ =>
    opened.table.UsesOpenWriteSchedules start.current.ready.state.session.directory opened.files opened.phase ∧
    reported.ReturnsOnOpenPhase request opened.phase opened.get opened.set start.reached next.reached ∧
    (∃ target, next.current.ready.state = reported.next target) ∧
    event = .acknowledged request prepared.batch ∧ next.pins = start.pins
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
  | .checkpoint reported =>
    opened.table.UsesOpenCheckpointSchedule start.current.ready.state.session.directory opened.files opened.phase ∧
    reported.ReturnsOnOpenPhase opened.phase opened.get opened.set start.reached next.reached ∧
    (∃ writer, reported.Completed writer ∧ next.current.ready.state = reported.next writer) ∧
    event = .checkpoint ∧ next.pins = start.pins
  | .acquireAt sequence (pin := pin) _ =>
    ∃ issue : SnapshotPin → DiskSnapshotPin, ∃ returned : NativeOpenedPin opened,
      opened.table.acquireAt sequence = acquireSnapshotWith (m := IO)
        (do (← opened.phase.get).installed) opened.phase.set issue sequence ∧
      acquireSnapshotWith (m := EStateM IO.Error heap) (do (← opened.get opened.phase).installed)
        (opened.set opened.phase) issue sequence start.reached = .ok (some returned.raw) next.reached ∧
      returned.raw = issue pin ∧ returned.localPin = pin ∧ next.pins = start.pins ++ [returned] ∧
      event = .snapshotControl (.acquireAt sequence) (.ok (some (start.current.ready.state.session.sessionRef, pin)))
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

/-- Derive the next common step and the exact raw phase interpretation
from the local report. The step acquires its next position here. -/
theorem reaches (report : NativeOpenedReport start instruction) :
    ∃ event next, report.Reached event next := by
  cases report with
  | @write request prepared reported rows =>
    obtain ⟨source, _, reached, target, next, _, _, _, _, stored, raw, normalized, state, initial, seed, reads, _, _⟩ :=
      start.current.ready.acknowledgesViaOpenReferences opened.table start.uses opened.phaseEffects start.stored reported request rows
    have directory : next.state.session.directory = opened.directory := by
      rw [state]
      exact start.directory
    let nextPosition : NativeOpenedPosition opened :=
      ⟨⟨start.current.history ++ prepared.batch, start.current.submissions ++ [.acknowledgedBatch prepared.batch], next⟩,
        reached, directory, stored, start.pins⟩
    exact ⟨_, nextPosition, .acknowledged start.current reported request rows target next normalized state initial seed reads,
      source, raw, ⟨target, state⟩, rfl, rfl⟩
  | writePreflight request calls cache preflight =>
    obtain ⟨source, seen, lookup, normalized, raw, continuation⟩ :=
      start.current.ready.preflightsClassifiedWriteOnOpenPhase opened.table start.uses opened.phaseEffects start.stored
        request calls cache preflight
    exact ⟨_, start, .writePreflight start.current seen continuation, source, seen, lookup, normalized, raw, rfl, rfl⟩
  | checkpoint reported =>
    obtain ⟨source, writer, _, reached, _, _, _, _, stored, raw, completed, history, _, _⟩ :=
      start.current.ready.checkpointsViaOpenReferences opened.table start.uses opened.phaseEffects start.stored reported
    obtain ⟨next, common, state, _⟩ := start.current.checkpointAtWriter reported writer completed history
    have directory : next.state.session.directory = opened.directory := by
      rw [state]
      exact start.directory
    let nextPosition : NativeOpenedPosition opened :=
      ⟨⟨start.current.history, start.current.submissions, next⟩, reached, directory, state.symm ▸ stored, start.pins⟩
    exact ⟨_, nextPosition, common, source, raw, ⟨writer, completed, state⟩, rfl, rfl⟩
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
