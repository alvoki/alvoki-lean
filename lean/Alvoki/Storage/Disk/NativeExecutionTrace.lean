import Alvoki.Storage.Disk.BootstrapExecution
import Alvoki.Storage.Disk.NativeReadRecoveryTrace

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

/-- The reached session, its committed WAL and the client requests that
account for it. A local read prefix preserves the corresponding ledger. -/
structure NativeExecutionPosition where
  history : List WAL.Write
  submissions : List DatabaseSubmissions
  ready : NativeReadPosition history submissions

inductive NativeExecutionEvent where
  | readOrRestart (event : NativeReadRecoveryEvent)
  | acknowledged (request : WriteRequest) (batch : List WAL.Write)

namespace NativeExecutionEvent

def writes : NativeExecutionEvent → List WAL.Write
  | .readOrRestart _ => []
  | .acknowledged _ batch => batch

def submissions : NativeExecutionEvent → List DatabaseSubmissions
  | .readOrRestart _ => []
  | .acknowledged _ batch => [.acknowledgedBatch batch]

def reads : NativeExecutionEvent → List RecordedSnapshotRead
  | .readOrRestart event => event.responses
  | .acknowledged _ _ => []

end NativeExecutionEvent

/-- A read or restart uses the exact preceding ready position. A write
changes that position only through its native acknowledgement, with the
same session token and the newly reached files, census and cache. -/
inductive NativeExecutionStep : NativeExecutionPosition → NativeExecutionEvent → NativeExecutionPosition → Prop where
  | readOrRestart (current : NativeExecutionPosition) {event : NativeReadRecoveryEvent}
      {next : NativeReadPosition current.history current.submissions}
      (observed : NativeReadRecoveryStep current.ready event next) :
      NativeExecutionStep current (.readOrRestart event) ⟨current.history, current.submissions, next⟩
  | acknowledged (current : NativeExecutionPosition)
      {prepared : NativeReadyWritePreparation current.ready.state} (observed : NativeReadyWriteReport prepared)
      (request : WriteRequest) (rows : request.rows = prepared.rows) (target : Target)
      (next : NativeReadPosition (current.history ++ prepared.batch) (current.submissions ++ [.acknowledgedBatch prepared.batch]))
      (returned : let reached := observed.next target
        observed.calls.run request current.ready.state.session.directory current.ready.state.writer =
          .ok prepared.table.committed (reached.session.phase, ⟨(reached.cache, prepared.settled), reached.files.owners⟩))
      (state : next.state = observed.next target)
      (initial : next.initial = observed.next target)
      (seed : next.opened = .ok next.state.session (next.state.census, next.state.files))
      (earlier : next.reads = current.ready.reads) :
      NativeExecutionStep current (.acknowledged request prepared.batch)
        ⟨current.history ++ prepared.batch, current.submissions ++ [.acknowledgedBatch prepared.batch], next⟩

/-- Interpret the submitted single or batch write with the reported
primitive effects and start the next position from its actual result. -/
theorem NativeExecutionPosition.acknowledges (current : NativeExecutionPosition)
    {prepared : NativeReadyWritePreparation current.ready.state} (observed : NativeReadyWriteReport prepared)
    (request : WriteRequest) (rows : request.rows = prepared.rows) :
    ∃ next, NativeExecutionStep current (.acknowledged request prepared.batch) next := by
  obtain ⟨target, next, returned, reached, initial, reads, opened, _⟩ :=
    current.ready.acknowledgesWrite observed request rows
  exact ⟨_, .acknowledged current observed request rows target next returned reached initial
    (reached.symm ▸ opened) reads⟩

theorem NativeExecutionStep.ledgers (step : NativeExecutionStep before event after) :
    after.history = before.history ++ event.writes ∧
    after.submissions = before.submissions ++ event.submissions ∧
    after.ready.reads = before.ready.reads ++ event.reads := by
  cases step with
  | readOrRestart observed => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], observed.frames.1⟩
  | acknowledged _ _ _ _ _ _ _ _ _ reads =>
    exact ⟨rfl, rfl, by simpa [NativeExecutionEvent.reads] using reads⟩

/-- A finite trace of supported reads, acknowledged native writes, and
reported quiet crashes followed by healthy aligned reopens. Each step
uses the exact files and session reached by its preceding step. -/
inductive NativeExecutionTrace (start : NativeExecutionPosition) :
    List NativeExecutionEvent → NativeExecutionPosition → Prop where
  | empty : NativeExecutionTrace start [] start
  | step (prior : NativeExecutionTrace start events before) (next : NativeExecutionStep before event after) :
      NativeExecutionTrace start (events ++ [event]) after

theorem NativeExecutionTrace.ledgers (observed : NativeExecutionTrace start events last) :
    last.history = start.history ++ events.flatMap NativeExecutionEvent.writes ∧
    last.submissions = start.submissions ++ events.flatMap NativeExecutionEvent.submissions ∧
    last.ready.reads = start.ready.reads ++ events.flatMap NativeExecutionEvent.reads := by
  induction observed with
  | empty => simp
  | step _ next ih =>
    obtain ⟨writes, submissions, reads⟩ := next.ledgers
    refine ⟨?_, ?_, ?_⟩
    · rw [writes, ih.1]
      simp [List.append_assoc]
    · rw [submissions, ih.2.1]
      simp [List.append_assoc]
    · rw [reads, ih.2.2]
      simp [List.append_assoc]

/-- Every acknowledged batch is present in order, all logged responses
agree with one replay, and that same replay explains the returned table's
supported reads. -/
theorem NativeExecutionTrace.keyValueRefinement (observed : NativeExecutionTrace start events last) :
    last.history = start.history ++ events.flatMap NativeExecutionEvent.writes ∧
    last.submissions = start.submissions ++ events.flatMap NativeExecutionEvent.submissions ∧
    last.ready.reads = start.ready.reads ++ events.flatMap NativeExecutionEvent.reads ∧
    InstalledClientReplay last.submissions last.ready.reads last.history
      last.ready.state.writer.installed last.ready.state.session := by
  obtain ⟨writes, submissions, reads⟩ := observed.ledgers
  exact ⟨writes, submissions, reads, last.ready.readPrefix.guardedReplay⟩

inductive NativeExecutionInstruction : Type 1 where
  | snapshot (sequence : UInt64) (request : SnapshotReadRequest α)
  | write (request : WriteRequest)
  | restart (input : FilePath)

/-- The recorded event belongs to the submitted instruction. Read
observations determine the requested key or range and sequence. -/
def NativeExecutionInstruction.Matches : NativeExecutionInstruction → NativeExecutionEvent → Prop
  | .snapshot sequence request, .readOrRestart (.read recorded) =>
    ∃ response, recorded = request.record sequence response
  | .write request, .acknowledged submitted _ => submitted = request
  | .restart input, .readOrRestart (.restart resolvedInput) => resolvedInput = input
  | _, _ => False

inductive NativeExecutionInstructions : List NativeExecutionInstruction → List NativeExecutionEvent → Prop where
  | empty : NativeExecutionInstructions [] []
  | step (prior : NativeExecutionInstructions instructions events)
      (matched : instruction.Matches event) :
      NativeExecutionInstructions (instructions ++ [instruction]) (events ++ [event])

/-- Reports for the next supported native operation. Each constructor
supplies local observations at the reached state. The returned session,
writer and client replay are derived by the corresponding step. -/
inductive NativeExecutionObservation (state : NativeReadyState) : Type 1 where
  | snapshot (sequence : UInt64) (request : SnapshotReadRequest α)
      (floor : state.writer.installed.table.pins.floor ≤ sequence)
      (committed : sequence ≤ state.writer.installed.table.committed)
  | write (prepared : NativeReadyWritePreparation state) (observed : NativeReadyWriteReport prepared)
      (request : WriteRequest) (rows : request.rows = prepared.rows)
  | restart (crash : NativeReadyQuietCrash state) (input : FilePath)
      (observe : ∀ layout : CanonicalKeeperLayout crash.retry.image state.writer.history,
        layout.target = state.writer.target → Prepared crash.retry.image layout.target layout.plan →
        ∀ selected : SelectedIntegrityCheckpoint state.writer.published.durable
          crash.retry.image.directory.active.manifest state.writer.checkpoint,
        Nonempty (NativeReadyRestartReads crash input layout selected))

def NativeExecutionObservation.instruction : NativeExecutionObservation state → NativeExecutionInstruction
  | .snapshot sequence request _ _ => .snapshot sequence request
  | .write _ _ request _ => .write request
  | .restart _ input _ => .restart input

theorem NativeExecutionPosition.observesStep (current : NativeExecutionPosition)
    (observed : NativeExecutionObservation current.ready.state) :
    ∃ event next, NativeExecutionStep current event next ∧ observed.instruction.Matches event := by
  cases observed with
  | snapshot sequence request floor committed =>
    obtain ⟨_, response, step⟩ := current.ready.readAt sequence floor committed request
    exact ⟨_, _, .readOrRestart current step, ⟨response, rfl⟩⟩
  | write _ observed request rows =>
    obtain ⟨_, step⟩ := current.acknowledges observed request rows
    exact ⟨_, _, step, rfl⟩
  | restart crash _ observe =>
    obtain ⟨_, step⟩ := current.ready.restart crash observe
    exact ⟨_, _, .readOrRestart current step, rfl⟩

/-- Supply the primitive reports for the next prescribed instruction
at its reached state. The whole trace and its endpoint are derived from
those reports, in the order of the original instruction list. -/
def NativeExecutionTrace.Reports (start : NativeExecutionPosition)
    (instructions : List NativeExecutionInstruction) : Prop :=
  ∀ issued events current instruction remaining,
    instructions = issued ++ instruction :: remaining →
    NativeExecutionTrace start events current → NativeExecutionInstructions issued events →
    ∃ observed : NativeExecutionObservation current.ready.state, observed.instruction = instruction

theorem NativeExecutionTrace.executes (start : NativeExecutionPosition)
    (instructions : List NativeExecutionInstruction) (observe : NativeExecutionTrace.Reports start instructions) :
    ∃ events last, NativeExecutionInstructions instructions events ∧ NativeExecutionTrace start events last ∧
      InstalledClientReplay last.submissions last.ready.reads last.history
        last.ready.state.writer.installed last.ready.state.session := by
  have finishes (remaining : List NativeExecutionInstruction) : ∀ issued events current,
      instructions = issued ++ remaining →
      NativeExecutionTrace start events current → NativeExecutionInstructions issued events →
      ∃ events last, NativeExecutionInstructions instructions events ∧ NativeExecutionTrace start events last := by
    induction remaining with
    | nil =>
      intro issued events current scheduled trace matched
      exact ⟨events, current, by simpa [scheduled] using matched, trace⟩
    | cons instruction remaining ih =>
      intro issued events current scheduled trace matched
      obtain ⟨reported, requested⟩ := observe issued events current instruction remaining scheduled trace matched
      obtain ⟨event, after, step, same⟩ := current.observesStep reported
      have scheduleNext : instructions = (issued ++ [instruction]) ++ remaining := by
        simpa [List.append_assoc] using scheduled
      exact ih (issued ++ [instruction]) (events ++ [event]) after scheduleNext (.step trace step)
        (.step matched (requested ▸ same))
  obtain ⟨events, last, matched, trace⟩ := finishes instructions [] [] start (by simp) .empty .empty
  exact ⟨events, last, matched, trace, trace.keyValueRefinement.2.2.2⟩

private abbrev BootstrapHandle := DescriptorInventory × DescriptorSlot × Nat

/-- The exact bootstrap return starts the mixed trace with empty
ledgers. A finite continuation uses the acknowledgements and local read
responses in that trace to explain its last reached session. -/
theorem BootstrapKeeperMarkerHandoff.executesFromEmpty
    {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
    {calls : BootstrapOpenCalls (Cache BootstrapHandle) directory before}
    {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls} {listed : BootstrapCheckedListing captured}
    {keeper : BootstrapZeroKeeperRoute listed} {marker : BootstrapMarkerCustody listed}
    (bootstrap : BootstrapKeeperMarkerHandoff keeper marker)
    {input : FilePath} (admission : OpenAdmissionReports input directory calls.slot)
    (empty : before.image = ⟨DirectoryPublication.Image.settled ⟨none, none⟩, .absent⟩)
    (effects : BootstrapKeeperMarkerHandoff.ReturnedCensus marker) :
    ∃ (boot : BootstrapClientStart directory calls.slot.description (calls.run admission)) (start : NativeExecutionPosition),
      calls.run admission = .ok start.ready.state.session boot.final ∧
      start.ready.state.session = boot.session ∧
      start.ready.state.writer = boot.writer ∧ start.ready.state.census = effects.reached ∧
      ∀ instructions, NativeExecutionTrace.Reports start instructions →
        ∃ events last, NativeExecutionInstructions instructions events ∧ NativeExecutionTrace start events last ∧
          last.history = events.flatMap NativeExecutionEvent.writes ∧
          last.submissions = events.flatMap NativeExecutionEvent.submissions ∧
          last.ready.reads = events.flatMap NativeExecutionEvent.reads ∧
          InstalledClientReplay last.submissions last.ready.reads last.history
            last.ready.state.writer.installed last.ready.state.session := by
  obtain ⟨boot, returned, _, _, _, _, _, _, _, _, ready⟩ :=
    bootstrap.startsNativeReadPrefixFromEmpty admission empty effects
  let state : NativeReadyState :=
    ⟨boot.session, boot.writer, effects.reached, captured.cache, calls.slot, captured.cached⟩
  let start : NativeExecutionPosition :=
    ⟨[], [], ⟨.ok state.session (state.census, state.files), state, state, [], ready⟩⟩
  refine ⟨boot, start, returned, rfl, rfl, rfl, ?_⟩
  intro instructions observe
  obtain ⟨events, last, matched, trace, replay⟩ := NativeExecutionTrace.executes start instructions observe
  obtain ⟨writes, submissions, reads⟩ := trace.ledgers
  exact ⟨events, last, matched, trace, by simpa [start] using writes, by simpa [start] using submissions,
    by simpa [start] using reads, replay⟩

end Alvoki.Storage.DiskSession
