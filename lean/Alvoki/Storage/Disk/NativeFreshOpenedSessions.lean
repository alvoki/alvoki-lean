import Alvoki.Storage.Disk.NativeFreshTableOpen
import Alvoki.Storage.Disk.NativeOpenReadyTrace
import Alvoki.Storage.Disk.NativeEarlyCheckpointTerminal

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication

namespace NativeOpenedTrace

variable {heap : Type} {opened : NativeOpenedHandle heap} {start last : NativeOpenedPosition opened}

/-- The write instructions in a returned prefix already determine the
matching client instructions. Ack and preflight denial both retain the
request that was actually issued. -/
theorem writeInstructions (trace : NativeOpenedTrace start instructions events last)
    {requests : List WriteRequest}
    (asWrites : instructions = requests.map NativeOpenedInstruction.write) :
    NativeExecutionInstructions (requests.map NativeExecutionInstruction.write) events := by
  induction trace generalizing requests with
  | empty =>
    have empty : requests = [] := List.map_eq_nil_iff.mp asWrites.symm
    subst requests
    exact .empty
  | @step instructions events current instruction event reached prior report next earlier =>
    rcases List.eq_nil_or_concat requests with empty | ⟨previous, request, appended⟩
    · simp [empty] at asWrites
    · subst requests
      simp only [List.concat_eq_append, List.map_append, List.map_cons, List.map_nil] at asWrites ⊢
      obtain ⟨priorWrites, sameInstruction⟩ := List.append_inj' asWrites (by simp)
      have same := (List.cons.inj sameInstruction).1
      subst instruction
      have matched : (NativeExecutionInstruction.write request).Matches event := by
        cases report with
        | write =>
          obtain ⟨_, _, _, _, eventEq, _⟩ := next.returned
          rw [eventEq]
          rfl
        | writePreflight =>
          obtain ⟨_, _, _, _, _, eventEq, _⟩ := next.returned
          rw [eventEq]
          rfl
      exact .step (earlier priorWrites) matched

end NativeOpenedTrace

namespace FreshBootstrapOpenHeap.Returned

variable {heap : Type} {call : EStateM IO.Error heap DiskTable} {entry : heap}
  (opened : FreshBootstrapOpenHeap.Returned call entry)

/-- The common execution consumes the empty ledgers derived by the
fresh installer. This applies to both same-handle and later sessions. -/
theorem refinesTrace (trace : NativeExecutionTrace opened.start.current events last) :
    last.history = events.flatMap NativeExecutionEvent.writes ∧
    last.submissions = events.flatMap NativeExecutionEvent.submissions ∧
    last.ready.reads = events.flatMap NativeExecutionEvent.reads ∧
    InstalledClientReplay last.submissions last.ready.reads last.history
      last.ready.state.writer.installed last.ready.state.session := by
  simpa only [opened.emptyHistory, opened.emptySubmissions, opened.emptyReads, List.nil_append]
    using trace.keyValueRefinement

/-- End at the checkpoint issued on the heap of the preceding returned
call. Both the prior replay and the stop use the same opened position. -/
def stopsAfterWrites {last : NativeOpenedPosition opened.handle} {requests : List WriteRequest}
    (trace : NativeOpenedTrace opened.start (requests.map NativeOpenedInstruction.write) events last)
    {primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap} {fsync : CheckpointFsync heap}
    {stage : Step} {reason : FilePath} {reached : CheckpointWorld heap}
    (stop : NativeCheckpointSourceStop last primitives fsync stage reason reached)
    {storage : heap → CheckpointStorageObservation}
    (early : stage = .syncRunsDirectory ∨ ∃ index, stage = .syncRun index)
    (stable : NativeReadyStorage last.current.ready.state (storage reached.2))
    (returnedKeeps : ∀ step ∈ stop.completed, ∀ before after,
      (primitives.checkpointStepUntilStop last.current.ready.state.session.directory
        fsync stop.next stop.manifest step).run before = .ok (.ok ()) after →
      opened.handle.contents after.2 opened.handle.phase = opened.handle.contents before.2 opened.handle.phase)
    (stoppedKeeps : opened.handle.contents reached.2 opened.handle.phase =
      opened.handle.contents stop.atIssue.2 opened.handle.phase) :
    NativeReachedExecutionPrefix opened.start.current (requests.map NativeExecutionInstruction.write) .checkpoint :=
  stop.terminalPrefix early stable returnedKeeps stoppedKeeps (trace.writeInstructions rfl) trace.common

end FreshBootstrapOpenHeap.Returned
end Alvoki.Storage.DiskSession
