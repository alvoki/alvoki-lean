import Alvoki.Storage.Disk.Proofs.Native.Execution.NativeInactiveSessionCalls
import Alvoki.Storage.Disk.Proofs.Native.Execution.NativePendingCloseRecovery

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

inductive NativePendingClientInstruction : Type 1 where
  | request (operation : NativeInactiveRequest)
  | close
  | lastReferenceDrop (event : LockReferenceDrop)

/-- The arguments and responses while the original write remains
pending. A reported reference drop marks the end of the held attempts. -/
inductive NativePendingClientEvent : Type 1 where
  | rejected (phase : NativeInactivePhase) (request : NativeInactiveRequest) (response : NativeInactiveResponse)
  | closeError (cause : IO.Error)
  | closed
  | lastReferenceDrop (event : LockReferenceDrop)

namespace NativePendingClientEvent

def instruction : NativePendingClientEvent → NativePendingClientInstruction
  | .rejected _ request _ => .request request
  | .closeError _ | .closed => .close
  | .lastReferenceDrop event => .lastReferenceDrop event

def error : NativePendingClientEvent → Option IO.Error
  | .closeError cause => some cause
  | _ => none

def rejectedAt (phase : NativeInactivePhase) (request : NativeInactiveRequest) : NativePendingClientEvent :=
  .rejected phase request (request.response phase)

end NativePendingClientEvent

/-- An ordinary rejected request or an actual failed close on the same
poisoned state. The caller supplies the original ordering. -/
inductive NativePoisonedClientCall {current : NativeReadPosition history log} (pending : NativePendingWrite current) :
    Type 1 where
  | request (request : NativeInactiveRequest)
  | close (reported : NativePendingCloseError pending)

namespace NativePoisonedClientCall

variable {current : NativeReadPosition history log} {pending : NativePendingWrite current}

def failedClose : NativePoisonedClientCall pending → Option (NativePendingCloseError pending)
  | .request _ => none
  | .close reported => some reported

def event : NativePoisonedClientCall pending → NativePendingClientEvent
  | .request operation => .rejectedAt .poisoned operation
  | .close reported => .closeError reported.cause

theorem errorsOrdered (calls : List (NativePoisonedClientCall pending)) :
    (calls.map event).filterMap NativePendingClientEvent.error = (calls.filterMap failedClose).map (·.cause) := by
  induction calls with
  | nil => rfl
  | cons call _ prior =>
    cases call <;> simp only [List.map_cons, List.filterMap_cons, event, failedClose,
      NativePendingClientEvent.error, NativePendingClientEvent.rejectedAt, prior]

end NativePoisonedClientCall

/-- Each returned result is tied to the corresponding request or native
close witness. Calls leave exactly the same cache, files and held
census, so no replay or receipt is added between two failing calls. -/
inductive NativePoisonedClientTrace {current : NativeReadPosition history log} (pending : NativePendingWrite current) :
    List (NativePoisonedClientCall pending) → List NativePendingClientEvent → Prop where
  | nil : NativePoisonedClientTrace pending [] []
  | request (returned : request.Returns pending.inactive response) (suffix : NativePoisonedClientTrace pending calls events) :
      NativePoisonedClientTrace pending (.request request :: calls) (.rejected .poisoned request response :: events)
  | close (reported : NativePendingCloseError pending)
      (returned : reported.close.report.run = .error reported.cause pending.poisoned)
      (suffix : NativePoisonedClientTrace pending calls events) :
      NativePoisonedClientTrace pending (.close reported :: calls) (.closeError reported.cause :: events)

theorem NativePendingWrite.executesClientCalls {current : NativeReadPosition history log} (pending : NativePendingWrite current)
    (calls : List (NativePoisonedClientCall pending)) : NativePoisonedClientTrace pending calls (calls.map (·.event)) := by
  induction calls with
  | nil => exact .nil
  | cons call _ suffix =>
    cases call with
    | request request => exact .request (request.rejects pending.inactive) suffix
    | close reported => exact .close reported reported.returns.1 suffix

/-- Rejected calls may be interleaved with earlier failed unlocks. After
a successful close they see the returned closed phase. After a last
failed unlock they can still see the poisoned phase before the reported
slot events retire its owner. -/
inductive NativePendingClientRecovery {current : NativeReadPosition history log}
    (pending : NativePendingWrite current) (input : FilePath) : Type 1 where
  | unlocked (before : List (NativePoisonedClientCall pending)) (close : NativePendingClose pending)
      (success : close.report.result = .ok ()) (after : List NativeInactiveRequest)
      (observe : pending.write.ReleasedMarkedReports input close.report.finished.descriptors
        (close.report.bindings (current.state.session.directory.file .lock)))
  | dropped (before : List (NativePoisonedClientCall pending)) (drop : NativePendingCloseReferenceDrop pending)
      (ordered : drop.prior = before.filterMap (·.failedClose)) (afterFailure : List NativeInactiveRequest)
      (observe : pending.write.ReleasedMarkedReports input drop.census
        (drop.failed.close.report.bindings (current.state.session.directory.file .lock)))

namespace NativePendingClientRecovery

variable {current : NativeReadPosition history log} {pending : NativePendingWrite current} {input : FilePath}

def calls : NativePendingClientRecovery pending input → List (NativePoisonedClientCall pending)
  | .unlocked before _ _ _ _ | .dropped before _ _ _ _ => before

def release : NativePendingClientRecovery pending input → NativePendingCloseRecovery pending input
  | .unlocked before close success _ observe => .unlocked ⟨before.filterMap (·.failedClose), close, success, observe⟩
  | .dropped _ drop _ _ observe => .dropped drop observe

def events : NativePendingClientRecovery pending input → List NativePendingClientEvent
  | .unlocked before _ _ after _ =>
    before.map (·.event) ++ [.closed] ++ after.map (NativePendingClientEvent.rejectedAt .closed)
  | .dropped before drop _ afterFailure _ =>
    before.map (·.event) ++ [.closeError drop.failed.cause] ++
      afterFailure.map (NativePendingClientEvent.rejectedAt .poisoned) ++ [.lastReferenceDrop drop.drop]

private theorem rejectedEventsHaveNoCloseError (phase : NativeInactivePhase) (requests : List NativeInactiveRequest) :
    (requests.map (NativePendingClientEvent.rejectedAt phase)).filterMap NativePendingClientEvent.error = [] := by
  induction requests with
  | nil => rfl
  | cons _ _ prior =>
    simpa only [List.map_cons, List.filterMap_cons, NativePendingClientEvent.rejectedAt, NativePendingClientEvent.error] using prior

theorem errorsInOrder (seen : NativePendingClientRecovery pending input) :
    seen.events.filterMap NativePendingClientEvent.error = seen.release.errors := by
  cases seen with
  | unlocked before close success after observe =>
    simp only [events, release, NativePendingCloseRecovery.errors, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil, NativePendingClientEvent.error, rejectedEventsHaveNoCloseError,
      NativePoisonedClientCall.errorsOrdered, List.append_nil]
  | dropped before drop ordered afterFailure observe =>
    simp only [events, release, NativePendingCloseRecovery.errors, NativePendingCloseReferenceDrop.attempts, ordered,
      List.filterMap_append, List.filterMap_cons, List.filterMap_nil, NativePendingClientEvent.error,
      rejectedEventsHaveNoCloseError, NativePoisonedClientCall.errorsOrdered, List.map_append, List.map_cons,
      List.map_nil, List.append_nil]

/-- The calls following the final close attempt use the phase it
actually leaves behind. They do not run after the reported slot drop. -/
def AfterClose : NativePendingClientRecovery pending input → Prop
  | .unlocked _ close success after _ =>
    NativeInactiveTrace (close.inactive success) after (after.map (NativeInactiveRequest.response .closed))
  | .dropped _ _ _ afterFailure _ =>
    NativeInactiveTrace pending.inactive afterFailure (afterFailure.map (NativeInactiveRequest.response .poisoned))

theorem rejectsAfterClose (seen : NativePendingClientRecovery pending input) : seen.AfterClose := by
  cases seen with
  | unlocked _ close success after _ => exact (close.inactive success).executes after
  | dropped _ _ _ afterFailure _ => exact pending.inactive.executes afterFailure

end NativePendingClientRecovery

structure NativePendingClientContinuation {current : NativeReadPosition history log}
    {pending : NativePendingWrite current} {input : FilePath} (seen : NativePendingClientRecovery pending input)
    (retained : List WAL.Write) (next : NativeReadPosition (history ++ retained) pending.submissions) : Prop where
  written : pending.write.returnedAt pending.cache
  calls : NativePoisonedClientTrace pending seen.calls (seen.calls.map (·.event))
  afterClose : seen.AfterClose
  diagnostics : seen.events.filterMap NativePendingClientEvent.error = seen.release.errors
  reopened : seen.release.Reopened retained next
  wholeOrNone : retained = [] ∨ retained = pending.write.failure.batch
  reads : next.reads = current.reads
  replay : InstalledClientReplay pending.submissions current.reads (history ++ retained) next.state.writer.installed
    next.state.session

/-- Read and update rejections, their failed close receipts and the
actual marked return form one continuation of the same uncertain write.
The selected history and previous read ledger come from the reopened
table. Only the original write contributes a pending submission. -/
theorem NativePendingWrite.recoversAfterClientCalls {current : NativeReadPosition history log}
    (pending : NativePendingWrite current) {input : FilePath} (seen : NativePendingClientRecovery pending input) :
    ∃ retained next, NativePendingClientContinuation seen retained next := by
  obtain ⟨retained, next, reopened⟩ := seen.release.reopens
  obtain ⟨wholeOrNone, reads⟩ := seen.release.frames reopened
  exact ⟨retained, next, pending.returned, pending.executesClientCalls seen.calls, seen.rejectsAfterClose,
    seen.errorsInOrder, reopened, wholeOrNone, reads, reads ▸ next.readPrefix.guardedReplay⟩

end Alvoki.Storage.DiskSession
