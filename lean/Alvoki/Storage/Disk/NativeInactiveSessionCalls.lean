import Alvoki.Storage.Disk.NativeExecutionOrdinaryClose
import Alvoki.Storage.Disk.NativeExecutionPendingClose
import Alvoki.Storage.Disk.NativeSnapshotExecution
import Alvoki.Storage.Disk.CheckpointPreflight

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair WAL.Boundary
open Sequential (SnapshotHandle SnapshotPin)

inductive NativeInactivePhase where
  | closed
  | poisoned

namespace NativeInactivePhase

def phase : NativeInactivePhase → Phase Installed
  | .closed => .closed
  | .poisoned => .poisoned

def error : NativeInactivePhase → IO.Error
  | .closed => IO.userError "database is closed"
  | .poisoned => IO.userError "publication failed; reopen the database"

end NativeInactivePhase

/-- The session still exists after close or a publication failure. Its
reached storage includes the actual cache, owner and descriptor census. -/
structure NativeInactiveSession (image : Type) where
  mode : NativeInactivePhase
  session : SegmentedSession
  reached : CachedCloseState CheckpointOpenHandle image
  sessionPhase : session.phase = mode.phase
  storagePhase : reached.phase = mode.phase

namespace NativeInactiveSession

abbrev FileEffects (image : Type) := CensusDirectoryCache × DescriptorInventory × image

def files (state : NativeInactiveSession image) : Phase Installed × LockedFileState (FileEffects image) :=
  (state.reached.phase, ⟨(state.reached.files.image.1, state.reached.descriptors, state.reached.files.image.2), state.reached.files.owners⟩)

def installed : EStateM IO.Error (NativeInactiveSession image) Installed :=
  fun state => state.session.phase.installed (m := EStateM IO.Error (NativeInactiveSession image)) state

theorem rejectsInstalled (state : NativeInactiveSession image) :
    installed state = .error state.mode.error state := by
  unfold installed
  rw [state.sessionPhase]
  cases state.mode <;> rfl

theorem rejectsFilePhase (state : NativeInactiveSession image) :
    (state.files.1.installed : Except IO.Error Installed) = .error state.mode.error := by
  change (state.reached.phase.installed : Except IO.Error Installed) = _
  rw [state.storagePhase]
  cases state.mode <;> rfl

end NativeInactiveSession

/-- Retain the arguments of each exercised public entry point, including
the issuing token of a snapshot and the plain or classified write API. -/
inductive NativeInactiveRequest : Type 1 where
  | snapshotControl (request : SnapshotUpdate α)
  | snapshotRead (issuer : Nat) (handle : SnapshotHandle) (request : SnapshotReadRequest α)
  | write (request : WriteRequest)
  | writeWithOutcome (request : WriteRequest)
  | checkpoint

inductive NativeInactiveResponse where
  | error (cause : IO.Error)
  | writeError (cause : DiskWriteError)

namespace NativeInactiveRequest

def response (mode : NativeInactivePhase) : NativeInactiveRequest → NativeInactiveResponse
  | .writeWithOutcome _ => .writeError (.rejected mode.error)
  | _ => .error mode.error

private abbrev SessionM (image : Type) := EStateM IO.Error (NativeInactiveSession image)

/-- The production snapshot-control schedule, interpreting its reached
phase and using the supplied release comparison and phase recorder. -/
def runControl (state : NativeInactiveSession image) (update : SnapshotUpdate α)
    (compare : Nat → SessionM image Bool) (record : Phase Installed → SessionM image Unit) : SessionM image α :=
  let installed := NativeInactiveSession.installed
  let issued := fun pin : SnapshotPin => (state.session.sessionRef, pin)
  match update with
  | .acquireAt sequence => acquireSnapshotWith installed record issued sequence
  | .acquire => acquireLatestWith installed (acquireSnapshotWith installed record issued)
  | .release issuer handle => releaseSnapshotWith installed (compare issuer) record handle
  | .advanceFloor floor => advanceFloorWith installed record floor

/-- Keep the precise typed error of the corresponding native schedule.
The entered state is also the returned state, before any later callback
can run. Unreached comparisons and publication calls are arbitrary. -/
def Returns (state : NativeInactiveSession image) : NativeInactiveRequest → NativeInactiveResponse → Prop
  | .snapshotControl request, .error cause =>
    ∀ compare record, runControl state request compare record state = .error cause state
  | .snapshotRead issuer handle request, .error cause =>
    ∀ compare : Nat → SessionM image Bool,
      readSnapshotWith NativeInactiveSession.installed (compare issuer) (request.read handle) state = .error cause state
  | .write request, .error cause =>
    ∀ lookup append stage sync rename,
      WriteRequest.plainResult (request.runReported state.session.directory lookup append stage sync rename state.files) =
        .error cause state.files
  | .writeWithOutcome request, .writeError cause =>
    ∀ lookup append stage sync rename,
      request.runReported state.session.directory lookup append stage sync rename state.files = .error cause state.files
  | .checkpoint, .error cause =>
    ∀ perform, runCheckpointWithEffects perform state.files = .error cause state.files
  | _, _ => False

private theorem rejectsWrite (state : NativeInactiveSession image) (request : WriteRequest)
    (lookup append stage sync rename) :
    request.runReported state.session.directory lookup append stage sync rename state.files =
      .error (.rejected state.mode.error) state.files := by
  cases request with
  | single key value => exact runSingleWrite_rejectedPhase state.rejectsFilePhase
  | batch rows =>
    cases exactFiles : state.files with
    | mk phase files =>
      have rejected := state.rejectsFilePhase
      rw [exactFiles] at rejected
      simp only [WriteRequest.runReported, runBatchWrite, writeBatchSchedule, Bind.bind, EStateM.bind, rejected]

/-- Inactive-phase rejection precedes even the empty-batch fast path,
snapshot token comparison, and checkpoint preparation. -/
theorem rejects (state : NativeInactiveSession image) (request : NativeInactiveRequest) :
    Returns state request (request.response state.mode) := by
  cases request with
  | snapshotControl update =>
    intro compare record
    cases update <;>
      simp only [runControl, acquireSnapshotWith, acquireLatestWith, releaseSnapshotWith, withLocalHandle,
        advanceFloorWith, Bind.bind, EStateM.bind, state.rejectsInstalled]
  | snapshotRead issuer handle request =>
    intro compare
    simp only [readSnapshotWith, withLocalHandle, Bind.bind, EStateM.bind, state.rejectsInstalled]
  | write request =>
    intro lookup append stage sync rename
    rw [rejectsWrite]
    rfl
  | writeWithOutcome request => exact rejectsWrite state request
  | checkpoint =>
    intro perform
    have rejected : CheckpointPreflight state.reached.phase (.error state.mode.error) := by
      rw [state.storagePhase]
      cases state.mode <;> constructor
    exact rejected.effect perform state.files.2

private theorem sameError {error state result : Type}
    {ran : EStateM.Result error state result} {cause expected : error} {reached : state}
    (first : ran = .error cause reached) (second : ran = .error expected reached) : cause = expected :=
  (EStateM.Result.error.inj (first.symm.trans second)).1

theorem responseExact (state : NativeInactiveSession image) {request : NativeInactiveRequest}
    {observed : NativeInactiveResponse} (returned : request.Returns state observed) :
    observed = request.response state.mode := by
  have expected := request.rejects state
  let lookup (_ : FilePath) : Except IO.Error IO.FS.Metadata := .error state.mode.error
  let write (_ : FilePath) (_ : ByteArray) : EStateM IO.Error (NativeInactiveSession.FileEffects image) Unit := pure ()
  let sync (_ : Array FilePath) : EStateM IO.Error (NativeInactiveSession.FileEffects image) Unit := pure ()
  let rename (_ _ : FilePath) : EStateM IO.Error (NativeInactiveSession.FileEffects image) Unit := pure ()
  cases request <;> cases observed <;> try exact False.elim returned
  case snapshotControl.error =>
    exact congrArg NativeInactiveResponse.error
      (sameError (returned (fun _ => pure false) (fun _ => pure ())) (expected (fun _ => pure false) (fun _ => pure ())))
  case snapshotRead.error =>
    exact congrArg NativeInactiveResponse.error
      (sameError (returned (fun _ => pure false)) (expected (fun _ => pure false)))
  case write.error =>
    exact congrArg NativeInactiveResponse.error
      (sameError (returned lookup write write sync rename) (expected lookup write write sync rename))
  case writeWithOutcome.writeError =>
    exact congrArg NativeInactiveResponse.writeError
      (sameError (returned lookup write write sync rename) (expected lookup write write sync rename))
  case checkpoint.error =>
    exact congrArg NativeInactiveResponse.error
      (sameError (returned (fun _ _ _ => pure ())) (expected (fun _ _ _ => pure ())))

end NativeInactiveRequest

/-- The prescribed argument list and exact error responses are threaded
together. Each call leaves the same reached native state for the next. -/
inductive NativeInactiveTrace (state : NativeInactiveSession image) :
    List NativeInactiveRequest → List NativeInactiveResponse → Prop where
  | nil : NativeInactiveTrace state [] []
  | cons (returned : request.Returns state response) (rest : NativeInactiveTrace state requests responses) :
      NativeInactiveTrace state (request :: requests) (response :: responses)

theorem NativeInactiveSession.executes (state : NativeInactiveSession image) (requests : List NativeInactiveRequest) :
    NativeInactiveTrace state requests (requests.map (NativeInactiveRequest.response state.mode)) := by
  induction requests with
  | nil => exact .nil
  | cons request _ rest => exact .cons (request.rejects state) rest

theorem NativeInactiveTrace.responsesExact (trace : NativeInactiveTrace state requests responses) :
    responses = requests.map (NativeInactiveRequest.response state.mode) := by
  induction trace with
  | nil => rfl
  | cons returned _ rest => rw [List.map_cons, ← rest, NativeInactiveRequest.responseExact state returned]

namespace NativePendingWrite

variable {current : NativeReadPosition history log}

def inactive (pending : NativePendingWrite current) : NativeInactiveSession WriteFiles :=
  ⟨.poisoned, pending.session, pending.poisoned, rfl, rfl⟩

/-- The exact poisoned write return starts the rejected calls. They
introduce no client read responses or extra write submissions. -/
theorem rejectsCalls (pending : NativePendingWrite current) (requests : List NativeInactiveRequest) :
    pending.write.returnedAt pending.cache ∧
    NativeInactiveTrace pending.inactive requests (requests.map (NativeInactiveRequest.response .poisoned)) ∧
    ∃ selected, (selected = history ∨ selected = history ++ pending.write.failure.batch) ∧
      PendingClientReplay pending.submissions current.reads selected ∧
      ∀ read ∈ current.reads, read.BoundedBy selected.length := by
  obtain ⟨selected, branch, _, replay, bounded⟩ := pending.selectsAtReturn
  exact ⟨pending.returned, pending.inactive.executes requests, selected, branch, replay, bounded⟩

end NativePendingWrite

namespace NativeReadyClose

variable {state : NativeReadyState}

def inactive (close : NativeReadyClose state) (unlocked : close.report.result = .ok ()) :
    NativeInactiveSession FileImage where
  mode := .closed
  session := close.session
  reached := close.report.finished
  sessionPhase := by simp only [session, reached, unlocked, CachedCloseReports.finished]; rfl
  storagePhase := rfl

end NativeReadyClose

/-- A successful ordinary close supplies the concrete closed endpoint.
All subsequent rejected calls retain the same selected files and the
prior acknowledgements and recorded responses. -/
theorem NativeReadPosition.rejectsCallsAfterClose (current : NativeReadPosition history log)
    (close : NativeReadyClose current.state) (unlocked : close.report.result = .ok ())
    (requests : List NativeInactiveRequest) :
    close.report.run = .ok () close.report.finished ∧
    NativeInactiveTrace (close.inactive unlocked) requests (requests.map (NativeInactiveRequest.response .closed)) ∧
    PendingClientReplay log current.reads history ∧ ∀ read ∈ current.reads, read.BoundedBy history.length := by
  have returned := (current.closes close).returned
  simp only [NativeReadyClose.Returned, unlocked, NativeReadyClose.reached] at returned
  exact ⟨returned.1, (close.inactive unlocked).executes requests, current.readPrefix.refines.2.2,
    current.readPrefix.readsBounded⟩

namespace NativePendingClose

variable {current : NativeReadPosition history log} {pending : NativePendingWrite current}

def inactive (close : NativePendingClose pending) (unlocked : close.report.result = .ok ()) :
    NativeInactiveSession WriteFiles where
  mode := .closed
  session := close.session
  reached := close.report.finished
  sessionPhase := by simp only [session, reached, unlocked, CachedCloseReports.finished]; rfl
  storagePhase := rfl

/-- Closing a poisoned writer changes the phase error seen by its
original handles. Its exact failed bytes and one pending receipt remain. -/
theorem rejectsCalls (close : NativePendingClose pending) (unlocked : close.report.result = .ok ())
    (requests : List NativeInactiveRequest) :
    pending.write.returnedAt pending.cache ∧ close.report.run = .ok () close.report.finished ∧
    NativeInactiveTrace (close.inactive unlocked) requests (requests.map (NativeInactiveRequest.response .closed)) ∧
    ∃ selected, (selected = history ∨ selected = history ++ pending.write.failure.batch) ∧
      PendingClientReplay pending.submissions current.reads selected ∧
      ∀ read ∈ current.reads, read.BoundedBy selected.length := by
  have returned := close.returns
  simp only [unlocked, NativePendingClose.reached] at returned
  obtain ⟨selected, branch, _, replay, bounded⟩ := close.selectsAtReturn
  exact ⟨pending.returned, returned.1, (close.inactive unlocked).executes requests, selected, branch, replay, bounded⟩

end NativePendingClose

end Alvoki.Storage.DiskSession
