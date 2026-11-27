import Alvoki.Storage.Disk.Proofs.Read.ClientReadTrace

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WAL.Boundary WalSegmentCommit WalSegmentRepair

/-- The arguments of either native write entry point. Single writes and
batches use different preflight schedules and share one publication. -/
inductive WriteRequest where
  | single (key : UInt64) (value : Option UInt64)
  | batch (rows : List (UInt64 × Option UInt64))

def WriteRequest.rows : WriteRequest → List (UInt64 × Option UInt64)
  | .single key value => [(key, value)]
  | .batch rows => rows

/-- Interpret the production schedule at the reported callbacks. -/
def WriteRequest.runReported {image : Type} (request : WriteRequest) (directory : DiskDirectory)
    (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    (append stage : FilePath → ByteArray → EStateM IO.Error image Unit)
    (sync : Array FilePath → EStateM IO.Error image Unit) (rename : FilePath → FilePath → EStateM IO.Error image Unit) :
    EStateM DiskWriteError (Phase Installed × LockedFileState image) UInt64 :=
  match request with
  | .single key value =>
    runSingleWrite directory key value lookup
      (fun state event count => commitAt directory state.activeFirst event count append stage sync rename)
  | .batch rows => runBatchWrite directory rows lookup append stage sync rename

theorem WriteRequest.runReported_eq_batch {image : Type} {directory : DiskDirectory}
    {descriptor : Nat} {writer : SegmentedWriterState} (ready : writer.RetainedReady directory descriptor)
    (request : WriteRequest) (before : LockedFileState image)
    (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    (append stage : FilePath → ByteArray → EStateM IO.Error image Unit)
    (sync : Array FilePath → EStateM IO.Error image Unit) (rename : FilePath → FilePath → EStateM IO.Error image Unit) :
    request.runReported directory lookup append stage sync rename (.ready writer.installed, before) =
    runBatchWrite directory request.rows lookup append stage sync rename (.ready writer.installed, before) := by
  cases request with
  | single key value => exact runSingleWrite_eq_runBatchWrite_singleton ready key value before lookup append stage sync rename
  | batch rows => rfl

abbrev WriteCallState (handle : Type) := Phase Installed × LockedFileState (Cache handle × WriteFiles)

namespace WriteRequest

variable {directory : DiskDirectory} {before : SegmentedWriterState} {handle : Type}

/-- Keep the value or original IO diagnostic and the exact reached state. -/
def plainResult {state value : Type} :
    EStateM.Result DiskWriteError state value → EStateM.Result IO.Error state value
  | .ok value reached => .ok value reached
  | .error outcome reached => .error outcome.cause reached

abbrev readyCall (before : SegmentedWriterState) (cache : Cache handle) : WriteCallState handle :=
  (.ready before.installed, ⟨(cache, WriteFiles.initial before.history
    (before.files.directory.staged .walBoundary)), before.owners⟩)

/-- The callbacks of one invocation, retaining the cache at entry. -/
structure Calls (handle : Type) where
  cache : Cache handle
  lookup : FilePath → Except IO.Error IO.FS.Metadata
  append : FilePath → ByteArray → EStateM IO.Error (Cache handle × WriteFiles) Unit
  stage : FilePath → ByteArray → EStateM IO.Error (Cache handle × WriteFiles) Unit
  sync : Array FilePath → EStateM IO.Error (Cache handle × WriteFiles) Unit
  rename : FilePath → FilePath → EStateM IO.Error (Cache handle × WriteFiles) Unit

def Calls.run (calls : Calls handle) (request : WriteRequest) (directory : DiskDirectory)
    (before : SegmentedWriterState) : EStateM.Result DiskWriteError (WriteCallState handle) UInt64 :=
  request.runReported directory calls.lookup calls.append calls.stage calls.sync calls.rename (readyCall before calls.cache)

/-- Interpret the plain IO entry points using the same reached result.
Their native equalities `DiskTable.write_eq_adaptOutcome` and
`DiskTable.writeBatch_eq_adaptOutcome` erase only the diagnostic's tag. -/
def Calls.runPlain (calls : Calls handle) (request : WriteRequest) (directory : DiskDirectory)
    (before : SegmentedWriterState) : EStateM.Result IO.Error (WriteCallState handle) UInt64 :=
  plainResult (calls.run request directory before)

def Calls.ofSuccess {report : SegmentedBatchAppendReport directory before} (seen : ObservedBatchWrite report handle) :
    Calls handle :=
  ⟨seen.cache, seen.guard.lookup, seen.append, seen.stage, seen.sync, seen.rename⟩

def Calls.ofFailure {failure : SegmentedBatchFailure directory before} (seen : ObservedBatchFailure failure handle) :
    Calls handle :=
  ⟨seen.cache, seen.guard.lookup, seen.append, seen.stage, seen.sync, seen.rename⟩

/-- Evidence for the reached branch of a returned write. A rejection
supplies the failing preflight check. Commit branches use the shared
publication reports for their exact returned states. -/
inductive ReturnedReports (request : WriteRequest) (directory : DiskDirectory) (before : SegmentedWriterState)
    (handle : Type) : Calls handle → Prop where
  | rejected {calls : Calls handle} {cause : IO.Error}
      (guard : BatchPreflightRejection directory before.installed request.rows calls.lookup cause) :
      ReturnedReports request directory before handle calls
  | empty {calls : Calls handle} (empty : request.rows = []) :
      ReturnedReports request directory before handle calls
  | acknowledged (report : SegmentedBatchAppendReport directory before)
      (observed : ObservedBatchWrite report handle) (rows : request.rows = report.rows) :
      ReturnedReports request directory before handle (Calls.ofSuccess observed)
  | unknown (failure : SegmentedBatchFailure directory before)
      (observed : ObservedBatchFailure failure handle) (rows : request.rows = failure.rows) :
      ReturnedReports request directory before handle (Calls.ofFailure observed)

/-- The client continuation of a returned write. An unknown commit keeps
the existing client trace and the pending batch at the exact poisoned
endpoint, so a later recovery may account for it without an early success
assumption. -/
inductive ClientReturn (request : WriteRequest) (directory : DiskDirectory) (initialDescriptor : Nat)
    (initial : SegmentedWriterState) (allowCollection : Bool) (log : List DatabaseSubmissions)
    (reads : List RecordedSnapshotRead) (writer : Nat) (before : SegmentedWriterState) (handle : Type)
    (calls : Calls handle) : EStateM.Result DiskWriteError (WriteCallState handle) UInt64 → Prop where
  | rejected (cause : IO.Error) :
      ClientReturn request directory initialDescriptor initial allowCollection log reads writer before handle calls
        (.error (.rejected cause) (readyCall before calls.cache))
  | empty (empty : request.rows = []) :
      ClientReturn request directory initialDescriptor initial allowCollection log reads writer before handle calls
        (.ok before.installed.table.committed (readyCall before calls.cache))
  | acknowledged (report : SegmentedBatchAppendReport directory before)
      (rows : request.rows = report.rows) (target : WalSegmentRepair.Target) (cacheAfter : Cache handle)
      (continued : SegmentedClientReadTrace directory initialDescriptor initial allowCollection
        (log ++ [.acknowledgedBatch report.batch]) reads writer (report.next target)) :
      ClientReturn request directory initialDescriptor initial allowCollection log reads writer before handle calls
        (.ok report.table.committed (.ready (report.next target).installed,
          ⟨(cacheAfter, report.written), (report.next target).owners⟩))
  | unknown (failure : SegmentedBatchFailure directory before)
      (observed : ObservedBatchFailure failure handle) (sameCalls : calls = Calls.ofFailure observed)
      (rows : request.rows = failure.rows) (cacheAfter : Cache handle) :
      ClientReturn request directory initialDescriptor initial allowCollection log reads writer before handle calls
        (.error (.commitUnknown failure.cause) (.poisoned, ⟨(cacheAfter, failure.failed), before.owners⟩))

/-- All returned write outcomes use the same observed cache and callback
schedule. Only a confirmed nonempty commit advances the ready client
ledger here. An uncertain batch remains attached to its poisoned state. -/
theorem ReturnedReports.refinesClient {request : WriteRequest} {calls : Calls handle}
    (reported : ReturnedReports request directory before handle calls)
    (trace : SegmentedClientReadTrace directory initialDescriptor initial allowCollection log reads writer before)
    (initialReady : initial.RetainedReady directory initialDescriptor) :
    ClientReturn request directory initialDescriptor initial allowCollection log reads writer before handle calls
      (calls.run request directory before) := by
  have ready := (trace.writes.preservesRetained initialReady).1
  have shared (actual : Calls handle) :
      actual.run request directory before =
        runBatchWrite directory request.rows actual.lookup actual.append actual.stage actual.sync actual.rename
          (readyCall before actual.cache) :=
    request.runReported_eq_batch ready _ _ _ _ _ _
  cases reported with
  | rejected guard =>
    rw [shared, guard.run]
    exact .rejected _
  | empty empty =>
    rw [shared, empty, runBatchWrite_empty]
    exact .empty empty
  | acknowledged report observed rows =>
    obtain ⟨target, cacheAfter, returned, _, added⟩ :=
      (SegmentedBatchDatabaseTrace.start (directory := directory) (initialDescriptor := writer) (initial := before)
        (allowCollection := allowCollection)).acknowledgeObservedBatch ready report observed
    rw [shared, rows]
    simp only [Calls.ofSuccess]
    change runBatchWrite directory report.rows _ _ _ _ _ (readyCall before observed.cache) = _ at returned
    rw [returned]
    exact .acknowledged report rows target cacheAfter (.advance trace added)
  | unknown failure observed rows =>
    obtain ⟨cacheAfter, returned⟩ := observed.commitUnknown
    rw [shared, rows]
    simp only [Calls.ofFailure]
    simp only [← ready.directoryFiles] at returned
    change runBatchWrite directory failure.rows _ _ _ _ _ (readyCall before observed.cache) = _ at returned
    rw [returned]
    exact .unknown failure observed rfl rows cacheAfter

/-- The same client continuation explains a plain IO return. The
classified witness carries the reached phase and file state and still
distinguishes a rejected write from an uncertain publication. -/
theorem ReturnedReports.refinesPlainClient {request : WriteRequest} {calls : Calls handle}
    (reported : ReturnedReports request directory before handle calls)
    (trace : SegmentedClientReadTrace directory initialDescriptor initial allowCollection log reads writer before)
    (initialReady : initial.RetainedReady directory initialDescriptor) :
    ∃ outcome, calls.runPlain request directory before = plainResult outcome ∧
      ClientReturn request directory initialDescriptor initial allowCollection log reads writer before handle calls outcome :=
  ⟨calls.run request directory before, rfl, reported.refinesClient trace initialReady⟩

end WriteRequest

/-- Resume an unknown commit from the exact returned cache, files and
owner. The later admitted open contributes one uncertain group to the
same client ledger, regardless of which allowed marker survives. -/
theorem SegmentedClientReadTrace.reopenAfterReturnedWrite {files handle : Type}
    {directory : DiskDirectory} {input : FilePath} {retry : LockedFileState WalSegmentRepair.FileImage}
    {before : SegmentedWriterState}
    (trace : SegmentedClientReadTrace directory initialDescriptor initial allowCollection log readLog writer before)
    (initialReady : initial.RetainedReady directory initialDescriptor)
    (request : WriteRequest) (failure : SegmentedBatchFailure directory before)
    (observed : ObservedBatchFailure failure handle) (rows : request.rows = failure.rows)
    (cacheAfter : Cache handle)
    (returned : (WriteRequest.Calls.ofFailure observed).run request directory before =
      .error (.commitUnknown failure.cause) (.poisoned, ⟨(cacheAfter, failure.failed), before.owners⟩))
    (release : SegmentedFailureRelease writer)
    (attempts : BoundedReopenTrace directory (BatchRetryTarget before.history failure.batch before.wal.active.first)
      failure.released retry)
    (reads : BatchCutReopenObservations directory before failure.batch files input retry) :
    ∃ descriptor after,
      let poisoned : WriteCallState handle := (.poisoned, ⟨(cacheAfter, failure.failed), before.owners⟩)
      release.Observed (directory := directory) poisoned ⟨poisoned.2.image, failure.released.owners⟩ ∧
      AdmittedBatchCutReopen (files := files) directory before failure.batch input retry descriptor after ∧
      SegmentedClientReadTrace directory initialDescriptor initial allowCollection
        (log ++ [.uncertainBatch failure.batch]) readLog descriptor after := by
  have ready := (trace.writes.preservesRetained initialReady).1
  obtain ⟨descriptor, after, endpoint⟩ := observed.reopensAdmitted ready release attempts reads
  obtain ⟨actualCache, batchReturned, released⟩ := endpoint.returned
  have fromSameWrite := request.runReported_eq_batch ready
    (WriteRequest.readyCall (handle := handle) before observed.cache).2
    observed.guard.lookup observed.append observed.stage observed.sync observed.rename
  change request.runReported directory observed.guard.lookup observed.append observed.stage observed.sync observed.rename
    (WriteRequest.readyCall before observed.cache) = _ at fromSameWrite
  rw [rows] at fromSameWrite
  simp only [← ready.directoryFiles] at batchReturned
  have sameEndpoint := (EStateM.Result.error.inj ((fromSameWrite.trans batchReturned).symm.trans returned)).2
  have sameCache := congrArg (fun (state : WriteCallState handle) => state.2.image.1) sameEndpoint
  change actualCache = cacheAfter at sameCache
  subst cacheAfter
  exact ⟨descriptor, after, released, endpoint.installation,
    .advance trace (.batchErrorAdmitted .start failure observed endpoint)⟩

end Alvoki.Storage.DiskSession
