import Alvoki.Storage.Disk.Proofs.Bootstrap.BootstrapExecution
import Alvoki.Storage.Disk.Proofs.Bootstrap.BootstrapZeroCreateRetry
import Alvoki.Storage.Disk.Proofs.Bootstrap.BootstrapCreateErrorLineage
import Alvoki.Storage.Disk.NativeReadRecoveryTrace
import Alvoki.Storage.Disk.NativeReadyCheckpoint
import Alvoki.Storage.Disk.NativeReadyWalCollection
import Alvoki.Storage.Disk.NativeCoveredWalUnlinkReopen
import Alvoki.Storage.Disk.NativeCoveredWalDirectoryReopen
import Alvoki.Storage.Disk.NativeExecutionClose
import Alvoki.Storage.Disk.NativeReadyCloseRetries
import Alvoki.Storage.Disk.Proofs.Recovery.NativeCloseMarkedBarrierReopen
import Alvoki.Storage.Disk.NativePendingCloseRecovery
import Alvoki.Storage.Disk.NativePendingClientRecovery
import Alvoki.Storage.Disk.NativePendingWriteProcessExit
import Alvoki.Storage.Disk.NativeReadyProcessExit
import Alvoki.Storage.Disk.NativeUncertainExecution
import Alvoki.Storage.Disk.NativeCollectionErrorReopen
import Alvoki.Storage.Disk.NativeWritePreflight
import Alvoki.Storage.Disk.NativeSnapshotExecution
import Alvoki.Storage.Disk.NativeExplicitSnapshotRead
import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointErrorReopen
import Alvoki.Storage.Disk.NativeEarlyCheckpointReopen
import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointRunFileReopen
import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointManifestSyncReopen
import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointManifestRenameReboot
import Alvoki.Storage.Disk.NativeCoveredWalUnlinkErrorReopen
import Alvoki.Storage.Disk.NativeCoveredWalUnlinkErrorPowerLoss
import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointPreflight
import Alvoki.Storage.Disk.NativeWalPlanningQuery
import Alvoki.Storage.Disk.Proofs.Rotation.NativeReadyRotation
import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointErrorPowerLoss
import Alvoki.Storage.Disk.NativeObsoleteRunCollection
import Alvoki.Storage.Disk.NativeRunMaintenance
import Alvoki.Storage.Disk.NativeRunMaintenanceReopen
import Alvoki.Storage.Disk.NativeMarkerInterruptionReopen
import Alvoki.Storage.Disk.NativeObsoleteRunBarrierError
import Alvoki.Storage.Disk.Proofs.Recovery.NativeRejectedOpenAlignedRecovery
import Alvoki.Storage.Disk.NativeContendedOpen
import Alvoki.Storage.Disk.NativeClassifiedWriteAck
import Alvoki.Storage.Disk.Proofs.Recovery.NativeUncertainStageRetry
import Alvoki.Storage.Disk.NativeUncertainWritePowerLoss
import Alvoki.Storage.Disk.NativePendingCheckpointRecovery
import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointRunDirectoryReboot
import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointRunFileReboot
import Alvoki.Storage.Disk.NativeFirstAppendExitReopen
import Alvoki.Storage.Disk.NativeFirstAppendPowerLoss
import Alvoki.Storage.Disk.NativeInterruptedCloseReopen
import Alvoki.Storage.Disk.NativePoisonedCloseReopen
import Alvoki.Storage.Disk.NativeObsoleteRunUnlinkCut
import Alvoki.Storage.Disk.NativeObsoleteRunUnlinkPowerLoss
import Alvoki.Storage.Disk.NativeObsoleteRunUnlinkRetries
import Alvoki.Storage.Disk.Proofs.Rotation.NativeRotationErrorReopen
import Alvoki.Storage.Disk.Proofs.Rotation.NativeRotationErrorPowerLoss

import Alvoki.Storage.Disk.Proofs.Recovery.NativeFinalizedOpenRetries
import Alvoki.Storage.Disk.NativeContendedAliasAdmission

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open Sequential (SnapshotHandle)

/-- The reached session, its committed WAL and the client requests that
account for it. A local read prefix preserves the corresponding ledger. -/
structure NativeExecutionPosition where
  history : List WAL.Write
  submissions : List DatabaseSubmissions
  ready : NativeReadPosition history submissions

/-- One reported stop and its selected reboot before manifest publication.
The issued run fsync and first directory fsync keep their own observations. -/
inductive NativeEarlyCheckpointReboot (state : NativeReadyState) : Type 1 where
  | file {image : Type} {cut : CheckpointPowerCut state.session.directory state.writer}
      {stop : NativeCheckpointRunFileStop (image := image) state cut}
      (reboot : NativeCheckpointRunFileReboot stop)
  | directory {image : Type} {cut : CheckpointPowerCut state.session.directory state.writer}
      {stop : NativeCheckpointRunDirectoryStop (image := image) state cut}
      (reboot : NativeCheckpointRunDirectoryReboot stop)

namespace NativeEarlyCheckpointReboot

def cut : NativeEarlyCheckpointReboot state → CheckpointPowerCut state.session.directory state.writer
  | .file (cut := cut) _ | .directory (cut := cut) _ => cut

def stage : NativeEarlyCheckpointReboot state → CheckpointPublication.Step
  | .file (stop := stop) _ => .syncRun stop.effect.index
  | .directory _ => .syncRunsDirectory

theorem issuedStage (seen : NativeEarlyCheckpointReboot state) : seen.cut.current = seen.stage := by
  cases seen with
  | @file _ _ stop _ => exact stop.issue.current
  | @directory _ _ stop _ => exact stop.current

def tookEffect (seen : NativeEarlyCheckpointReboot state) : Bool := seen.cut.tookEffect

def observed (seen : NativeEarlyCheckpointReboot state) (valid : state.Valid) : NativeReadyQuietCrash state :=
  match seen with
  | .file reboot => reboot.observed valid
  | .directory reboot => reboot.observed valid

end NativeEarlyCheckpointReboot

inductive NativeExecutionEvent : Type 1 where
  | readOrRestart (event : NativeReadRecoveryEvent)
  | acknowledged (request : WriteRequest) (batch : List WAL.Write)
  | checkpoint
  | checkpointRejected (error : IO.Error)
  | checkpointErrorRecovered (input : FilePath) (error : IO.Error)
  | checkpointRunFileErrorRecovered (input : FilePath) (index : Nat) (error : IO.Error)
  | checkpointManifestSyncErrorRecovered (input : FilePath) (error : IO.Error)
  | firstCheckpointBarrierErrorRecovered (input : FilePath) (error : IO.Error)
  | checkpointCrashRecovered (input : FilePath) (error : IO.Error) (manifest : Option ByteArray)
  | checkpointManifestRenameCrashRecovered (input : FilePath) (error : IO.Error) (manifest : Option ByteArray)
  | interruptedCheckpointRecovered (input : FilePath) (manifest : Option ByteArray)
  | interruptedEarlyCheckpointRecovered (input : FilePath) (stage : CheckpointPublication.Step)
      (effective : Bool) (manifest : Option ByteArray)
  | collectCoveredWal
  | coveredWalCollectionRejected (error : IO.Error)
  | interruptedCoveredWalUnlinkRecovered (input : FilePath)
  | coveredWalUnlinkErrorCrashRecovered (input : FilePath) (error : IO.Error)
  | interruptedCoveredWalDirectoryRecovered (input : FilePath) (syncEffective : Bool)
  | walCollectionPlan (result : Except IO.Error (List Nat))
  | rotatedWal
  | rotationErrorRecovered (input : FilePath) (error : IO.Error)
  | rotationCrashRecovered (input : FilePath) (error : IO.Error) (activeFirst : Nat)
  | interruptedRotationRecovered (input : FilePath) (activeFirst : Nat)
  | collectedObsoleteRuns (held : List UInt64)
  | obsoleteRunCollectionError (held : List UInt64) (error : IO.Error)
  | interruptedRunUnlinkRecovered (held : List UInt64) (input : FilePath)
  | collectedObsoleteRunsAfterRetries (held : List UInt64) (errors : List IO.Error)
  | contendedOpenRejected (input : FilePath) (error : IO.Error)
  | markedBarrierRetriesRecovered (input : FilePath) (attempts : List NativeMarkedBarrierEvent)
  | rejectedOpenSequenceRecovered (inputs : List FilePath) (input : FilePath) (errors : List IO.Error)
  | rewroteRun (request : RunMaintenance) (result : Bool)
  | rewroteRunCheckpointAndReopened (request : RunMaintenance) (input : FilePath)
  | closedAndReopened (input : FilePath) (result : Except IO.Error Unit)
  | closedAfterRetries (input : FilePath) (errors : List IO.Error) (result : Except IO.Error Unit)
  | readyExitRecovered (input : FilePath) (process : Nat)
  | interruptedCloseRecovered (input : FilePath) (unlockEffective : Bool)
  | uncertainWriteRecovered (request : WriteRequest) (input : FilePath) (cause : IO.Error)
      (attempted retained : List WAL.Write)
  | uncertainWriteCrashRecovered (request : WriteRequest) (input : FilePath) (cause : IO.Error)
      (attempted retained : List WAL.Write)
  | uncertainWriteStageRetryRecovered (request : WriteRequest) (failedInput input : FilePath)
      (writeCause openDiagnostic : IO.Error) (attempted : List WAL.Write)
  | uncertainWriteInterruptedCloseRecovered (request : WriteRequest) (input : FilePath) (cause : IO.Error)
      (attempted retained : List WAL.Write)
  | uncertainWriteCloseRetriesRecovered (request : WriteRequest) (input : FilePath) (cause : IO.Error)
      (release : PendingCloseRelease) (errors : List IO.Error) (attempted retained : List WAL.Write)
  | uncertainWriteExitRecovered (request : WriteRequest) (input : FilePath) (cause : IO.Error)
      (rejected : List NativeInactiveRequest) (process : Nat) (attempted retained : List WAL.Write)
  | uncertainWriteClientCallsRecovered (request : WriteRequest) (input : FilePath) (cause : IO.Error)
      (calls : List NativePendingClientEvent) (attempted retained : List WAL.Write)
  | interruptedAppendRecovered (request : WriteRequest) (input : FilePath) (attempted : List WAL.Write)
  | interruptedAppendRetriesRecovered (request : WriteRequest) (errors : List (FilePath × IO.Error))
      (input : FilePath) (attempted : List WAL.Write)
  | interruptedAppendContendedRetriesRecovered (request : WriteRequest) (busy : FilePath × IO.Error)
      (errors : List (FilePath × IO.Error)) (input : FilePath) (attempted : List WAL.Write)
  | interruptedAppendCrashRecovered (request : WriteRequest) (input : FilePath) (attempted : List WAL.Write)
  | interruptedMarkerRecovered (request : WriteRequest) (input : FilePath) (attempted retained : List WAL.Write)
  | collectionErrorRecovered (input : FilePath) (error : IO.Error)
  | coveredWalUnlinkErrorRecovered (input : FilePath) (error : IO.Error)
  | writePreflight (request : WriteRequest) (result : Except IO.Error UInt64)
  | snapshotControl (request : SnapshotUpdate α) (result : Except IO.Error α)
  | snapshotHandleRead (issuer : Nat) (handle : SnapshotHandle) (request : SnapshotReadRequest α)
      (result : Option α) (recorded : RecordedSnapshotRead)

/-- Record the issued checkpoint step and its reported effect without any
ordinary return from the interrupted checkpoint. -/
def NativeEarlyCheckpointReboot.event (seen : NativeEarlyCheckpointReboot state) (input : FilePath) :
    NativeExecutionEvent :=
  .interruptedEarlyCheckpointRecovered input seen.stage seen.tookEffect state.writer.target.pair.manifest

namespace NativeExecutionEvent

def writes : NativeExecutionEvent → List WAL.Write
  | .acknowledged _ batch => batch
  | .uncertainWriteRecovered _ _ _ _ retained | .uncertainWriteCrashRecovered _ _ _ _ retained
  | .uncertainWriteInterruptedCloseRecovered _ _ _ _ retained | .interruptedMarkerRecovered _ _ _ retained
  | .uncertainWriteCloseRetriesRecovered _ _ _ _ _ _ retained
  | .uncertainWriteClientCallsRecovered _ _ _ _ _ retained
  | .uncertainWriteExitRecovered _ _ _ _ _ _ retained => retained
  | _ => []

def submissions : NativeExecutionEvent → List DatabaseSubmissions
  | .acknowledged _ batch => [.acknowledgedBatch batch]
  | .uncertainWriteRecovered _ _ _ attempted _ | .uncertainWriteCrashRecovered _ _ _ attempted _
  | .uncertainWriteInterruptedCloseRecovered _ _ _ attempted _ | .interruptedAppendRecovered _ _ attempted
  | .interruptedMarkerRecovered _ _ attempted _ | .interruptedAppendCrashRecovered _ _ attempted
  | .interruptedAppendRetriesRecovered _ _ _ attempted
  | .interruptedAppendContendedRetriesRecovered _ _ _ _ attempted
  | .uncertainWriteStageRetryRecovered _ _ _ _ _ attempted
  | .uncertainWriteCloseRetriesRecovered _ _ _ _ _ attempted _
  | .uncertainWriteClientCallsRecovered _ _ _ _ attempted _
  | .uncertainWriteExitRecovered _ _ _ _ _ attempted _ =>
    [.uncertainBatch attempted]
  | _ => []

def reads : NativeExecutionEvent → List RecordedSnapshotRead
  | .readOrRestart event => event.responses
  | .snapshotHandleRead _ _ _ _ recorded => [recorded]
  | _ => []

def uncertainBatchWhole : NativeExecutionEvent → Prop
  | .uncertainWriteRecovered _ _ _ attempted retained | .uncertainWriteCrashRecovered _ _ _ attempted retained
  | .uncertainWriteInterruptedCloseRecovered _ _ _ attempted retained | .interruptedMarkerRecovered _ _ attempted retained
  | .uncertainWriteCloseRetriesRecovered _ _ _ _ _ attempted retained
  | .uncertainWriteClientCallsRecovered _ _ _ _ attempted retained
  | .uncertainWriteExitRecovered _ _ _ _ _ attempted retained =>
    retained = [] ∨ retained = attempted
  | _ => True

/-- Select the receipt for the same interrupted write and admitted
retry sequence, keeping an earlier contended diagnostic when present. -/
def appendRetryRecovery (request : WriteRequest) (errors : List (FilePath × IO.Error)) (input : FilePath)
    (attempted : List WAL.Write) : Option (FilePath × IO.Error) → NativeExecutionEvent
  | none => .interruptedAppendRetriesRecovered request errors input attempted
  | some busy => .interruptedAppendContendedRetriesRecovered request busy errors input attempted

end NativeExecutionEvent

/-- The observed checkpoint and close start from the successful
rewrite's exact table and published run binding. -/
structure NativeRunMaintenanceReopenObservation (state : NativeReadyState) (request : RunMaintenance) (input : FilePath) where
  rewritten : PackedTable
  updated : request.update state.writer.installed.table = some rewritten
  image : Type
  attempt : SegmentedCheckpointReport state.session.directory (state.withTable rewritten).writer
  reports : CheckpointCompletionReports (CensusDirectoryCache × image) attempt
  checkpoint : NativeReadyCheckpoint (state.withTable rewritten) reports
  binding : checkpoint.RunBinding request.index
  observe : ∀ writer, checkpoint.Completed writer →
    ∃ close : NativeCloseReopenObservation (checkpoint.next writer) input,
      close.close.report.result = .ok () ∧
      let path := state.session.directory.file (.run attempt.prepared.generation request.index)
      close.files.names path = checkpoint.bindings reports.observed.completed.2 path

private def snapshotControlResult : SnapshotUpdate.Outcome α → Except IO.Error α
  | .unchanged value | .updated value _ => .ok value
  | .failed cause => .error cause

/-- A successful maintenance operation continues the same committed
history and read ledger from its exact reached ready state. -/
def NativeReadPosition.afterMaintenance (current : NativeReadPosition history log) (next : NativeReadyState)
    (valid : next.Valid) (historyEq : next.writer.history = history) : NativeReadPosition history log :=
  ⟨.ok next.session (next.census, next.files), next, next, current.reads,
    .installed rfl valid historyEq current.readPrefix.refines.2.2 current.readPrefix.readsBounded⟩

/-- The reported close releases the input for the failed open sequence.
Each retry starts from the preceding inventory and file state. -/
structure NativeCloseMarkedBarrierObservation (state : NativeReadyState) (inputs : List FilePath) (input : FilePath) where
  close : NativeReadyClose state
  success : close.report.result = .ok ()
  events : List NativeMarkedBarrierEvent
  inputsInOrder : events.map (·.input) = inputs
  after : CensusOpenState
  lineage : NativeMarkedBarrierRetries state.session.directory
    (state.census.inode state.owner.description) (state.census.inode state.directorySlot.description)
    state.writer.history state.writer.published state.writer.checkpoint
    (close.report.finished.descriptors, state.releasedFiles) events after true
  files : NativeCloseFiles state
  names : ∀ path, state.crashPath path → files.names path = close.report.bindings path
  observe : ∀ plan : ClosedReadyReopenLayout state.writer state.releasedFiles,
    ∀ selected : SelectedIntegrityCheckpoint state.writer.published.durable
      state.releasedFiles.image.directory.active.manifest state.writer.checkpoint,
      Nonempty (NativeCloseAlignedReads files input after.1 plan.layout selected)

/-- The files released by the stopped append enter the same diagnostic
lineage and selected healthy open for direct or contended access. -/
structure NativeFirstAppendRetryRecovery (current : NativeExecutionPosition) {heap : Type}
    {prepared : NativeReadyWritePreparation current.ready.state} (stop : NativeFirstAppendStop prepared)
    (exited : NativeFirstAppendExit stop) (view : OpenCloseHeapView heap FileImage)
    (calls : RawOpenAdmissionCallbacks heap) (init : OpenSyncCacheCallbacks heap)
    (release : IO.FS.Handle → heap → heap) (first : heap) (errors : List (FilePath × IO.Error)) (input : FilePath)
    (next : NativeReadPosition current.history (current.submissions ++ [.uncertainBatch prepared.batch])) : Prop where
  pending : NativePendingFirstAppend current.ready stop
  initialFiles : view.files first = exited.retry
  initialCensus : view.descriptors first = exited.census
  opens : ∃ (after : heap) (plan : exited.Plan)
      (vacant : TryLockObserves (view.files after).owners current.ready.state.session.directory (.ok true))
      (opening : MarkedReadyOpenObservations input current.ready.state.session.directory
        (view.descriptors after) ⟨exited.retry.image, (view.files after).owners⟩ plan.layout
        current.ready.state.writer.published vacant plan.selected),
    RawFinalizedOpenAttempts view current.ready.state.session.directory calls init release first errors after ∧
    opening.admission.view = stop.view ∧ opening.admission.root = stop.root ∧
    opening.reads.wal.keeper.object = stop.keeper.child ∧ opening.finish.run opening.chronology = next.opened
  keepsReads : next.reads = current.ready.reads

/-- Each operation starts at the exact preceding ready position. A
reported reopen uses the reached files and descriptor inventory.
Maintenance continues from its native return with the ledger intact. -/
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
  | acknowledgedClassified (current : NativeExecutionPosition) {request : WriteRequest}
      {calls : WriteRequest.Calls (DescriptorInventory × DescriptorSlot × Nat)} {sequence : UInt64}
      {reached : OpenWriteFiles} {custody : NativePendingWriteCensus current.ready.state reached.1}
      (ack : ClassifiedWriteAcknowledgement current.ready request calls sequence reached custody) :
      NativeExecutionStep current (.acknowledged request ack.report.batch)
        ⟨current.history ++ ack.report.batch, current.submissions ++ [.acknowledgedBatch ack.report.batch], ack.next⟩
  | checkpoint (current : NativeExecutionPosition)
      {image : Type} {attempt : SegmentedCheckpointReport current.ready.state.session.directory current.ready.state.writer}
      {reports : CheckpointCompletionReports (CensusDirectoryCache × image) attempt}
      (observed : NativeReadyCheckpoint current.ready.state reports) (writer : SegmentedWriterState)
      (completed : observed.Completed writer) (historyEq : writer.history = current.history) :
      NativeExecutionStep current .checkpoint
        ⟨current.history, current.submissions,
          current.ready.afterMaintenance (observed.next writer) completed.valid historyEq⟩
  | collectCoveredWal (current : NativeExecutionPosition)
      (observed : NativeReadyWalCollection current.ready.state) (completed : observed.barrier.outcome = .completed)
      (returned : observed.Completed (observed.next completed) current.submissions current.ready.reads current.history) :
      NativeExecutionStep current .collectCoveredWal
        ⟨current.history, current.submissions,
          current.ready.afterMaintenance (observed.next completed) returned.valid returned.historyEq⟩
  | rejectsCoveredWalPlan (current : NativeExecutionPosition)
      (observed : NativeWalPlanningObservation current.ready.state) (cause : IO.Error)
      (rejected : observed.extents.result = .error cause)
      (returned :
        let state := current.ready.state
        let reached := (state.session.phase, ⟨(state.cache, state.files.image), state.files.owners⟩)
        observed.calls.runPlan state.session.directory reached = .error cause reached) :
      NativeExecutionStep current (.coveredWalCollectionRejected cause) current
  | closeAndReopen (current : NativeExecutionPosition) {input : FilePath}
      (observed : NativeCloseReopenObservation current.ready.state input)
      (next : NativeReadPosition current.history current.submissions)
      (reopened : NativeCloseReopenStep current.ready observed next) :
      NativeExecutionStep current (.closedAndReopened input observed.close.report.result)
        ⟨current.history, current.submissions, next⟩
  | recoverUncertainWrite (current : NativeExecutionPosition)
      (observed : NativeUncertainWriteObservation current.ready.state) (retained : List WAL.Write)
      (next : NativeReadPosition (current.history ++ retained)
        (current.submissions ++ [.uncertainBatch observed.write.failure.batch]))
      (recovered : NativeUncertainWriteContinuation current.ready observed retained next) :
      NativeExecutionStep current
        (.uncertainWriteRecovered observed.write.request observed.input observed.write.failure.cause
          observed.write.failure.batch retained)
        ⟨current.history ++ retained, current.submissions ++ [.uncertainBatch observed.write.failure.batch], next⟩
  | recoverCollectionError (current : NativeExecutionPosition) {input : FilePath}
      (observed : NativeCollectionReopenObservation current.ready.state input)
      (next : NativeReadPosition current.history current.submissions)
      (reopened : NativeCollectionReopenContinuation current.ready observed next) :
      NativeExecutionStep current (.collectionErrorRecovered input observed.diagnostic)
        ⟨current.history, current.submissions, next⟩
  | writePreflight (current : NativeExecutionPosition) {request : WriteRequest}
      (observed : NativeWritePreflightObservation current.ready.state request)
      (returned : NativeWritePreflightStep current.ready observed current.ready) :
      NativeExecutionStep current (.writePreflight request observed.response) current
  | snapshotControl (current : NativeExecutionPosition) (observed : NativeSnapshotUpdateObservation current.ready.state α)
      (next : NativeReadPosition current.history current.submissions)
      (returned : NativeSnapshotUpdateContinuation current.ready observed next) :
      NativeExecutionStep current
        (.snapshotControl observed.update (snapshotControlResult (observed.update.outcome current.ready.state.session)))
        ⟨current.history, current.submissions, next⟩
  | snapshotHandleRead (current : NativeExecutionPosition)
      (observed : NativeSnapshotHandleObservation current.ready.state.session) (request : SnapshotReadRequest α)
      (result : Option α) (recorded : RecordedSnapshotRead) (next : NativeReadPosition current.history current.submissions)
      (returned : NativeSnapshotHandleRead current.ready observed request result recorded next) :
      NativeExecutionStep current (.snapshotHandleRead observed.issuer observed.handle request result recorded)
        ⟨current.history, current.submissions, next⟩
  | checkpointRejected (current : NativeExecutionPosition) (cause : IO.Error)
      (returned : NativeCheckpointRejectedStep current.ready cause current.ready) :
      NativeExecutionStep current (.checkpointRejected cause) current
  | recoverEarlyCheckpointError (current : NativeExecutionPosition) {input : FilePath}
      (seen : NativeEarlyCheckpointReopenObservation current.ready.state input)
      (next : NativeReadPosition current.history current.submissions)
      (reopened : NativeEarlyCheckpointReopen current.ready seen next) :
      NativeExecutionStep current (.firstCheckpointBarrierErrorRecovered input seen.error.error)
        ⟨current.history, current.submissions, next⟩
  | recoverCoveredWalUnlinkError (current : NativeExecutionPosition) {input : FilePath}
      (seen : NativeCoveredWalUnlinkErrorReopen current.ready.state input)
      (next : NativeReadPosition current.history current.submissions)
      (reopened : NativeCoveredWalUnlinkErrorContinuation current.ready seen next) :
      NativeExecutionStep current (.coveredWalUnlinkErrorRecovered input seen.error.cause)
        ⟨current.history, current.submissions, next⟩
  | recoverCoveredWalUnlinkErrorCrash (current : NativeExecutionPosition) {input : FilePath}
      (error : NativeCoveredWalUnlinkError current.ready.state) (crash : NativeCoveredWalUnlinkErrorCrash error)
      (reopened : NativeCoveredWalUnlinkErrorReboot current.ready crash input)
      {layout : CanonicalKeeperLayout crash.observed.retry.image current.ready.state.writer.history}
      {selected : SelectedIntegrityCheckpoint current.ready.state.writer.published.durable
        crash.observed.retry.image.directory.active.manifest current.ready.state.writer.checkpoint}
      (seen : NativeReadyRestartReads crash.observed input layout selected) (state : NativeReadyState)
      (reached : seen.ReachedSession state current.history current.submissions current.ready.reads) :
      NativeExecutionStep current (.coveredWalUnlinkErrorCrashRecovered input error.cause)
        ⟨current.history, current.submissions, ⟨seen.run, state, state, current.ready.reads, reached.1⟩⟩
  | recoverCheckpointError (current : NativeExecutionPosition) {input : FilePath}
      (observed : NativeCheckpointReopenObservation current.ready.state input)
      (next : NativeReadPosition current.history current.submissions)
      (reopened : NativeCheckpointReopenContinuation current.ready observed next) :
      NativeExecutionStep current (.checkpointErrorRecovered input observed.diagnostic)
        ⟨current.history, current.submissions, next⟩
  | planWalCollection (current : NativeExecutionPosition)
      (observed : NativeWalPlanningObservation current.ready.state)
      (returned :
        let state := current.ready.state
        let reached := (state.session.phase, ⟨(state.cache, state.files.image), state.files.owners⟩)
        observed.calls.runPlan state.session.directory reached = match observed.extents.result with
          | .ok offsets => .ok offsets reached
          | .error cause => .error cause reached) :
      NativeExecutionStep current (.walCollectionPlan observed.extents.result) current
  | rotateCreated (current : NativeExecutionPosition) (reported : NativeReadyCreatedRotation current.ready.state)
      (next : NativeReadPosition current.history current.submissions)
      (returned : NativeCreatedRotationContinuation current.ready next reported) :
      NativeExecutionStep current .rotatedWal ⟨current.history, current.submissions, next⟩
  | rotateExisting (current : NativeExecutionPosition) (reported : NativeReadyExistingRotation current.ready.state)
      (next : NativeReadPosition current.history current.submissions)
      (returned : NativeExistingRotationContinuation current.ready next reported) :
      NativeExecutionStep current .rotatedWal ⟨current.history, current.submissions, next⟩
  | rotateEmpty (current : NativeExecutionPosition)
      (returned : ∀ {image : Type} (files : image)
        (lookup : FilePath → Except IO.Error IO.FS.Metadata)
        (read : FilePath → EStateM IO.Error (CensusDirectoryCache × image) (Option ByteArray))
        (create sync : FilePath → EStateM IO.Error (CensusDirectoryCache × image) Unit)
        (release : CensusDirectoryCache → image → image),
        let state := current.ready.state
        let before := (state.session.phase, ⟨(state.cache, files), state.files.owners⟩)
        runObservedRotationWithReset state.session.directory lookup read create sync release before = .ok () before) :
      NativeExecutionStep current .rotatedWal current
  | recoverCheckpointCrash (current : NativeExecutionPosition) {input : FilePath}
      (observed : NativeCheckpointCrashObservation current.ready.state input)
      (next : NativeReadPosition current.history current.submissions)
      (reopened : NativeCheckpointCrashContinuation current.ready observed.crash input next) :
      NativeExecutionStep current (.checkpointCrashRecovered input observed.diagnostic observed.crash.pair.manifest)
        ⟨current.history, current.submissions, next⟩
  | collectObsoleteRuns (current : NativeExecutionPosition) (observed : NativeObsoleteRunCollection current.ready.state)
      (next : NativeReadPosition current.history current.submissions)
      (returned : NativeObsoleteRunCollectionStep current.ready observed next) :
      NativeExecutionStep current (.collectedObsoleteRuns observed.reports.held)
        ⟨current.history, current.submissions, next⟩
  | rewriteRun (current : NativeExecutionPosition) (request : RunMaintenance) (result : Bool)
      (next : NativeReadPosition current.history current.submissions)
      (returned : NativeRunMaintenanceStep current.ready request result next) :
      NativeExecutionStep current (.rewroteRun request result) ⟨current.history, current.submissions, next⟩
  | obsoleteRunCollectionError (current : NativeExecutionPosition)
      (observed : NativeObsoleteRunBarrierError current.ready.state) (next : NativeReadPosition current.history current.submissions)
      (returned : NativeObsoleteRunBarrierErrorStep current.ready observed next) :
      NativeExecutionStep current (.obsoleteRunCollectionError observed.reports.held observed.diagnostic)
        ⟨current.history, current.submissions, next⟩
  | rejectsContendedOpen (current : NativeExecutionPosition) {input : FilePath}
      (seen : NativeContendedOpen current.ready.state input) (drop : LockReferenceDrop)
      (retired : drop = seen.slot.closeEvent)
      (returned : ∀ recover : DiskDirectory → DescriptorSlot → EStateM IO.Error CensusOpenState SegmentedSession,
        seen.run recover = .error seen.diagnostic
          (current.ready.state.census.insert seen.slot seen.free, current.ready.state.files))
      (disposed : (current.ready.state.census.insert seen.slot seen.free).afterDrops [drop] = current.ready.state.census) :
      NativeExecutionStep current (.contendedOpenRejected input seen.diagnostic) current
  | recoverMarkedBarrierRetries (current : NativeExecutionPosition) {inputs : List FilePath} {input : FilePath}
      (seen : NativeCloseMarkedBarrierObservation current.ready.state inputs input)
      (closed : seen.close.report.run = .ok () seen.close.report.finished)
      (next : NativeReadPosition current.history current.submissions)
      (reopened : NativeCloseMarkedBarrierResult current.ready seen.files seen.after input seen.events next) :
      NativeExecutionStep current (.markedBarrierRetriesRecovered input seen.events)
        ⟨current.history, current.submissions, next⟩
  | recoverRejectedOpenSequence (current : NativeExecutionPosition) {inputs : List FilePath} {input : FilePath}
      (observed : NativeRejectedOpenReopenObservation current.ready.state inputs input)
      (next : NativeReadPosition current.history current.submissions)
      (closed : observed.close.report.run = .ok () observed.close.report.finished)
      (errorCount : observed.errors.length = inputs.length)
      (reopened : NativeRejectedOpenAlignedResult current.ready observed.after observed.files input next) :
      NativeExecutionStep current (.rejectedOpenSequenceRecovered inputs input observed.errors)
        ⟨current.history, current.submissions, next⟩
  | recoverFinalizedOpenSequence (current : NativeExecutionPosition) {heap : Type} {input : FilePath}
      {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
      {init : OpenSyncCacheCallbacks heap} {release : IO.FS.Handle → heap → heap}
      {first after : heap} {errors : List (FilePath × IO.Error)}
      (close : NativeReadyClose current.ready.state)
      (closed : close.report.run = .ok () close.report.finished)
      (initialFiles : view.files first = current.ready.state.releasedFiles)
      (initialCensus : view.descriptors first = close.report.finished.descriptors)
      (attempts : RawFinalizedOpenAttempts view current.ready.state.session.directory calls init release first errors after)
      (files : NativeCloseFiles current.ready.state)
      (next : NativeReadPosition current.history current.submissions)
      (reopened : NativeRejectedOpenAlignedResult current.ready (view.descriptors after, view.files after) files input next) :
      NativeExecutionStep current (.rejectedOpenSequenceRecovered (errors.map Prod.fst) input (errors.map Prod.snd))
        ⟨current.history, current.submissions, next⟩
  | recoverReadyExit (current : NativeExecutionPosition) {input : FilePath}
      (seen : NativeReadyProcessExitObservation current.ready.state input)
      (next : NativeReadPosition current.history current.submissions)
      (reopened : NativeReadyProcessExitReopened current.ready seen next) :
      NativeExecutionStep current (.readyExitRecovered input current.ready.state.owner.reference.process)
        ⟨current.history, current.submissions, next⟩
  | recoverInterruptedClose (current : NativeExecutionPosition) {input : FilePath}
      (observed : NativeInterruptedCloseReopenObservation current.ready.state input)
      (next : NativeReadPosition current.history current.submissions)
      (reopened : NativeInterruptedCloseReopenContinuation current.ready next observed) :
      NativeExecutionStep current (.interruptedCloseRecovered input observed.cut.effective)
        ⟨current.history, current.submissions, next⟩
  | recoverCheckpointRunFileError (current : NativeExecutionPosition) {input : FilePath}
      (seen : NativeCheckpointRunFileReopenObservation current.ready.state input)
      (next : NativeReadPosition current.history current.submissions)
      (reopened : NativeCheckpointRunFileReopened current.ready seen next) :
      NativeExecutionStep current (.checkpointRunFileErrorRecovered input seen.error.index seen.error.error)
        ⟨current.history, current.submissions, next⟩
  | recoverCheckpointManifestSyncError (current : NativeExecutionPosition) {input : FilePath}
      (seen : NativeCheckpointManifestSyncReopenObservation current.ready.state input)
      (next : NativeReadPosition current.history current.submissions)
      (reopened : NativeCheckpointManifestSyncReopened current.ready seen next) :
      NativeExecutionStep current (.checkpointManifestSyncErrorRecovered input seen.error.error)
        ⟨current.history, current.submissions, next⟩
  | recoverCheckpointManifestRenameError (current : NativeExecutionPosition) {input : FilePath} {image : Type}
      {cut : CheckpointPowerCut current.ready.state.session.directory current.ready.state.writer}
      {report : NativeCheckpointManifestRenameError (image := image) current.ready.state cut}
      (crash : NativeCheckpointManifestRenameCrash report) (next : NativeReadPosition current.history current.submissions)
      (reopened : NativeCheckpointManifestRenameReopened current.ready crash input next) :
      NativeExecutionStep current (.checkpointManifestRenameCrashRecovered input report.cause crash.pair.manifest)
        ⟨current.history, current.submissions, next⟩
  | recoverInterruptedCheckpoint (current : NativeExecutionPosition) {input : FilePath}
      (observed : NativePendingCheckpointCrashObservation current.ready.state input)
      (next : NativeReadPosition current.history current.submissions)
      (reopened : NativePendingCheckpointReopened current.ready observed next) :
      NativeExecutionStep current (.interruptedCheckpointRecovered input observed.crash.pair.manifest)
        ⟨current.history, current.submissions, next⟩
  | recoverInterruptedEarlyCheckpoint (current : NativeExecutionPosition) {input : FilePath}
      (recovery : NativeEarlyCheckpointReboot current.ready.state) {valid : current.ready.state.Valid}
      {layout : CanonicalKeeperLayout (recovery.observed valid).retry.image current.ready.state.writer.history}
      {selected : SelectedIntegrityCheckpoint current.ready.state.writer.published.durable
        (recovery.observed valid).retry.image.directory.active.manifest current.ready.state.writer.checkpoint}
      (reader : NativeReadyRestartReads (recovery.observed valid) input layout selected)
      (next : NativeReadPosition current.history current.submissions)
      (sameReader : next.opened = reader.run)
      (reached : reader.ReachedSession next.state current.history current.submissions current.ready.reads)
      (sameReads : next.reads = current.ready.reads) :
      NativeExecutionStep current (recovery.event input) ⟨current.history, current.submissions, next⟩
  | recoverUncertainWriteCrash (current : NativeExecutionPosition) {input : FilePath}
      (observed : NativeUncertainWriteCrashObservation current.ready.state input) (retained : List WAL.Write)
      (next : NativeReadPosition (current.history ++ retained)
        (current.submissions ++ [.uncertainBatch observed.write.failure.batch]))
      (reopened : NativeUncertainWriteCrashContinuation current.ready observed retained next) :
      NativeExecutionStep current
        (.uncertainWriteCrashRecovered observed.write.request input observed.write.failure.cause
          observed.write.failure.batch retained)
        ⟨current.history ++ retained, current.submissions ++ [.uncertainBatch observed.write.failure.batch], next⟩
  | recoverUncertainWriteStageRetry (current : NativeExecutionPosition) {failedInput input : FilePath}
      (pending : NativePendingWrite current.ready) (observed : NativeUncertainStageRetryObservation pending failedInput input)
      (next : NativeReadPosition current.history pending.submissions)
      (reopened : NativeUncertainStageRetryContinuation pending observed next) :
      NativeExecutionStep current
        (.uncertainWriteStageRetryRecovered pending.write.request failedInput input pending.write.failure.cause
          (reopened.failedOpen.failure.diagnostic reopened.failedOpen.unlock) pending.write.failure.batch)
        ⟨current.history, pending.submissions, next⟩
  | recoverUncertainWriteInterruptedClose (current : NativeExecutionPosition) {input : FilePath}
      (pending : NativePendingWrite current.ready) (observed : NativePoisonedCloseReopenObservation pending input)
      (retained : List WAL.Write) (next : NativeReadPosition (current.history ++ retained) pending.submissions)
      (reopened : NativePoisonedCloseReopenContinuation pending observed retained next) :
      NativeExecutionStep current
        (.uncertainWriteInterruptedCloseRecovered pending.write.request input pending.write.failure.cause
          pending.write.failure.batch retained)
        ⟨current.history ++ retained, pending.submissions, next⟩
  | obsoleteRunUnlinkError (current : NativeExecutionPosition) (cut : NativeObsoleteRunUnlinkCut current.ready.state)
      (error : NativeObsoleteRunUnlinkError cut) (next : NativeReadPosition current.history current.submissions)
      (returned : NativeObsoleteRunUnlinkErrorStep current.ready cut error next) :
      NativeExecutionStep current (.obsoleteRunCollectionError cut.plan.reports.held error.cause)
        ⟨current.history, current.submissions, next⟩
  | recoverInterruptedCoveredWalUnlink (current : NativeExecutionPosition) {input : FilePath}
      {stop : NativeCoveredWalUnlinkStop current.ready.state} (crash : NativeCoveredWalUnlinkCrash stop)
      (recovery : NativeCoveredWalUnlinkReopen current.ready crash input)
      {layout : CanonicalKeeperLayout crash.observed.retry.image current.ready.state.writer.history}
      {selected : SelectedIntegrityCheckpoint current.ready.state.writer.published.durable
        crash.observed.retry.image.directory.active.manifest current.ready.state.writer.checkpoint}
      (seen : NativeReadyRestartReads crash.observed input layout selected) (state : NativeReadyState)
      (reached : seen.ReachedSession state current.history current.submissions current.ready.reads) :
      NativeExecutionStep current (.interruptedCoveredWalUnlinkRecovered input)
        ⟨current.history, current.submissions, ⟨seen.run, state, state, current.ready.reads, reached.1⟩⟩
  | recoverInterruptedCoveredWalDirectory (current : NativeExecutionPosition) {input : FilePath}
      {stop : NativeCoveredWalDirectoryStop current.ready.state} (crash : NativeCoveredWalDirectoryCrash stop)
      (recovery : NativeCoveredWalDirectoryReopen current.ready crash input)
      {layout : CanonicalKeeperLayout crash.observed.retry.image current.ready.state.writer.history}
      {selected : SelectedIntegrityCheckpoint current.ready.state.writer.published.durable
        crash.observed.retry.image.directory.active.manifest current.ready.state.writer.checkpoint}
      (seen : NativeReadyRestartReads crash.observed input layout selected) (state : NativeReadyState)
      (reached : seen.ReachedSession state current.history current.submissions current.ready.reads) :
      NativeExecutionStep current (.interruptedCoveredWalDirectoryRecovered input stop.applied)
        ⟨current.history, current.submissions, ⟨seen.run, state, state, current.ready.reads, reached.1⟩⟩
  | recoverInterruptedRunUnlink (current : NativeExecutionPosition) {input : FilePath}
      {cut : NativeObsoleteRunUnlinkCut current.ready.state} (stop : NativeObsoleteRunUnlinkStop cut)
      (crash : NativeObsoleteRunUnlinkCrash cut) (next : NativeReadPosition current.history current.submissions)
      (reopened : NativeObsoleteRunUnlinkCrashReopen current.ready next stop crash input) :
      NativeExecutionStep current (.interruptedRunUnlinkRecovered cut.plan.reports.held input)
        ⟨current.history, current.submissions, next⟩
  | rewriteRunCheckpointAndReopen (current : NativeExecutionPosition) {request : RunMaintenance} {input : FilePath}
      (seen : NativeRunMaintenanceReopenObservation current.ready.state request input)
      (next : NativeReadPosition current.history current.submissions)
      (reopened : NativeRunMaintenanceReopen current.ready request seen.checkpoint input next) :
      NativeExecutionStep current (.rewroteRunCheckpointAndReopened request input)
        ⟨current.history, current.submissions, next⟩
  | recoverInterruptedMarker (current : NativeExecutionPosition) {input : FilePath}
      {prepared : NativeReadyWritePreparation current.ready.state} {stop : NativeMarkerPublicationStop prepared}
      (crash : NativeMarkerPublicationCrash stop) (retained : List WAL.Write)
      (next : NativeReadPosition (current.history ++ retained) (current.submissions ++ [.uncertainBatch prepared.batch]))
      (reopened : NativeMarkerPublicationCrashContinuation current.ready crash input retained next) :
      NativeExecutionStep current (.interruptedMarkerRecovered stop.request input prepared.batch retained)
        ⟨current.history ++ retained, current.submissions ++ [.uncertainBatch prepared.batch], next⟩
  | closesAfterRetries (current : NativeExecutionPosition) {input : FilePath}
      (seen : NativeReadyCloseRetryObservation current.ready.state input)
      (next : NativeReadPosition current.history current.submissions)
      (reopened : NativeReadyCloseRetryContinuation current.ready seen next) :
      NativeExecutionStep current (.closedAfterRetries input (seen.attempts.map (·.cause)) seen.final.close.report.result)
        ⟨current.history, current.submissions, next⟩
  | recoverUncertainWriteAfterCloseRetries (current : NativeExecutionPosition) {input : FilePath}
      (pending : NativePendingWrite current.ready) (seen : NativePendingCloseRecovery pending input)
      (retained : List WAL.Write) (next : NativeReadPosition (current.history ++ retained) pending.submissions)
      (reopened : seen.Reopened retained next) :
      NativeExecutionStep current
        (.uncertainWriteCloseRetriesRecovered pending.write.request input pending.write.failure.cause
          seen.release seen.errors pending.write.failure.batch retained)
        ⟨current.history ++ retained, pending.submissions, next⟩
  | recoverUncertainWriteAfterExit (current : NativeExecutionPosition) {input : FilePath}
      (pending : NativePendingWrite current.ready) (seen : NativePendingWriteProcessExit pending)
      (retained : List WAL.Write) (next : NativeReadPosition (current.history ++ retained) pending.submissions)
      (reopened : NativePendingWriteExitReopened seen input retained next) :
      NativeExecutionStep current
        (.uncertainWriteExitRecovered pending.write.request input pending.write.failure.cause
          seen.requests current.ready.state.owner.reference.process pending.write.failure.batch retained)
        ⟨current.history ++ retained, pending.submissions, next⟩
  | recoverUncertainWriteAfterClientCalls (current : NativeExecutionPosition) {input : FilePath}
      (pending : NativePendingWrite current.ready) (seen : NativePendingClientRecovery pending input)
      (retained : List WAL.Write) (next : NativeReadPosition (current.history ++ retained) pending.submissions)
      (reopened : NativePendingClientContinuation seen retained next) :
      NativeExecutionStep current
        (.uncertainWriteClientCallsRecovered pending.write.request input pending.write.failure.cause
          seen.events pending.write.failure.batch retained)
        ⟨current.history ++ retained, pending.submissions, next⟩
  | recoverInterruptedAppendCrash (current : NativeExecutionPosition) {input : FilePath}
      {prepared : NativeReadyWritePreparation current.ready.state} {stop : NativeFirstAppendStop prepared}
      (crash : NativeFirstAppendCrash stop)
      (next : NativeReadPosition current.history (current.submissions ++ [.uncertainBatch prepared.batch]))
      (reopened : NativeFirstAppendCrashContinuation current.ready crash input next) :
      NativeExecutionStep current (.interruptedAppendCrashRecovered stop.request input prepared.batch)
        ⟨current.history, current.submissions ++ [.uncertainBatch prepared.batch], next⟩
  | recoverInterruptedAppend (current : NativeExecutionPosition) {input : FilePath}
      {prepared : NativeReadyWritePreparation current.ready.state} (stop : NativeFirstAppendStop prepared)
      (exited : NativeFirstAppendExit stop)
      (next : NativeReadPosition current.history (current.submissions ++ [.uncertainBatch prepared.batch]))
      (reopened : NativeFirstAppendExitContinuation current.ready stop exited input next) :
      NativeExecutionStep current (.interruptedAppendRecovered stop.request input prepared.batch)
        ⟨current.history, current.submissions ++ [.uncertainBatch prepared.batch], next⟩
  | recoverInterruptedAppendAfterRetries (current : NativeExecutionPosition) {heap : Type} {input : FilePath}
      {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
      {init : OpenSyncCacheCallbacks heap} {release : IO.FS.Handle → heap → heap}
      {first : heap} {errors : List (FilePath × IO.Error)}
      {prepared : NativeReadyWritePreparation current.ready.state} (stop : NativeFirstAppendStop prepared)
      (exited : NativeFirstAppendExit stop)
      (next : NativeReadPosition current.history (current.submissions ++ [.uncertainBatch prepared.batch]))
      (reopened : NativeFirstAppendRetryRecovery current stop exited view calls init release first errors input next) :
      NativeExecutionStep current (.interruptedAppendRetriesRecovered stop.request errors input prepared.batch)
        ⟨current.history, current.submissions ++ [.uncertainBatch prepared.batch], next⟩
  | recoverInterruptedAppendAfterContention (current : NativeExecutionPosition) {heap : Type} {input : FilePath}
      {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
      {init : OpenSyncCacheCallbacks heap} {release : IO.FS.Handle → heap → heap}
      {first : heap} {errors : List (FilePath × IO.Error)} {busy : FilePath × IO.Error}
      {prepared : NativeReadyWritePreparation current.ready.state} (stop : NativeFirstAppendStop prepared)
      (exited : NativeFirstAppendExit stop)
      (access : NativeFirstAppendRetryAccess exited view calls release first (some busy))
      (next : NativeReadPosition current.history (current.submissions ++ [.uncertainBatch prepared.batch]))
      (reopened : NativeFirstAppendRetryRecovery current stop exited view calls init release first errors input next) :
      NativeExecutionStep current (.interruptedAppendContendedRetriesRecovered stop.request busy errors input prepared.batch)
        ⟨current.history, current.submissions ++ [.uncertainBatch prepared.batch], next⟩
  | collectsObsoleteRunsAfterRetries (current : NativeExecutionPosition) {held errors initial before}
      {retryAt : NativeReadPosition current.history current.submissions}
      (prior : NativeObsoleteRunUnlinkRetries current.ready initial held retryAt before errors)
      (retry : NativeObsoleteRunCollection retryAt.state) (sameImage : retry.initial = before)
      (sameHolds : retry.reports.held = held) (next : NativeReadPosition current.history current.submissions)
      (returned : NativeObsoleteRunCollectionStep retryAt retry next) :
      NativeExecutionStep current (.collectedObsoleteRunsAfterRetries held errors)
        ⟨current.history, current.submissions, next⟩
  | recoverRotationError (current : NativeExecutionPosition) {input : FilePath} {cause : IO.Error}
      {failure : NativeRotationDirectoryFailure current.ready.state (some cause)}
      (observed : NativeRotationErrorReopenObservation failure current.ready.readPrefix.refines.1 input)
      (next : NativeReadPosition current.history current.submissions)
      (reopened : NativeRotationErrorReopenContinuation current.ready next observed) :
      NativeExecutionStep current
        (.rotationErrorRecovered input (IO.userError s!"sync failed for '{current.ready.state.session.directory.path}': {cause}"))
        ⟨current.history, current.submissions, next⟩
  | recoverRotationCrash (current : NativeExecutionPosition) {input : FilePath} {cause : IO.Error}
      {failure : NativeRotationDirectoryFailure current.ready.state (some cause)}
      (crash : NativeRotationErrorCrash failure)
      (next : NativeReadPosition current.history current.submissions)
      (reopened : NativeRotationCrashReopen current.ready next crash input) :
      NativeExecutionStep current
        (.rotationCrashRecovered input (IO.userError s!"sync failed for '{current.ready.state.session.directory.path}': {cause}")
          next.state.writer.installed.activeFirst)
        ⟨current.history, current.submissions, next⟩
  | recoverInterruptedRotation (current : NativeExecutionPosition) {input : FilePath}
      {stop : NativeRotationDirectoryStop current.ready.state} (crash : NativeRotationErrorCrash stop)
      (next : NativeReadPosition current.history current.submissions)
      (reopened : NativeInterruptedRotationCrashReopen current.ready next crash input) :
      NativeExecutionStep current (.interruptedRotationRecovered input next.state.writer.installed.activeFirst)
        ⟨current.history, current.submissions, next⟩

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

theorem NativeExecutionPosition.checkpoints (current : NativeExecutionPosition)
    {image : Type} {attempt : SegmentedCheckpointReport current.ready.state.session.directory current.ready.state.writer}
    {reports : CheckpointCompletionReports (CensusDirectoryCache × image) attempt}
    (observed : NativeReadyCheckpoint current.ready.state reports) :
    ∃ next, NativeExecutionStep current .checkpoint next := by
  obtain ⟨writer, completed, sameHistory, _⟩ := current.ready.readPrefix.checkpoints observed
  exact ⟨_, .checkpoint current observed writer completed sameHistory⟩

theorem NativeExecutionPosition.collectsCoveredWal (current : NativeExecutionPosition)
    (observed : NativeReadyWalCollection current.ready.state) (completed : observed.barrier.outcome = .completed) :
    ∃ next, NativeExecutionStep current .collectCoveredWal next := by
  exact ⟨_, .collectCoveredWal current observed completed (current.ready.readPrefix.collectsCoveredWal observed completed)⟩

/-- Preserve the established directory-stop interface by projecting it
to the shared early checkpoint transition. -/
theorem NativeExecutionStep.recoverInterruptedCheckpointRunDirectory
    (current : NativeExecutionPosition) {input : FilePath} {image : Type}
    {cut : CheckpointPowerCut current.ready.state.session.directory current.ready.state.writer}
    {stop : NativeCheckpointRunDirectoryStop (image := image) current.ready.state cut}
    (reboot : NativeCheckpointRunDirectoryReboot stop) {valid : current.ready.state.Valid} {plan : reboot.Plan valid}
    (reader : NativeReadyRestartReads (reboot.observed valid) input plan.layout plan.selected)
    (next : NativeReadPosition current.history current.submissions)
    (reopened : NativeCheckpointRunDirectoryReopened current.ready reboot reader next) :
    NativeExecutionStep current
      (.interruptedEarlyCheckpointRecovered input .syncRunsDirectory cut.tookEffect
        current.ready.state.writer.target.pair.manifest)
      ⟨current.history, current.submissions, next⟩ :=
  .recoverInterruptedEarlyCheckpoint current (.directory reboot) (valid := valid) reader next
    reopened.returned.1 reopened.returned.2 reopened.reads

theorem NativeExecutionStep.ledgers (step : NativeExecutionStep before event after) :
    after.history = before.history ++ event.writes ∧
    after.submissions = before.submissions ++ event.submissions ∧
    after.ready.reads = before.ready.reads ++ event.reads := by
  cases step
  case readOrRestart observed => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], observed.frames.1⟩
  case acknowledged reads =>
    exact ⟨rfl, rfl, by simpa [NativeExecutionEvent.reads] using reads⟩
  case acknowledgedClassified ack =>
    exact ⟨rfl, rfl, by simpa [NativeExecutionEvent.reads] using ack.reads⟩
  case checkpoint => simp [NativeExecutionEvent.writes, NativeExecutionEvent.submissions, NativeExecutionEvent.reads,
      NativeReadPosition.afterMaintenance]
  case collectCoveredWal => simp [NativeExecutionEvent.writes, NativeExecutionEvent.submissions,
      NativeExecutionEvent.reads, NativeReadPosition.afterMaintenance]
  case rejectsCoveredWalPlan => simp [NativeExecutionEvent.writes, NativeExecutionEvent.submissions, NativeExecutionEvent.reads]
  case closeAndReopen reopened => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], by simpa [NativeExecutionEvent.reads] using reopened.reads⟩
  case recoverUncertainWrite recovered =>
    exact ⟨rfl, rfl, by simpa [NativeExecutionEvent.reads] using recovered.earlierReads⟩
  case recoverCollectionError reopened => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], by simpa [NativeExecutionEvent.reads] using reopened.reads⟩
  case writePreflight =>
    simp [NativeExecutionEvent.writes, NativeExecutionEvent.submissions, NativeExecutionEvent.reads]
  case snapshotControl returned => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], by simpa [NativeExecutionEvent.reads] using returned.reads⟩
  case snapshotHandleRead returned => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], returned.reads⟩
  case checkpointRejected =>
    simp [NativeExecutionEvent.writes, NativeExecutionEvent.submissions, NativeExecutionEvent.reads]
  case recoverEarlyCheckpointError reopened => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], by simpa [NativeExecutionEvent.reads] using reopened.reads⟩
  case recoverCoveredWalUnlinkError reopened => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], by simpa [NativeExecutionEvent.reads] using reopened.reads⟩
  case recoverCoveredWalUnlinkErrorCrash =>
    simp [NativeExecutionEvent.writes, NativeExecutionEvent.submissions, NativeExecutionEvent.reads]
  case recoverCheckpointError reopened => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], by simpa [NativeExecutionEvent.reads] using reopened.reads⟩
  case planWalCollection =>
    simp [NativeExecutionEvent.writes, NativeExecutionEvent.submissions, NativeExecutionEvent.reads]
  case rotateCreated returned => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], by simpa [NativeExecutionEvent.reads] using returned.frame.reads⟩
  case rotateExisting returned => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], by simpa [NativeExecutionEvent.reads] using returned.frame.reads⟩
  case rotateEmpty =>
    simp [NativeExecutionEvent.writes, NativeExecutionEvent.submissions, NativeExecutionEvent.reads]
  case recoverCheckpointCrash reopened => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], by simpa [NativeExecutionEvent.reads] using reopened.reads⟩
  case collectObsoleteRuns returned => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], by simpa [NativeExecutionEvent.reads] using returned.reads⟩
  case rewriteRun returned => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], by simpa [NativeExecutionEvent.reads] using returned.reads⟩
  case obsoleteRunCollectionError returned => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], by simpa [NativeExecutionEvent.reads] using returned.reads⟩
  case rejectsContendedOpen => simp [NativeExecutionEvent.writes, NativeExecutionEvent.submissions, NativeExecutionEvent.reads]
  case recoverMarkedBarrierRetries reopened => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], by simpa [NativeExecutionEvent.reads] using reopened.reads⟩
  case recoverRejectedOpenSequence reopened => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], by simpa [NativeExecutionEvent.reads] using reopened.reads⟩
  case recoverFinalizedOpenSequence reopened => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], by simpa [NativeExecutionEvent.reads] using reopened.reads⟩
  case recoverReadyExit reopened => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], by simpa [NativeExecutionEvent.reads] using reopened.reads⟩
  case recoverInterruptedClose reopened => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], by simpa [NativeExecutionEvent.reads] using reopened.reads⟩
  case recoverCheckpointRunFileError reopened => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], by simpa [NativeExecutionEvent.reads] using reopened.reads⟩
  case recoverCheckpointManifestSyncError reopened => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], by simpa [NativeExecutionEvent.reads] using reopened.reads⟩
  case recoverCheckpointManifestRenameError reopened => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], by simpa [NativeExecutionEvent.reads] using reopened.reads⟩
  case recoverInterruptedCheckpoint reopened => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], by simpa [NativeExecutionEvent.reads] using reopened.reads⟩
  case recoverInterruptedEarlyCheckpoint sameReads =>
    exact ⟨by simp [NativeEarlyCheckpointReboot.event, NativeExecutionEvent.writes],
      by simp [NativeEarlyCheckpointReboot.event, NativeExecutionEvent.submissions],
      by simpa [NativeEarlyCheckpointReboot.event, NativeExecutionEvent.reads] using sameReads⟩
  case recoverUncertainWriteCrash reopened =>
    exact ⟨rfl, rfl, by simpa [NativeExecutionEvent.reads] using reopened.reads⟩
  case recoverUncertainWriteStageRetry reopened =>
    exact ⟨by simp [NativeExecutionEvent.writes], rfl, by simpa [NativeExecutionEvent.reads] using reopened.reads⟩
  case recoverUncertainWriteInterruptedClose reopened =>
    exact ⟨rfl, rfl, by simpa [NativeExecutionEvent.reads] using reopened.reads⟩
  case obsoleteRunUnlinkError returned => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], by simpa [NativeExecutionEvent.reads] using returned.reads⟩
  case recoverInterruptedCoveredWalUnlink =>
    simp [NativeExecutionEvent.writes, NativeExecutionEvent.submissions, NativeExecutionEvent.reads]
  case recoverInterruptedCoveredWalDirectory =>
    simp [NativeExecutionEvent.writes, NativeExecutionEvent.submissions, NativeExecutionEvent.reads]
  case recoverInterruptedRunUnlink reopened => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], by simpa [NativeExecutionEvent.reads] using reopened.reads⟩
  case rewriteRunCheckpointAndReopen reopened => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], by simpa [NativeExecutionEvent.reads] using reopened.reads⟩
  case recoverInterruptedMarker reopened =>
    exact ⟨rfl, rfl, by simpa [NativeExecutionEvent.reads] using reopened.reads⟩
  case closesAfterRetries reopened => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], by simpa [NativeExecutionEvent.reads] using reopened.reopened.reads⟩
  case recoverUncertainWriteAfterCloseRetries =>
    rename_i pending seen next reopened
    exact ⟨rfl, rfl, by simpa [NativeExecutionEvent.reads] using (seen.frames reopened).2⟩
  case recoverUncertainWriteAfterExit reopened =>
    exact ⟨rfl, rfl, by simpa [NativeExecutionEvent.reads] using reopened.reads⟩
  case recoverUncertainWriteAfterClientCalls reopened =>
    exact ⟨rfl, rfl, by simpa [NativeExecutionEvent.reads] using reopened.reads⟩
  case recoverInterruptedAppendCrash reopened =>
    exact ⟨by simp [NativeExecutionEvent.writes], rfl, by simpa [NativeExecutionEvent.reads] using reopened.reads⟩
  case recoverInterruptedAppend reopened =>
    exact ⟨by simp [NativeExecutionEvent.writes], rfl, by simpa [NativeExecutionEvent.reads] using reopened.reads⟩
  case recoverInterruptedAppendAfterRetries reopened | recoverInterruptedAppendAfterContention reopened =>
    exact ⟨by simp [NativeExecutionEvent.writes], rfl, by simpa [NativeExecutionEvent.reads] using reopened.keepsReads⟩
  case collectsObsoleteRunsAfterRetries prior _ _ _ _ returned =>
    obtain ⟨_, _, _, _, _, _, _, _, _, reads⟩ := prior.frames
    exact ⟨by simp [NativeExecutionEvent.writes], by simp [NativeExecutionEvent.submissions],
      by simpa [NativeExecutionEvent.reads] using returned.reads.trans reads⟩
  case recoverRotationError reopened => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], by simpa [NativeExecutionEvent.reads] using reopened.reads⟩
  case recoverRotationCrash reopened => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], by simpa [NativeExecutionEvent.reads] using reopened.reads⟩
  case recoverInterruptedRotation reopened => exact ⟨by simp [NativeExecutionEvent.writes],
      by simp [NativeExecutionEvent.submissions], by simpa [NativeExecutionEvent.reads] using reopened.reads⟩

theorem NativeExecutionStep.uncertainBatchWhole (step : NativeExecutionStep before event after) :
    event.uncertainBatchWhole := by
  cases step <;> try trivial
  case recoverUncertainWrite recovered => exact recovered.wholeOrNone
  case recoverUncertainWriteCrash recovered => exact recovered.wholeOrNone
  case recoverUncertainWriteInterruptedClose recovered => exact recovered.wholeOrNone
  case recoverInterruptedMarker recovered => exact recovered.wholeOrNone
  case recoverUncertainWriteAfterExit recovered => exact recovered.wholeOrNone
  case recoverUncertainWriteAfterClientCalls recovered => exact recovered.wholeOrNone
  case recoverUncertainWriteAfterCloseRetries =>
    rename_i pending seen next reopened
    exact (seen.frames reopened).1

/-- Client observations of a reached source or modeled execution.
The execution itself supplies the evidence for these equations. -/
structure NativeExecutionPosition.LedgerSuffix
    (start : NativeExecutionPosition) (events : List NativeExecutionEvent) (last : NativeExecutionPosition) : Prop where
  history : last.history = start.history ++ events.flatMap NativeExecutionEvent.writes
  submissions : last.submissions = start.submissions ++ events.flatMap NativeExecutionEvent.submissions
  reads : last.ready.reads = start.ready.reads ++ events.flatMap NativeExecutionEvent.reads
  whole : ∀ event ∈ events, event.uncertainBatchWhole

namespace NativeExecutionPosition.LedgerSuffix

variable {start middle last : NativeExecutionPosition} {earlier later : List NativeExecutionEvent}

theorem empty (position : NativeExecutionPosition) : position.LedgerSuffix [] position := by
  exact ⟨by simp, by simp, by simp, by simp⟩

theorem append (first : start.LedgerSuffix earlier middle) (second : middle.LedgerSuffix later last) :
    start.LedgerSuffix (earlier ++ later) last := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [second.history, first.history, List.flatMap_append, List.append_assoc]
  · simp only [second.submissions, first.submissions, List.flatMap_append, List.append_assoc]
  · simp only [second.reads, first.reads, List.flatMap_append, List.append_assoc]
  · intro event member
    exact (List.mem_append.mp member).elim (first.whole event) (second.whole event)

end NativeExecutionPosition.LedgerSuffix

theorem NativeExecutionStep.ledgerSuffix {start last : NativeExecutionPosition} {event : NativeExecutionEvent}
    (step : NativeExecutionStep start event last) : start.LedgerSuffix [event] last := by
  obtain ⟨history, submissions, reads⟩ := step.ledgers
  refine ⟨by simpa using history, by simpa using submissions, by simpa using reads, ?_⟩
  intro observed member
  obtain rfl := List.mem_singleton.mp member
  exact step.uncertainBatchWhole

/-- A finite trace of supported reads, acknowledged native writes,
healthy maintenance, and the covered close, write recovery, and quiet
crash/reopen routes. Each step starts at the preceding reached state. -/
inductive NativeExecutionTrace (start : NativeExecutionPosition) :
    List NativeExecutionEvent → NativeExecutionPosition → Prop where
  | empty : NativeExecutionTrace start [] start
  | step (prior : NativeExecutionTrace start events before) (next : NativeExecutionStep before event after) :
      NativeExecutionTrace start (events ++ [event]) after

theorem NativeExecutionTrace.ledgerSuffix (observed : NativeExecutionTrace start events last) :
    start.LedgerSuffix events last := by
  induction observed with
  | empty => exact .empty _
  | step _ next ih => exact ih.append next.ledgerSuffix

theorem NativeExecutionTrace.ledgers (observed : NativeExecutionTrace start events last) :
    last.history = start.history ++ events.flatMap NativeExecutionEvent.writes ∧
    last.submissions = start.submissions ++ events.flatMap NativeExecutionEvent.submissions ∧
    last.ready.reads = start.ready.reads ++ events.flatMap NativeExecutionEvent.reads :=
  ⟨observed.ledgerSuffix.history, observed.ledgerSuffix.submissions, observed.ledgerSuffix.reads⟩

theorem NativeExecutionTrace.uncertainBatchesWhole (observed : NativeExecutionTrace start events last) :
    ∀ event ∈ events, event.uncertainBatchWhole :=
  observed.ledgerSuffix.whole

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
  | checkpoint
  | checkpointThenCloseAndReopen (input : FilePath)
  | checkpointRunFileErrorThenReopen (input : FilePath) (index : Nat)
  | checkpointManifestSyncErrorThenReopen (input : FilePath)
  | checkpointFirstBarrierErrorThenReopen (input : FilePath)
  | coveredWalUnlinkErrorThenReopen (input : FilePath)
  | checkpointThenPowerLossAndReopen (input : FilePath)
  | checkpointManifestRenameErrorThenPowerLossAndReopen (input : FilePath)
  | collectCoveredWal
  | interruptedCoveredWalUnlinkThenReopen (input : FilePath)
  | coveredWalUnlinkErrorThenPowerLossAndReopen (input : FilePath)
  | interruptedCoveredWalDirectoryThenReopen (input : FilePath)
  | planWalCollection
  | rotateWal
  | rotateThenCloseAndReopen (input : FilePath)
  | rotateThenPowerLossAndReopen (input : FilePath)
  | interruptedRotationThenReopen (input : FilePath)
  | collectObsoleteRuns (held : List UInt64)
  | interruptedRunUnlinkThenReopen (held : List UInt64) (input : FilePath)
  | retryObsoleteRunCollection (held : List UInt64) (failedAttempts : Nat)
  | rewriteRun (request : RunMaintenance)
  | rewriteRunThenCheckpointAndReopen (request : RunMaintenance) (input : FilePath)
  | openContended (input : FilePath)
  | closeThenRetryMarkedBarriers (inputs : List FilePath) (input : FilePath)
  | closeThenRetryAndReopen (inputs : List FilePath) (input : FilePath)
  | closeAndReopen (input : FilePath)
  | closeAfterRetriesAndReopen (input : FilePath) (failedAttempts : Nat)
  | readyExitThenReopen (input : FilePath)
  | interruptedCloseThenReopen (input : FilePath)
  | interruptedCheckpointThenReopen (input : FilePath)
  | interruptedCheckpointRunDirectoryThenReopen (input : FilePath)
  | writeThenCloseAndReopen (request : WriteRequest) (input : FilePath)
  | writeThenPowerLossAndReopen (request : WriteRequest) (input : FilePath)
  | writeThenPowerLossStageRetryAndReopen (request : WriteRequest) (failedInput input : FilePath)
  | writeThenInterruptedCloseAndReopen (request : WriteRequest) (input : FilePath)
  | interruptedAppendThenReopen (request : WriteRequest) (input : FilePath)
  | interruptedAppendThenPowerLossAndReopen (request : WriteRequest) (input : FilePath)
  | writeThenCloseRetriesAndReopen (request : WriteRequest) (input : FilePath)
      (release : PendingCloseRelease) (failedAttempts : Nat)
  | writeThenExitAndReopen (request : WriteRequest) (input : FilePath) (rejected : List NativeInactiveRequest)
  | writeThenClientCallsAndReopen (request : WriteRequest) (input : FilePath)
      (calls : List NativePendingClientInstruction)
  | interruptedMarkerThenReopen (request : WriteRequest) (input : FilePath)
  | collectThenCloseAndReopen (input : FilePath)
  | snapshotControl (request : SnapshotUpdate α)
  | snapshotHandleRead (issuer : Nat) (handle : SnapshotHandle) (request : SnapshotReadRequest α)

/-- The recorded event belongs to the submitted instruction. Read
observations determine the requested key or range and sequence. -/
def NativeExecutionInstruction.Matches : NativeExecutionInstruction → NativeExecutionEvent → Prop
  | .snapshot sequence request, .readOrRestart (.read recorded) =>
    ∃ response, recorded = request.record sequence response
  | .write request, .acknowledged submitted _ => submitted = request
  | .write request, .writePreflight submitted _ => submitted = request
  | .restart input, .readOrRestart (.restart resolvedInput) => resolvedInput = input
  | .checkpoint, .checkpoint => True
  | .checkpoint, .checkpointRejected _ => True
  | .checkpointThenCloseAndReopen input, .checkpointErrorRecovered opened _ => opened = input
  | .checkpointRunFileErrorThenReopen input index, .checkpointRunFileErrorRecovered opened issued _ =>
    opened = input ∧ issued = index
  | .checkpointManifestSyncErrorThenReopen input, .checkpointManifestSyncErrorRecovered opened _ => opened = input
  | .checkpointFirstBarrierErrorThenReopen input, .firstCheckpointBarrierErrorRecovered opened _ => opened = input
  | .coveredWalUnlinkErrorThenReopen input, .coveredWalUnlinkErrorRecovered opened _ => opened = input
  | .checkpointThenPowerLossAndReopen input, .checkpointCrashRecovered opened _ _ => opened = input
  | .checkpointManifestRenameErrorThenPowerLossAndReopen input, .checkpointManifestRenameCrashRecovered opened _ _ =>
    opened = input
  | .collectCoveredWal, .collectCoveredWal | .collectCoveredWal, .coveredWalCollectionRejected _ => True
  | .interruptedCoveredWalUnlinkThenReopen input, .interruptedCoveredWalUnlinkRecovered opened => opened = input
  | .coveredWalUnlinkErrorThenPowerLossAndReopen input, .coveredWalUnlinkErrorCrashRecovered opened _ => opened = input
  | .interruptedCoveredWalDirectoryThenReopen input, .interruptedCoveredWalDirectoryRecovered opened _ => opened = input
  | .planWalCollection, .walCollectionPlan _ => True
  | .rotateWal, .rotatedWal => True
  | .rotateThenCloseAndReopen input, .rotationErrorRecovered opened _ => opened = input
  | .rotateThenPowerLossAndReopen input, .rotationCrashRecovered opened _ _ => opened = input
  | .interruptedRotationThenReopen input, .interruptedRotationRecovered opened _ => opened = input
  | .collectObsoleteRuns held, .collectedObsoleteRuns issued => issued = held
  | .collectObsoleteRuns held, .obsoleteRunCollectionError issued _ => issued = held
  | .interruptedRunUnlinkThenReopen held input, .interruptedRunUnlinkRecovered issued opened =>
    issued = held ∧ opened = input
  | .openContended input, .contendedOpenRejected issued _ => issued = input
  | .closeThenRetryMarkedBarriers inputs input, .markedBarrierRetriesRecovered opened attempts =>
    attempts.map (·.input) = inputs ∧ opened = input
  | .closeThenRetryAndReopen inputs input, .rejectedOpenSequenceRecovered attempted opened _ =>
    attempted = inputs ∧ opened = input
  | .retryObsoleteRunCollection held failedAttempts, .collectedObsoleteRunsAfterRetries issued errors =>
    issued = held ∧ errors.length = failedAttempts
  | .rewriteRun request, .rewroteRun issued _ => issued = request
  | .rewriteRunThenCheckpointAndReopen request input, .rewroteRunCheckpointAndReopened issued opened =>
    issued = request ∧ opened = input
  | .closeAndReopen input, .closedAndReopened opened _ => opened = input
  | .closeAfterRetriesAndReopen input failedAttempts, .closedAfterRetries opened errors _ =>
    opened = input ∧ errors.length = failedAttempts
  | .readyExitThenReopen input, .readyExitRecovered opened _ => opened = input
  | .interruptedCloseThenReopen input, .interruptedCloseRecovered opened _ => opened = input
  | .interruptedCheckpointThenReopen input, .interruptedCheckpointRecovered opened _ => opened = input
  | .interruptedCheckpointRunDirectoryThenReopen input, .interruptedEarlyCheckpointRecovered opened .syncRunsDirectory _ _ =>
    opened = input
  | .writeThenCloseAndReopen request input, .uncertainWriteRecovered submitted opened _ _ _ =>
    submitted = request ∧ opened = input
  | .writeThenPowerLossAndReopen request input, .uncertainWriteCrashRecovered submitted opened _ _ _ =>
    submitted = request ∧ opened = input
  | .writeThenPowerLossStageRetryAndReopen request failedInput input,
      .uncertainWriteStageRetryRecovered submitted failed opened _ _ _ =>
    submitted = request ∧ failed = failedInput ∧ opened = input
  | .writeThenInterruptedCloseAndReopen request input, .uncertainWriteInterruptedCloseRecovered submitted opened _ _ _ =>
    submitted = request ∧ opened = input
  | .interruptedAppendThenReopen request input, .interruptedAppendRecovered submitted opened _ =>
    submitted = request ∧ opened = input
  | .interruptedAppendThenPowerLossAndReopen request input, .interruptedAppendCrashRecovered submitted opened _ =>
    submitted = request ∧ opened = input
  | .writeThenCloseRetriesAndReopen request input release failedAttempts,
      .uncertainWriteCloseRetriesRecovered submitted opened _ disposed errors _ _ =>
    submitted = request ∧ opened = input ∧ disposed = release ∧ errors.length = failedAttempts
  | .writeThenExitAndReopen request input rejected, .uncertainWriteExitRecovered submitted opened _ calls _ _ _ =>
    submitted = request ∧ opened = input ∧ calls = rejected
  | .writeThenClientCallsAndReopen request input calls,
      .uncertainWriteClientCallsRecovered submitted opened _ returned _ _ =>
    submitted = request ∧ opened = input ∧ returned.map (·.instruction) = calls
  | .interruptedMarkerThenReopen request input, .interruptedMarkerRecovered submitted opened _ _ =>
    submitted = request ∧ opened = input
  | .collectThenCloseAndReopen input, .collectionErrorRecovered opened _ => opened = input
  | .snapshotControl request, .snapshotControl issued _ => HEq issued request
  | .snapshotHandleRead issuer handle request, .snapshotHandleRead supplied observed issued _ _ =>
    supplied = issuer ∧ observed = handle ∧ HEq issued request
  | _, _ => False

inductive NativeExecutionInstructions : List NativeExecutionInstruction → List NativeExecutionEvent → Prop where
  | empty : NativeExecutionInstructions [] []
  | step (prior : NativeExecutionInstructions instructions events)
      (matched : instruction.Matches event) :
      NativeExecutionInstructions (instructions ++ [instruction]) (events ++ [event])

/-- Reports for the next supported native operation. Each constructor
supplies local observations at the reached state. The returned session,
writer and client replay are derived by the corresponding step. -/
inductive NativeExecutionObservation (current : NativeReadPosition history log) : Type 1 where
  | snapshot (sequence : UInt64) (request : SnapshotReadRequest α)
      (floor : current.state.writer.installed.table.pins.floor ≤ sequence)
      (committed : sequence ≤ current.state.writer.installed.table.committed)
  | write (prepared : NativeReadyWritePreparation current.state) (observed : NativeReadyWriteReport prepared)
      (request : WriteRequest) (rows : request.rows = prepared.rows)
  | restart (crash : NativeReadyQuietCrash current.state) (input : FilePath)
      (observe : ∀ layout : CanonicalKeeperLayout crash.retry.image current.state.writer.history,
        layout.target = current.state.writer.target → Prepared crash.retry.image layout.target layout.plan →
        ∀ selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
          crash.retry.image.directory.active.manifest current.state.writer.checkpoint,
        Nonempty (NativeReadyRestartReads crash input layout selected))
  | checkpoint {image : Type} {attempt : SegmentedCheckpointReport current.state.session.directory current.state.writer}
      {reports : CheckpointCompletionReports (CensusDirectoryCache × image) attempt}
      (observed : NativeReadyCheckpoint current.state reports)
  | collectCoveredWal (observed : NativeReadyWalCollection current.state)
      (completed : observed.barrier.outcome = .completed)
  | rejectsCoveredWalPlan (observed : NativeWalPlanningObservation current.state) (cause : IO.Error)
      (rejected : observed.extents.result = .error cause)
  | coveredWalUnlinkErrorThenPowerLossAndReopen (input : FilePath) (error : NativeCoveredWalUnlinkError current.state)
      (crash : NativeCoveredWalUnlinkErrorCrash error) (observe : crash.ReopenReports input)
  | interruptedCoveredWalDirectoryThenReopen (input : FilePath) {stop : NativeCoveredWalDirectoryStop current.state}
      (crash : NativeCoveredWalDirectoryCrash stop) (observe : crash.ReopenReports input)
  | interruptedCoveredWalUnlinkThenReopen (input : FilePath) {stop : NativeCoveredWalUnlinkStop current.state}
      (crash : NativeCoveredWalUnlinkCrash stop)
      (observe : ∀ layout : CanonicalKeeperLayout crash.observed.retry.image current.state.writer.history,
        layout.target = current.state.writer.target → Prepared crash.observed.retry.image layout.target layout.plan →
        ∀ selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
          crash.observed.retry.image.directory.active.manifest current.state.writer.checkpoint,
        Nonempty (NativeReadyRestartReads crash.observed input layout selected))
  | closeAndReopen (input : FilePath) (observed : NativeCloseReopenObservation current.state input)
  | closeAfterRetriesAndReopen (input : FilePath) (observed : NativeReadyCloseRetryObservation current.state input)
  | readyExitThenReopen (input : FilePath) (seen : NativeReadyProcessExitObservation current.state input)
  | interruptedCloseThenReopen (input : FilePath) (observed : NativeInterruptedCloseReopenObservation current.state input)
  | interruptedCheckpointThenReopen (input : FilePath) (observed : NativePendingCheckpointCrashObservation current.state input)
  | interruptedCheckpointRunDirectoryThenReopen (input : FilePath) {image : Type}
      {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
      {stop : NativeCheckpointRunDirectoryStop (image := image) current.state cut}
      (reboot : NativeCheckpointRunDirectoryReboot stop) (valid : current.state.Valid) (plan : reboot.Plan valid)
      (reader : NativeReadyRestartReads (reboot.observed valid) input plan.layout plan.selected)
  | writeThenCloseAndReopen (observed : NativeUncertainWriteObservation current.state)
  | writeThenPowerLossAndReopen (input : FilePath) (observed : NativeUncertainWriteCrashObservation current.state input)
  | writeThenPowerLossStageRetryAndReopen (failedInput input : FilePath) (write : NativeReadyWriteFailure current.state)
      (inspect : ∀ cache, write.returnedAt cache → Nonempty (NativePendingWriteCensus current.state cache))
      (observe : ∀ pending : NativePendingWrite current, pending.write = write →
        Nonempty (NativeUncertainStageRetryObservation pending failedInput input))
  | writeThenInterruptedCloseAndReopen (input : FilePath) (write : NativeReadyWriteFailure current.state)
      (inspect : ∀ cache, write.returnedAt cache → Nonempty (NativePendingWriteCensus current.state cache))
      (observe : ∀ pending : NativePendingWrite current, pending.write = write →
        Nonempty (NativePoisonedCloseReopenObservation pending input))
  | interruptedMarkerThenReopen (input : FilePath)
      {prepared : NativeReadyWritePreparation current.state} {stop : NativeMarkerPublicationStop prepared}
      (crash : NativeMarkerPublicationCrash stop)
      (observe : ∀ chosen, ∀ layout : CanonicalKeeperLayout crash.retry.image chosen,
        (chosen = current.state.writer.history ∨ chosen = current.state.writer.history ++ prepared.batch) →
        Prepared crash.retry.image layout.target layout.plan →
        ∀ selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
          crash.retry.image.directory.active.manifest current.state.writer.checkpoint,
        Nonempty (NativeMarkerPublicationCrashReads crash input layout selected))
  | writeThenExitAndReopen (input : FilePath) (failedWrite : NativeReadyWriteFailure current.state)
      (rejected : List NativeInactiveRequest)
      (inspect : ∀ cache, failedWrite.returnedAt cache → Nonempty (NativePendingWriteCensus current.state cache))
      (observe : ∀ pending : NativePendingWrite current, pending.write = failedWrite →
        ∃ seen : NativePendingWriteProcessExit pending, seen.requests = rejected ∧
          pending.write.ReleasedMarkedReports input seen.census
            (pending.observed.bindings (current.state.session.directory.file .lock)))
  | writeThenClientCallsAndReopen (input : FilePath) (failedWrite : NativeReadyWriteFailure current.state)
      (calls : List NativePendingClientInstruction)
      (inspect : ∀ cache, failedWrite.returnedAt cache → Nonempty (NativePendingWriteCensus current.state cache))
      (observe : ∀ pending : NativePendingWrite current, pending.write = failedWrite →
        ∃ seen : NativePendingClientRecovery pending input, seen.events.map (·.instruction) = calls)
  | writeThenCloseRetriesAndReopen (input : FilePath) (failedWrite : NativeReadyWriteFailure current.state)
      (release : PendingCloseRelease) (failedAttempts : Nat)
      (inspect : ∀ cache, failedWrite.returnedAt cache → Nonempty (NativePendingWriteCensus current.state cache))
      (observe : ∀ pending : NativePendingWrite current, pending.write = failedWrite →
        ∃ seen : NativePendingCloseRecovery pending input,
          seen.release = release ∧ seen.errors.length = failedAttempts)
  | interruptedAppendThenPowerLossAndReopen (input : FilePath)
      {prepared : NativeReadyWritePreparation current.state} {stop : NativeFirstAppendStop prepared}
      (crash : NativeFirstAppendCrash stop)
      (observe : ∀ layout : CanonicalKeeperLayout crash.retry.image current.state.writer.history,
        BatchAppendInterruption.PreparedRetry current.state.writer layout →
        ∀ selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
          crash.retry.image.directory.active.manifest current.state.writer.checkpoint,
        Nonempty (NativeFirstAppendCrashReads crash input layout selected))
  | interruptedAppendThenReopen (input : FilePath) {prepared : NativeReadyWritePreparation current.state}
      (stop : NativeFirstAppendStop prepared) (exited : NativeFirstAppendExit stop)
      (observe : ∀ layout : CanonicalKeeperLayout exited.retry.image current.state.writer.history,
        BatchAppendInterruption.PreparedRetry current.state.writer layout →
        ∀ selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
          exited.retry.image.directory.active.manifest current.state.writer.checkpoint,
        Nonempty (NativeFirstAppendExitReads exited input layout selected))
  | collectThenCloseAndReopen (input : FilePath) (observed : NativeCollectionReopenObservation current.state input)
  | writePreflight (request : WriteRequest) (observed : NativeWritePreflightObservation current.state request)
  | snapshotControl (observed : NativeSnapshotUpdateObservation current.state α)
  | snapshotHandleRead (observed : NativeSnapshotHandleObservation current.state.session) (request : SnapshotReadRequest α)
  | checkpointRejected (cause : IO.Error) (preflight : CheckpointPreflight (.ready current.state.writer.installed) (.error cause))
  | checkpointThenCloseAndReopen (input : FilePath) (observed : NativeCheckpointReopenObservation current.state input)
  | checkpointRunFileErrorThenReopen (input : FilePath)
      (seen : NativeCheckpointRunFileReopenObservation current.state input)
  | checkpointManifestSyncErrorThenReopen (input : FilePath)
      (seen : NativeCheckpointManifestSyncReopenObservation current.state input)
  | checkpointFirstBarrierErrorThenReopen (input : FilePath) (seen : NativeEarlyCheckpointReopenObservation current.state input)
  | coveredWalUnlinkErrorThenReopen (input : FilePath) (seen : NativeCoveredWalUnlinkErrorReopen current.state input)
  | checkpointManifestRenameErrorThenPowerLossAndReopen (input : FilePath) {image : Type}
      {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
      {report : NativeCheckpointManifestRenameError (image := image) current.state cut}
      (crash : NativeCheckpointManifestRenameCrash report)
      (observe : ∀ plan : crash.Plan, Nonempty (NativeCheckpointManifestRenameReads crash input plan))
  | planWalCollection (observed : NativeWalPlanningObservation current.state)
  | rotateCreated (reported : NativeReadyCreatedRotation current.state)
  | rotateExisting (reported : NativeReadyExistingRotation current.state)
  | rotateEmpty (empty : current.state.writer.installed.walBytes / WAL.frameSize ≤ current.state.writer.installed.activeFirst)
  | rotateThenCloseAndReopen (input : FilePath) (cause : IO.Error)
      (failure : NativeRotationDirectoryFailure current.state (some cause))
      (observe : ∀ valid : current.state.Valid, Nonempty (NativeRotationErrorReopenObservation failure valid input))
  | rotateThenPowerLossAndReopen (input : FilePath) {cause : IO.Error}
      {failure : NativeRotationDirectoryFailure current.state (some cause)}
      (crash : NativeRotationErrorCrash failure)
      (observe : ∀ plan : crash.Plan current.readPrefix.refines.1,
        ∀ selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
          crash.retry.image.directory.active.manifest current.state.writer.checkpoint,
        Nonempty (NativeRotationCrashReads crash input plan selected))
  | interruptedRotationThenReopen (input : FilePath) {stop : NativeRotationDirectoryStop current.state}
      (crash : NativeRotationErrorCrash stop)
      (observe : ∀ plan : crash.Plan current.readPrefix.refines.1,
        ∀ selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
          crash.retry.image.directory.active.manifest current.state.writer.checkpoint,
        Nonempty (NativeRotationCrashReads crash input plan selected))
  | checkpointThenPowerLossAndReopen (input : FilePath) (observed : NativeCheckpointCrashObservation current.state input)
  | collectObsoleteRuns (observed : NativeObsoleteRunCollection current.state)
  | interruptedRunUnlinkThenReopen (input : FilePath) {cut : NativeObsoleteRunUnlinkCut current.state}
      (stop : NativeObsoleteRunUnlinkStop cut) (crash : NativeObsoleteRunUnlinkCrash cut)
      (observe : ∀ layout : CanonicalKeeperLayout crash.observed.retry.image current.state.writer.history,
        layout.target = current.state.writer.target → Prepared crash.observed.retry.image layout.target layout.plan →
        ∀ selected : SelectedIntegrityCheckpoint crash.runs
          crash.observed.retry.image.directory.active.manifest current.state.writer.checkpoint,
        Nonempty (NativeReadyRestartReads crash.observed input layout selected))
  | retryObsoleteRunCollection {held errors initial before}
      {retryAt : NativeReadPosition history log}
      (prior : NativeObsoleteRunUnlinkRetries current initial held retryAt before errors)
      (retry : NativeObsoleteRunCollection retryAt.state) (sameImage : retry.initial = before)
      (sameHolds : retry.reports.held = held)
  | rewriteRun (request : RunMaintenance)
  | rewriteRunThenCheckpointAndReopen (request : RunMaintenance) (input : FilePath)
      (observe : NativeRunMaintenanceReopenObservation current.state request input)
  | obsoleteRunCollectionError (observed : NativeObsoleteRunBarrierError current.state)
  | obsoleteRunUnlinkError (cut : NativeObsoleteRunUnlinkCut current.state) (error : NativeObsoleteRunUnlinkError cut)
  | openContended (input : FilePath) (seen : NativeContendedOpen current.state input)
      (drop : LockReferenceDrop) (retired : drop = seen.slot.closeEvent)
  | closeThenRetryMarkedBarriers (inputs : List FilePath) (input : FilePath)
      (seen : NativeCloseMarkedBarrierObservation current.state inputs input)
  | closeThenRetryAndReopen (inputs : List FilePath) (input : FilePath)
      (observed : NativeRejectedOpenReopenObservation current.state inputs input)

def NativeExecutionObservation.instruction : NativeExecutionObservation current → NativeExecutionInstruction
  | .snapshot sequence request _ _ => .snapshot sequence request
  | .write _ _ request _ => .write request
  | .restart _ input _ => .restart input
  | .checkpoint _ => .checkpoint
  | .collectCoveredWal _ _ | .rejectsCoveredWalPlan _ _ _ => .collectCoveredWal
  | .interruptedCoveredWalUnlinkThenReopen input _ _ => .interruptedCoveredWalUnlinkThenReopen input
  | .interruptedCoveredWalDirectoryThenReopen input _ _ => .interruptedCoveredWalDirectoryThenReopen input
  | .coveredWalUnlinkErrorThenPowerLossAndReopen input _ _ _ => .coveredWalUnlinkErrorThenPowerLossAndReopen input
  | .closeAndReopen input _ => .closeAndReopen input
  | .closeAfterRetriesAndReopen input seen => .closeAfterRetriesAndReopen input seen.attempts.length
  | .readyExitThenReopen input _ => .readyExitThenReopen input
  | .interruptedCloseThenReopen input _ => .interruptedCloseThenReopen input
  | .interruptedCheckpointThenReopen input _ => .interruptedCheckpointThenReopen input
  | .interruptedCheckpointRunDirectoryThenReopen input _ _ _ _ => .interruptedCheckpointRunDirectoryThenReopen input
  | .writeThenCloseAndReopen observed => .writeThenCloseAndReopen observed.write.request observed.input
  | .writeThenPowerLossAndReopen input observed => .writeThenPowerLossAndReopen observed.write.request input
  | .writeThenPowerLossStageRetryAndReopen failedInput input failedWrite _ _ =>
    .writeThenPowerLossStageRetryAndReopen failedWrite.request failedInput input
  | .writeThenInterruptedCloseAndReopen input failedWrite _ _ =>
    .writeThenInterruptedCloseAndReopen failedWrite.request input
  | .interruptedAppendThenReopen input stop _ _ => .interruptedAppendThenReopen stop.request input
  | .interruptedAppendThenPowerLossAndReopen (stop := stop) input _ _ =>
    .interruptedAppendThenPowerLossAndReopen stop.request input
  | .writeThenExitAndReopen input failedWrite rejected _ _ => .writeThenExitAndReopen failedWrite.request input rejected
  | .writeThenClientCallsAndReopen input failedWrite calls _ _ =>
    .writeThenClientCallsAndReopen failedWrite.request input calls
  | .writeThenCloseRetriesAndReopen input failedWrite release failedAttempts _ _ =>
    .writeThenCloseRetriesAndReopen failedWrite.request input release failedAttempts
  | .interruptedMarkerThenReopen (stop := stop) input _ _ => .interruptedMarkerThenReopen stop.request input
  | .collectThenCloseAndReopen input _ => .collectThenCloseAndReopen input
  | .writePreflight request _ => .write request
  | .snapshotControl observed => .snapshotControl observed.update
  | .snapshotHandleRead observed request => .snapshotHandleRead observed.issuer observed.handle request
  | .checkpointRejected _ _ => .checkpoint
  | .checkpointThenCloseAndReopen input _ => .checkpointThenCloseAndReopen input
  | .checkpointRunFileErrorThenReopen input seen => .checkpointRunFileErrorThenReopen input seen.error.index
  | .checkpointManifestSyncErrorThenReopen input _ => .checkpointManifestSyncErrorThenReopen input
  | .checkpointFirstBarrierErrorThenReopen input _ => .checkpointFirstBarrierErrorThenReopen input
  | .coveredWalUnlinkErrorThenReopen input _ => .coveredWalUnlinkErrorThenReopen input
  | .planWalCollection _ => .planWalCollection
  | .rotateCreated _ | .rotateExisting _ | .rotateEmpty _ => .rotateWal
  | .rotateThenCloseAndReopen input _ _ _ => .rotateThenCloseAndReopen input
  | .rotateThenPowerLossAndReopen input _ _ => .rotateThenPowerLossAndReopen input
  | .interruptedRotationThenReopen input _ _ => .interruptedRotationThenReopen input
  | .checkpointThenPowerLossAndReopen input _ => .checkpointThenPowerLossAndReopen input
  | .checkpointManifestRenameErrorThenPowerLossAndReopen input _ _ =>
    .checkpointManifestRenameErrorThenPowerLossAndReopen input
  | .collectObsoleteRuns observed => .collectObsoleteRuns observed.reports.held
  | .interruptedRunUnlinkThenReopen (cut := cut) input _ _ _ => .interruptedRunUnlinkThenReopen cut.plan.reports.held input
  | .retryObsoleteRunCollection (held := held) (errors := errors) _ _ _ _ => .retryObsoleteRunCollection held errors.length
  | .rewriteRun request => .rewriteRun request
  | .rewriteRunThenCheckpointAndReopen request input _ => .rewriteRunThenCheckpointAndReopen request input
  | .obsoleteRunCollectionError observed => .collectObsoleteRuns observed.reports.held
  | .obsoleteRunUnlinkError cut _ => .collectObsoleteRuns cut.plan.reports.held
  | .openContended input _ _ _ => .openContended input
  | .closeThenRetryMarkedBarriers inputs input _ => .closeThenRetryMarkedBarriers inputs input
  | .closeThenRetryAndReopen inputs input _ => .closeThenRetryAndReopen inputs input

theorem NativeExecutionPosition.observesStep (current : NativeExecutionPosition)
    (observed : NativeExecutionObservation current.ready) :
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
  | checkpoint observed =>
    obtain ⟨_, step⟩ := current.checkpoints observed
    exact ⟨_, _, step, trivial⟩
  | collectCoveredWal observed completed =>
    obtain ⟨_, step⟩ := current.collectsCoveredWal observed completed
    exact ⟨_, _, step, trivial⟩
  | rejectsCoveredWalPlan observed cause rejected =>
    have planned := (current.ready.plansWalCollection observed).1
    simp only [rejected] at planned
    exact ⟨_, current, .rejectsCoveredWalPlan current observed cause rejected planned, trivial⟩
  | coveredWalUnlinkErrorThenPowerLossAndReopen _ error crash observe =>
    have recovery := current.ready.recoversCoveredWalUnlinkErrorPowerLoss error crash observe
    obtain ⟨_, _, _, _, seen, state, reached⟩ := recovery.reopened
    exact ⟨_, _, .recoverCoveredWalUnlinkErrorCrash current error crash recovery seen state reached, rfl⟩
  | interruptedCoveredWalDirectoryThenReopen _ crash observe =>
    have recovery := current.ready.recoversInterruptedCoveredWalDirectory _ crash observe
    obtain ⟨_, _, _, _, seen, state, reached⟩ := recovery.reopened
    exact ⟨_, _, .recoverInterruptedCoveredWalDirectory current crash recovery seen state reached, rfl⟩
  | interruptedCoveredWalUnlinkThenReopen _ crash observe =>
    have recovery := current.ready.recoversInterruptedCoveredWalUnlink _ crash observe
    obtain ⟨_, _, layout, selected, seen, state, reached⟩ := recovery.reopened
    exact ⟨_, _, .recoverInterruptedCoveredWalUnlink current crash recovery seen state reached, rfl⟩
  | closeAndReopen _ observed =>
    obtain ⟨next, reopened⟩ := current.ready.closesAndReopens observed
    exact ⟨_, _, .closeAndReopen current observed next reopened, rfl⟩
  | closeAfterRetriesAndReopen _ observed =>
    obtain ⟨next, reopened⟩ := current.ready.closesAndReopensAfterRetries observed
    exact ⟨_, _, .closesAfterRetries current observed next reopened, rfl, List.length_map ..⟩
  | readyExitThenReopen _ seen =>
    obtain ⟨next, reopened⟩ := current.ready.reopensAfterProcessExit seen
    exact ⟨_, _, .recoverReadyExit current seen next reopened, rfl⟩
  | interruptedCloseThenReopen _ observed =>
    obtain ⟨next, reopened⟩ := current.ready.recoversInterruptedClose observed
    exact ⟨_, _, .recoverInterruptedClose current observed next reopened, rfl⟩
  | interruptedCheckpointThenReopen _ observed =>
    obtain ⟨next, reopened⟩ := current.ready.recoversStoppedCheckpoint observed
    exact ⟨_, _, .recoverInterruptedCheckpoint current observed next reopened, rfl⟩
  | interruptedCheckpointRunDirectoryThenReopen _ reboot valid plan reader =>
    obtain ⟨next, reopened⟩ := current.ready.recoversStoppedCheckpointRunDirectory reboot valid plan reader
    exact ⟨_, _, .recoverInterruptedCheckpointRunDirectory current reboot reader next reopened, rfl⟩
  | writeThenCloseAndReopen observed =>
    obtain ⟨retained, next, recovered⟩ := current.ready.recoversUncertainWrite observed
    exact ⟨_, _, .recoverUncertainWrite current observed retained next recovered, rfl, rfl⟩
  | writeThenPowerLossAndReopen _ observed =>
    obtain ⟨retained, next, reopened⟩ := current.ready.recoversUncertainWriteAfterPowerLoss observed
    exact ⟨_, _, .recoverUncertainWriteCrash current observed retained next reopened, rfl, rfl⟩
  | writeThenPowerLossStageRetryAndReopen _ _ failedWrite inspect observe =>
    obtain ⟨pending, same, _⟩ := current.ready.stopsAtUncertainWrite failedWrite inspect
    obtain ⟨seen⟩ := observe pending same
    obtain ⟨next, ⟨reopened⟩⟩ := pending.reopensAfterOldMarkerStageError seen
    exact ⟨_, _, .recoverUncertainWriteStageRetry current pending seen next reopened,
      congrArg NativeReadyWriteFailure.request same, rfl, rfl⟩
  | writeThenInterruptedCloseAndReopen _ write inspect observe =>
    obtain ⟨pending, same, _⟩ := current.ready.stopsAtUncertainWrite write inspect
    obtain ⟨seen⟩ := observe pending same
    obtain ⟨retained, next, reopened⟩ := pending.recoversInterruptedClose seen
    exact ⟨_, _, .recoverUncertainWriteInterruptedClose current pending seen retained next reopened,
      congrArg NativeReadyWriteFailure.request same, rfl⟩
  | interruptedMarkerThenReopen _ crash observe =>
    obtain ⟨retained, next, reopened⟩ := current.ready.recoversInterruptedMarker crash observe
    exact ⟨_, _, .recoverInterruptedMarker current crash retained next reopened, rfl, rfl⟩
  | writeThenExitAndReopen _ failedWrite _ inspect observe =>
    obtain ⟨pending, same, _⟩ := current.ready.stopsAtUncertainWrite failedWrite inspect
    obtain ⟨seen, rejected, reports⟩ := observe pending same
    obtain ⟨retained, next, reopened⟩ := pending.recoversAfterProcessExit seen reports
    exact ⟨_, _, .recoverUncertainWriteAfterExit current pending seen retained next reopened,
      congrArg NativeReadyWriteFailure.request same, rfl, rejected⟩
  | writeThenClientCallsAndReopen _ failedWrite _ inspect observe =>
    obtain ⟨pending, same, _⟩ := current.ready.stopsAtUncertainWrite failedWrite inspect
    obtain ⟨seen, calls⟩ := observe pending same
    obtain ⟨retained, next, reopened⟩ := pending.recoversAfterClientCalls seen
    exact ⟨_, _, .recoverUncertainWriteAfterClientCalls current pending seen retained next reopened,
      congrArg NativeReadyWriteFailure.request same, rfl, calls⟩
  | writeThenCloseRetriesAndReopen _ failedWrite _ _ inspect observe =>
    obtain ⟨pending, same, _⟩ := current.ready.stopsAtUncertainWrite failedWrite inspect
    obtain ⟨seen, release, count⟩ := observe pending same
    obtain ⟨retained, next, reopened⟩ := seen.reopens
    exact ⟨_, _, .recoverUncertainWriteAfterCloseRetries current pending seen retained next reopened,
      congrArg NativeReadyWriteFailure.request same, rfl, release, count⟩
  | interruptedAppendThenPowerLossAndReopen _ crash observe =>
    obtain ⟨next, reopened⟩ := current.ready.recoversFirstAppendPowerLoss crash observe
    exact ⟨_, _, .recoverInterruptedAppendCrash current crash next reopened, rfl, rfl⟩
  | interruptedAppendThenReopen input stop exited observe =>
    obtain ⟨next, reopened⟩ := current.ready.recoversFirstAppendAfterExit stop exited input observe
    exact ⟨_, _, .recoverInterruptedAppend current stop exited next reopened, rfl, rfl⟩
  | collectThenCloseAndReopen _ observed =>
    obtain ⟨next, reopened⟩ := current.ready.recoversCollectionBarrier observed
    exact ⟨_, _, .recoverCollectionError current observed next reopened, rfl⟩
  | writePreflight _ observed =>
    exact ⟨_, current, .writePreflight current observed (current.ready.preflightsWrite observed), rfl⟩
  | snapshotControl observed =>
    obtain ⟨next, returned⟩ := current.ready.updatesSnapshot observed
    exact ⟨_, _, .snapshotControl current observed next returned, HEq.rfl⟩
  | snapshotHandleRead observed request =>
    obtain ⟨result, recorded, next, returned⟩ := current.ready.readsHandle observed request
    exact ⟨_, _, .snapshotHandleRead current observed request result recorded next returned, rfl, rfl, HEq.rfl⟩
  | checkpointRejected cause preflight =>
    exact ⟨_, current, .checkpointRejected current cause (current.ready.rejectsCheckpoint preflight), trivial⟩
  | checkpointRunFileErrorThenReopen _ seen =>
    obtain ⟨next, reopened⟩ := current.ready.recoversCheckpointRunFileError seen
    exact ⟨_, _, .recoverCheckpointRunFileError current seen next reopened, rfl, rfl⟩
  | checkpointManifestSyncErrorThenReopen _ seen =>
    obtain ⟨next, reopened⟩ := current.ready.recoversCheckpointManifestSyncError seen
    exact ⟨_, _, .recoverCheckpointManifestSyncError current seen next reopened, rfl⟩
  | checkpointFirstBarrierErrorThenReopen _ seen =>
    obtain ⟨next, reopened⟩ := current.ready.recoversEarlyCheckpointError seen
    exact ⟨_, _, .recoverEarlyCheckpointError current seen next reopened, rfl⟩
  | coveredWalUnlinkErrorThenReopen _ seen =>
    obtain ⟨next, reopened⟩ := current.ready.recoversCoveredWalUnlinkError seen
    exact ⟨_, _, .recoverCoveredWalUnlinkError current seen next reopened, rfl⟩
  | checkpointManifestRenameErrorThenPowerLossAndReopen _ crash observe =>
    obtain ⟨next, reopened⟩ := current.ready.recoversCheckpointManifestRenamePowerLoss crash observe
    exact ⟨_, _, .recoverCheckpointManifestRenameError current crash next reopened, rfl⟩
  | checkpointThenCloseAndReopen _ observed =>
    obtain ⟨next, reopened⟩ := current.ready.recoversCheckpointDirectoryError observed
    exact ⟨_, _, .recoverCheckpointError current observed next reopened, rfl⟩
  | planWalCollection observed =>
    exact ⟨_, current, .planWalCollection current observed (current.ready.plansWalCollection observed).1, trivial⟩
  | rotateCreated reported =>
    obtain ⟨next, rotated⟩ := current.ready.rotatesCreated reported
    exact ⟨_, _, .rotateCreated current reported next rotated, trivial⟩
  | rotateExisting reported =>
    obtain ⟨next, rotated⟩ := current.ready.rotatesExisting reported
    exact ⟨_, _, .rotateExisting current reported next rotated, trivial⟩
  | rotateEmpty empty =>
    refine ⟨_, current, .rotateEmpty current ?_, trivial⟩
    intro image files lookup read create sync release
    dsimp only
    rw [current.ready.readPrefix.refines.1.phase]
    exact runObservedRotationWithReset_empty _ _ _ lookup read create sync release empty
  | rotateThenCloseAndReopen _ _ _ observe =>
    obtain ⟨observed⟩ := observe current.ready.readPrefix.refines.1
    obtain ⟨next, reopened⟩ := current.ready.recoversRotationError observed
    exact ⟨_, _, .recoverRotationError current observed next reopened, rfl⟩
  | rotateThenPowerLossAndReopen _ crash observe =>
    obtain ⟨next, reopened⟩ := current.ready.recoversRotationPowerLoss crash observe
    exact ⟨_, _, .recoverRotationCrash current crash next reopened, rfl⟩
  | interruptedRotationThenReopen _ crash observe =>
    obtain ⟨next, reopened⟩ := current.ready.recoversInterruptedRotation crash observe
    exact ⟨_, _, .recoverInterruptedRotation current crash next reopened, rfl⟩
  | checkpointThenPowerLossAndReopen _ observed =>
    obtain ⟨next, reopened⟩ := current.ready.recoversCheckpointCrash observed
    exact ⟨_, _, .recoverCheckpointCrash current observed next reopened, rfl⟩
  | collectObsoleteRuns observed =>
    obtain ⟨next, returned⟩ := current.ready.collectsObsoleteRuns observed
    exact ⟨_, _, .collectObsoleteRuns current observed next returned, rfl⟩
  | interruptedRunUnlinkThenReopen _ stop crash observe =>
    obtain ⟨next, reopened⟩ := current.ready.recoversInterruptedRunUnlink stop crash observe
    exact ⟨_, _, .recoverInterruptedRunUnlink current stop crash next reopened, rfl, rfl⟩
  | retryObsoleteRunCollection prior retry sameImage sameHolds =>
    obtain ⟨next, returned, _⟩ := prior.completes retry sameImage sameHolds
    exact ⟨_, _, .collectsObsoleteRunsAfterRetries current prior retry sameImage sameHolds next returned, rfl, rfl⟩
  | rewriteRun request =>
    obtain ⟨result, next, returned⟩ := current.ready.rewritesRun request
    exact ⟨_, _, .rewriteRun current request result next returned, rfl⟩
  | rewriteRunThenCheckpointAndReopen request input seen =>
    obtain ⟨next, reopened⟩ := current.ready.rewritesRunCheckpointAndReopens request seen.updated seen.checkpoint
      seen.binding input seen.observe
    exact ⟨_, _, .rewriteRunCheckpointAndReopen current seen next reopened, rfl, rfl⟩
  | obsoleteRunCollectionError observed =>
    obtain ⟨next, returned⟩ := current.ready.reachesObsoleteRunBarrierError observed
    exact ⟨_, _, .obsoleteRunCollectionError current observed next returned, rfl⟩
  | obsoleteRunUnlinkError cut error =>
    obtain ⟨next, returned⟩ := current.ready.reachesObsoleteRunUnlinkError cut error
    exact ⟨_, _, .obsoleteRunUnlinkError current cut error next returned, rfl⟩
  | openContended _ seen drop retired =>
    have disposed : (current.ready.state.census.insert seen.slot seen.free).afterDrops [drop] = current.ready.state.census :=
      retired.symm ▸ checkpointTemporaryClose _ _ _
    exact ⟨_, current, .rejectsContendedOpen current seen drop retired seen.returns disposed, rfl⟩
  | closeThenRetryMarkedBarriers _ _ seen =>
    obtain ⟨closed, _, _, next, reopened⟩ :=
      current.ready.reopensAfterMarkedBarriers seen.close seen.success seen.lineage seen.files seen.observe
    exact ⟨_, _, .recoverMarkedBarrierRetries current seen closed next reopened, seen.inputsInOrder, rfl⟩
  | closeThenRetryAndReopen _ _ observed =>
    obtain ⟨closed, count, next, reopened⟩ := current.ready.retriesAndReopens observed
    exact ⟨_, _, .recoverRejectedOpenSequence current observed next closed count reopened, rfl, rfl⟩

/-- Supply the primitive reports for the next prescribed instruction
at its reached state. The whole trace and its endpoint are derived from
those reports, in the order of the original instruction list. -/
def NativeExecutionTrace.Reports (start : NativeExecutionPosition)
    (instructions : List NativeExecutionInstruction) : Prop :=
  ∀ issued events current instruction remaining,
    instructions = issued ++ instruction :: remaining →
    NativeExecutionTrace start events current → NativeExecutionInstructions issued events →
    ∃ observed : NativeExecutionObservation current.ready, observed.instruction = instruction

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
          (∀ event ∈ events, event.uncertainBatchWhole) ∧
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
    by simpa [start] using reads, trace.uncertainBatchesWhole, replay⟩

/-- The same ready execution can start after the initial keeper create
failed. The reported cleanup and admitted retry carry the empty image
and actual descriptor inventory to the successful bootstrap. -/
theorem BootstrapZeroCreateError.executesAfterCreateError
    {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
    {calls : BootstrapOpenCalls (Cache BootstrapHandle) directory before}
    {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls} {listed : BootstrapCheckedListing captured}
    {input nextInput : FilePath} (failure : BootstrapZeroCreateError listed) (cleanup : failure.Cleanup)
    (admission : OpenAdmissionReports input directory calls.slot)
    {inventory : DescriptorInventory} {files : LockedFileState WalSegmentRotation.State}
    (disposed : failure.DisposedForRetry inventory files)
    {nextCalls : BootstrapOpenCalls (Cache BootstrapHandle) directory files}
    {nextCapture : BootstrapCacheOpen nextCalls.toBootstrapAdmissionCalls}
    {nextList : BootstrapCheckedListing nextCapture}
    {nextKeeper : BootstrapZeroKeeperRoute nextList} {nextMarker : BootstrapMarkerCustody nextList}
    {opening : OpenAdmissionReports nextInput directory nextCalls.slot}
    (acquired : CapturedBootstrapAdmission nextCapture opening inventory)
    (namespaceView : nextCapture.view = failure.afterView) (root : nextCapture.root = captured.root)
    (publication : BootstrapKeeperMarkerHandoff nextKeeper nextMarker)
    (effects : BootstrapKeeperMarkerHandoff.ReturnedCensus nextMarker) :
    ∃ (boot : BootstrapClientStart directory nextCalls.slot.description (nextCalls.run opening))
      (start : NativeExecutionPosition),
      calls.run admission = .error failure.diagnostic failure.final ∧
      nextCalls.run opening = .ok start.ready.state.session boot.final ∧ start.ready.state.census = effects.reached ∧
      start.history = [] ∧ start.submissions = [] ∧ start.ready.reads = [] ∧
      ∀ instructions, NativeExecutionTrace.Reports start instructions →
        ∃ events last, NativeExecutionInstructions instructions events ∧ NativeExecutionTrace start events last ∧
          InstalledClientReplay last.submissions last.ready.reads last.history
            last.ready.state.writer.installed last.ready.state.session := by
  obtain ⟨failed, _, _, _, _, _, boot, returned, _, _, _, _, _, _, readyPrefix⟩ :=
    failure.reopensAfterCreateError cleanup admission disposed acquired namespaceView root publication effects
  let state : NativeReadyState :=
    ⟨boot.session, boot.writer, effects.reached, nextCapture.cache, nextCalls.slot, nextCapture.cached⟩
  let start : NativeExecutionPosition :=
    ⟨[], [], ⟨.ok state.session (state.census, state.files), state, state, [], readyPrefix⟩⟩
  exact ⟨boot, start, failed, returned, rfl, rfl, rfl, rfl, NativeExecutionTrace.executes start⟩

/-- Every failed first keeper create contributes its own returned diagnostic.
The successful projected bootstrap uses the last attempt's reached files
and inventory before starting the ordinary native execution. -/
theorem BootstrapCreateErrorLineage.executesAfterCreateErrors
    {directory : DiskDirectory} {before atFiles : LockedFileState WalSegmentRotation.State}
    {first : ReleasedBootstrapCreateError directory before} {last : ReleasedBootstrapCreateError directory atFiles}
    {attempts : List ((files : LockedFileState WalSegmentRotation.State) × ReleasedBootstrapCreateError directory files)}
    (lineage : BootstrapCreateErrorLineage first attempts last) {input : FilePath}
    {calls : BootstrapOpenCalls (Cache (DescriptorInventory × DescriptorSlot × Nat)) directory last.retry}
    {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls} {listed : BootstrapCheckedListing captured}
    {keeper : BootstrapZeroKeeperRoute listed} {marker : BootstrapMarkerCustody listed}
    {opening : OpenAdmissionReports input directory calls.slot}
    (acquired : CapturedBootstrapAdmission captured opening last.inventory)
    (namespaceView : captured.view = last.error.afterView) (root : captured.root = last.captured.root)
    (publication : BootstrapKeeperMarkerHandoff keeper marker)
    (effects : BootstrapKeeperMarkerHandoff.ReturnedCensus marker) :
    ∃ (boot : BootstrapClientStart directory calls.slot.description (calls.run opening))
      (start : NativeExecutionPosition),
      (∀ receipt ∈ attempts, receipt.2.calls.run receipt.2.admission =
        .error receipt.2.error.diagnostic receipt.2.error.final) ∧
      calls.run opening = .ok start.ready.state.session boot.final ∧ start.ready.state.census = effects.reached ∧
      start.history = [] ∧ start.submissions = [] ∧ start.ready.reads = [] ∧
      ∀ instructions, NativeExecutionTrace.Reports start instructions →
        ∃ events endPosition, NativeExecutionInstructions instructions events ∧ NativeExecutionTrace start events endPosition ∧
          InstalledClientReplay endPosition.submissions endPosition.ready.reads endPosition.history
            endPosition.ready.state.writer.installed endPosition.ready.state.session := by
  obtain ⟨boot, start, _, opened, census, history, submissions, reads, executes⟩ :=
    last.error.executesAfterCreateError last.cleanup last.admission last.disposed acquired namespaceView root publication effects
  exact ⟨boot, start, fun receipt included => (lineage.returns receipt included).1, opened, census, history, submissions,
    reads, executes⟩

end Alvoki.Storage.DiskSession
