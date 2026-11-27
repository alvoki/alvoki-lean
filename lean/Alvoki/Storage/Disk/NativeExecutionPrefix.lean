import Alvoki.Storage.Disk.NativeExecutionTrace
import Alvoki.Storage.Disk.NativeOpenReferences
import Alvoki.Storage.Disk.NativeExecutionPendingClose
import Alvoki.Storage.Disk.NativeExecutionOrdinaryClose
import Alvoki.Storage.Disk.NativeInactiveSessionCalls
import Alvoki.Storage.Disk.NativeCloseUnlockInterruption
import Alvoki.Storage.Disk.NativePendingRotation
import Alvoki.Storage.Disk.NativePendingCheckpoint
import Alvoki.Storage.Disk.NativeCheckpointRunDirectoryCut
import Alvoki.Storage.Disk.NativeCheckpointRunFileStop
import Alvoki.Storage.Disk.NativePendingFirstAppend
import Alvoki.Storage.Disk.NativePendingMarkerSync
import Alvoki.Storage.Disk.NativePendingMarkerRename
import Alvoki.Storage.Disk.NativePendingMarkerDirectory
import Alvoki.Storage.Disk.NativePendingMarkerStageWrite
import Alvoki.Storage.Disk.NativePendingStagedMarkerSync
import Alvoki.Storage.Disk.NativeObsoleteRunUnlinkCut
import Alvoki.Storage.Disk.NativeCoveredWalUnlinkStop
import Alvoki.Storage.Disk.NativeCoveredWalDirectoryStop
import Alvoki.Storage.Disk.Proofs.Recovery.NativeRejectedOpenLineage
import Alvoki.Storage.Disk.NativeCheckpointRunDirectoryError
import Alvoki.Storage.Disk.NativeCheckpointRunFileError
import Alvoki.Storage.Disk.NativeCheckpointRunDataError
import Alvoki.Storage.Disk.NativeCheckpointManifestSyncError
import Alvoki.Storage.Disk.NativeCheckpointManifestOpenError
import Alvoki.Storage.Disk.NativeCheckpointManifestDataError
import Alvoki.Storage.Disk.NativeCheckpointManifestRenameError
import Alvoki.Storage.Disk.NativeCoveredWalUnlinkError
import Alvoki.Storage.Disk.NativeCheckpointDirectoryError
import Alvoki.Storage.Disk.NativeOpenCheckpointScheduleStop

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

inductive NativeExecutionEndInstruction : Type 1 where
  | ready
  | write (request : WriteRequest)
  | writeThenClose (request : WriteRequest)
  | writeThenInactiveCalls (request : WriteRequest) (calls : List NativeInactiveRequest)
  | writeThenCloseThenInactiveCalls (request : WriteRequest) (calls : List NativeInactiveRequest)
  | closeThenInactiveCalls (calls : List NativeInactiveRequest)
  | close
  | closeThenOpenAttempts (inputs : List FilePath)
  | checkpoint
  | collectCoveredWal
  | collectObsoleteRuns (held : List UInt64)
  | rotateWal

/-- The first open uses the files and census left by the successful
close. Each rejected attempt uses the exact predecessor in the lineage. -/
structure NativeRejectedOpenSequence (current : NativeExecutionPosition) where
  close : NativeReadyClose current.ready.state
  closed : close.report.result = .ok ()
  inputs : List FilePath
  errors : List IO.Error
  after : CensusOpenState
  available : Bool
  reported : NativeRejectedOpenLineage current.ready.state.session.directory
    (current.ready.state.census.inode current.ready.state.owner.description)
    (current.ready.state.census.inode current.ready.state.directorySlot.description)
    (close.report.finished.descriptors, current.ready.state.releasedFiles) inputs errors after available

/-- An execution can stop at a ready session, the return of an
operation that requires recovery, or an interrupted native call.
The reached files and ownership remain available at each endpoint. -/
inductive NativeExecutionEnd (current : NativeExecutionPosition) : Type 1 where
  | ready
  | uncertainWrite (pending : NativePendingWrite current.ready)
  | callsAfterUncertainWrite (pending : NativePendingWrite current.ready) (calls : List NativeInactiveRequest)
  | callsAfterPoisonedClose (pending : NativePendingWrite current.ready) (reported : NativePendingClose pending)
      (unlocked : reported.report.result = .ok ()) (calls : List NativeInactiveRequest)
  | callsAfterReadyClose (reported : NativeReadyClose current.ready.state) (unlocked : reported.report.result = .ok ())
      (calls : List NativeInactiveRequest)
  | interruptedFirstAppend {prepared : NativeReadyWritePreparation current.ready.state}
      (stop : NativeFirstAppendStop prepared)
  | interruptedKeeperSync {prepared : NativeReadyWritePreparation current.ready.state}
      (stop : NativeWriteKeeperSyncStop prepared)
  | interruptedMarkerStageWrite {prepared : NativeReadyWritePreparation current.ready.state}
      (stop : NativeMarkerStageWriteStop prepared)
  | interruptedStagedMarkerSync {prepared : NativeReadyWritePreparation current.ready.state}
      (stop : NativeWriteStagedMarkerSyncStop prepared)
  | interruptedMarkerRename {prepared : NativeReadyWritePreparation current.ready.state}
      (stop : NativeWriteMarkerRenameStop prepared)
  | interruptedMarkerDirectory {prepared : NativeReadyWritePreparation current.ready.state}
      (stop : NativeWriteMarkerDirectoryStop prepared)
  | closeAfterUncertainWrite (pending : NativePendingWrite current.ready) (close : NativePendingClose pending)
  | close (reported : NativeReadyClose current.ready.state)
  | rejectedOpensAfterClose (sequence : NativeRejectedOpenSequence current)
  | interruptedClose
      (cut : NativeCloseUnlockInterruption current.ready.state.session.directory
        current.ready.state.session.descriptor current.ready.state.closeState)
      (owner : cut.slot = current.ready.state.owner)
  | interruptedCloseAfterUncertainWrite (pending : NativePendingWrite current.ready)
      (cut : NativeCloseUnlockInterruption current.ready.state.session.directory
        current.ready.state.session.descriptor pending.poisoned)
      (owner : cut.slot = current.ready.state.owner)
  | checkpointError {image : Type} {cut : CheckpointPowerCut current.ready.state.session.directory current.ready.state.writer}
      (reported : NativeCheckpointDirectoryError (image := image) current.ready.state cut) (physical : reported.Physical)
  | checkpointRunDirectoryError {image : Type}
      {cut : CheckpointPowerCut current.ready.state.session.directory current.ready.state.writer}
      (reported : NativeCheckpointRunDirectoryError (image := image) current.ready.state cut)
  | checkpointManifestSyncError {image : Type}
      {cut : CheckpointPowerCut current.ready.state.session.directory current.ready.state.writer}
      (reported : NativeCheckpointManifestSyncError (image := image) current.ready.state cut)
  | checkpointManifestOpenError {image : Type}
      {cut : CheckpointPowerCut current.ready.state.session.directory current.ready.state.writer}
      (reported : NativeCheckpointManifestOpenError (image := image) current.ready.state cut)
  | checkpointManifestDataError {image : Type}
      {cut : CheckpointPowerCut current.ready.state.session.directory current.ready.state.writer}
      (reported : NativeCheckpointManifestDataError (image := image) current.ready.state cut)
  | checkpointManifestRenameError {image : Type}
      {cut : CheckpointPowerCut current.ready.state.session.directory current.ready.state.writer}
      (reported : NativeCheckpointManifestRenameError (image := image) current.ready.state cut)
  | checkpointRunDataError {image : Type}
      {cut : CheckpointPowerCut current.ready.state.session.directory current.ready.state.writer}
      (reported : NativeCheckpointRunDataError (image := image) current.ready.state cut)
  | checkpointRunFileError {image : Type}
      {cut : CheckpointPowerCut current.ready.state.session.directory current.ready.state.writer}
      (reported : NativeCheckpointRunFileError (image := image) current.ready.state cut)
  | interruptedCheckpoint {image : Type} {cut : CheckpointPowerCut current.ready.state.session.directory current.ready.state.writer}
      (stop : NativeCheckpointDirectoryStop (image := image) current.ready.state cut)
  | interruptedCheckpointRunFile {image : Type}
      {cut : CheckpointPowerCut current.ready.state.session.directory current.ready.state.writer}
      (stop : NativeCheckpointRunFileStop (image := image) current.ready.state cut)
  | interruptedCheckpointRunDirectory {image : Type}
      {cut : CheckpointPowerCut current.ready.state.session.directory current.ready.state.writer}
      (stop : NativeCheckpointRunDirectoryStop (image := image) current.ready.state cut)
  | stoppedCheckpoint {heap : Type} {opened : NativeOpenedHandle heap}
      {position : NativeOpenedPosition opened} (same : position.current = current)
      {primitives : CheckpointPrimitiveCalls CheckpointOpenHandle heap} {fsync : CheckpointFsync heap}
      {stage : CheckpointPublication.Step} {reason : FilePath} {reached : CheckpointWorld heap}
      (stop : NativeCheckpointSourceStop position primitives fsync stage reason reached)
      (poisoned : opened.contents reached.2 opened.phase = some .poisoned)
  | collectionError (reported : NativeReadyWalCollection current.ready.state) (cause : IO.Error)
      (failed : reported.barrier.outcome = .errorBeforeEffect cause ∨ reported.barrier.outcome = .errorAfterEffect cause)
  | coveredWalUnlinkError (reported : NativeCoveredWalUnlinkError current.ready.state)
  | interruptedCoveredWalUnlink (stop : NativeCoveredWalUnlinkStop current.ready.state)
  | interruptedCoveredWalDirectory (stop : NativeCoveredWalDirectoryStop current.ready.state)
  | interruptedObsoleteRunUnlink (cut : NativeObsoleteRunUnlinkCut current.ready.state)
      (stop : NativeObsoleteRunUnlinkStop cut)
  | interruptedRotation (stop : NativeRotationDirectoryStop current.ready.state)
  | rotationError (cause : IO.Error) (failure : NativeRotationDirectoryFailure current.ready.state (some cause))

namespace NativeExecutionEnd

def instruction : NativeExecutionEnd current → NativeExecutionEndInstruction
  | .ready => .ready
  | .uncertainWrite pending => .write pending.write.request
  | .callsAfterUncertainWrite pending calls => .writeThenInactiveCalls pending.write.request calls
  | .callsAfterPoisonedClose pending _ _ calls => .writeThenCloseThenInactiveCalls pending.write.request calls
  | .callsAfterReadyClose _ _ calls => .closeThenInactiveCalls calls
  | .interruptedFirstAppend stop => .write stop.request
  | .interruptedKeeperSync stop => .write stop.request
  | .interruptedMarkerStageWrite stop => .write stop.request
  | .interruptedStagedMarkerSync stop => .write stop.request
  | .interruptedMarkerRename stop => .write stop.request
  | .interruptedMarkerDirectory stop => .write stop.request
  | .closeAfterUncertainWrite pending _ => .writeThenClose pending.write.request
  | .close _ => .close
  | .rejectedOpensAfterClose sequence => .closeThenOpenAttempts sequence.inputs
  | .interruptedClose _ _ => .close
  | .interruptedCloseAfterUncertainWrite pending _ _ => .writeThenClose pending.write.request
  | .checkpointError _ _ | .checkpointRunDirectoryError _ | .checkpointRunFileError _
  | .checkpointRunDataError _ | .checkpointManifestSyncError _
  | .checkpointManifestOpenError _ | .checkpointManifestDataError _ | .checkpointManifestRenameError _ => .checkpoint
  | .interruptedCheckpoint _ | .interruptedCheckpointRunFile _ | .interruptedCheckpointRunDirectory _
  | .stoppedCheckpoint _ _ _ => .checkpoint
  | .collectionError _ _ _ => .collectCoveredWal
  | .interruptedCoveredWalUnlink _ | .interruptedCoveredWalDirectory _ | .coveredWalUnlinkError _ => .collectCoveredWal
  | .interruptedObsoleteRunUnlink cut _ => .collectObsoleteRuns cut.plan.reports.held
  | .interruptedRotation _ => .rotateWal
  | .rotationError _ _ => .rotateWal

def uncertainBatch : NativeExecutionEnd current → Option (List WAL.Write)
  | .uncertainWrite pending | .closeAfterUncertainWrite pending _ | .callsAfterUncertainWrite pending _
  | .callsAfterPoisonedClose pending _ _ _ => some pending.write.failure.batch
  | .interruptedFirstAppend (prepared := prepared) _ | .interruptedKeeperSync (prepared := prepared) _
  | .interruptedMarkerRename (prepared := prepared) _
  | .interruptedStagedMarkerSync (prepared := prepared) _
  | .interruptedMarkerStageWrite (prepared := prepared) _
  | .interruptedMarkerDirectory (prepared := prepared) _ =>
    some prepared.batch
  | .interruptedCloseAfterUncertainWrite pending _ _ => some pending.write.failure.batch
  | _ => none

def submissions (ending : NativeExecutionEnd current) : List DatabaseSubmissions :=
  current.submissions ++ (ending.uncertainBatch.map DatabaseSubmissions.uncertainBatch).toList

/-- Retain the native schedule's exact endpoint, including the original
write return when close follows it. The interrupted cases record the
issued unlock or directory barrier and its reached state. -/
def Reached : NativeExecutionEnd current → Prop
  | .ready => current.ready.opened =
      .ok current.ready.initial.session (current.ready.initial.census, current.ready.initial.files)
  | .uncertainWrite pending => pending.write.returnedAt pending.cache
  | .callsAfterUncertainWrite pending calls =>
      pending.write.returnedAt pending.cache ∧
      NativeInactiveTrace pending.inactive calls (calls.map (NativeInactiveRequest.response .poisoned))
  | .callsAfterPoisonedClose pending reported unlocked calls =>
      pending.write.returnedAt pending.cache ∧ reported.report.run = .ok () reported.report.finished ∧
      NativeInactiveTrace (reported.inactive unlocked) calls (calls.map (NativeInactiveRequest.response .closed))
  | .callsAfterReadyClose reported unlocked calls =>
      reported.report.run = .ok () reported.report.finished ∧
      NativeInactiveTrace (reported.inactive unlocked) calls (calls.map (NativeInactiveRequest.response .closed))
  | .interruptedFirstAppend stop => NativePendingFirstAppend current.ready stop
  | .interruptedKeeperSync stop => NativePendingKeeperSync current.ready stop
  | .interruptedMarkerStageWrite stop => NativePendingMarkerStageWrite current.ready stop
  | .interruptedStagedMarkerSync stop => NativePendingStagedMarkerSync current.ready stop
  | .interruptedMarkerRename stop => NativePendingMarkerRename current.ready stop
  | .interruptedMarkerDirectory stop => NativePendingMarkerDirectory current.ready stop
  | .closeAfterUncertainWrite pending closed =>
      pending.write.returnedAt pending.cache ∧
      closed.report.run = match closed.report.result with
        | .ok () => .ok () closed.reached
        | .error cause => .error cause closed.reached
  | .close reported => reported.Returned
  | .rejectedOpensAfterClose sequence =>
      sequence.close.report.run = .ok () sequence.close.report.finished ∧
      sequence.close.report.finished.phase = .closed ∧
      sequence.close.report.finished.descriptors = current.ready.state.census.afterDrops
        (sequence.close.report.drops .active ++ sequence.close.report.drops .pending ++ sequence.close.report.drops .directory) ∧
      sequence.after.1.inode = current.ready.state.census.inode ∧
      sequence.after.2.image = current.ready.state.files.image ∧
      (TryLockObserves sequence.after.2.owners current.ready.state.session.directory (.ok true) ↔ sequence.available = true) ∧
      sequence.errors.length = sequence.inputs.length
  | .interruptedClose cut _ =>
      (∀ clear, cut.run clear = .error current.ready.state.owner cut.atCut ∧
        cut.atCut.phase = .ready current.ready.state.writer.installed ∧
        cut.atCut.files.image = (current.ready.state.cache, current.ready.state.files.image) ∧
        cut.atCut.descriptors = cut.issueCensus ∧
        cut.bindings (current.ready.state.session.directory.file .lock) =
          some (current.ready.state.census.inode current.ready.state.owner.description)) ∧
      ∀ drops, TryLockObserves (cut.afterDrops drops).files.owners current.ready.state.session.directory (.ok true) ↔
        cut.effective = true ∨ (cut.afterDrops drops).descriptors.references current.ready.state.session.descriptor = []
  | .interruptedCloseAfterUncertainWrite pending cut _ =>
      pending.write.returnedAt pending.cache ∧
      (∀ clear, cut.run clear = .error current.ready.state.owner cut.atCut ∧
        cut.atCut.phase = .poisoned ∧ cut.atCut.files.image = (pending.cache, pending.write.failure.failed) ∧
        cut.atCut.descriptors = cut.issueCensus ∧
        cut.bindings (current.ready.state.session.directory.file .lock) =
          pending.observed.bindings (current.ready.state.session.directory.file .lock)) ∧
      ∀ drops, TryLockObserves (cut.afterDrops drops).files.owners current.ready.state.session.directory (.ok true) ↔
        cut.effective = true ∨ (cut.afterDrops drops).descriptors.references current.ready.state.session.descriptor = []
  | .checkpointError (cut := cut) reported physical =>
      reported.run = .error reported.error
        (.poisoned, ⟨(current.ready.state.cache, reported.after), current.ready.state.files.owners⟩) ∧
      reported.callbackPrefix.descriptors reported.after = current.ready.state.census ∧
      CheckpointWalView.ofFiles (physical.files reported.after) = CheckpointWalView.ofFiles current.ready.state.files.image ∧
      ∀ pair ∈ (physical.files reported.after).directory.crashImages,
        pair.walBoundary = current.ready.state.writer.wal.directory.active.walBoundary ∧
        cut.PendingReplay (physical.runs reported.after) pair.manifest current.submissions current.ready.reads
  | .checkpointRunDirectoryError reported => NativeReturnedCheckpointRunDirectoryError current.ready reported
  | .checkpointRunFileError reported => NativeReturnedCheckpointRunFileError current.ready reported
  | .checkpointRunDataError reported => NativeReturnedCheckpointRunDataError current.ready reported
  | .checkpointManifestSyncError reported => NativeReturnedCheckpointManifestSyncError current.ready reported
  | .checkpointManifestOpenError reported => NativeReturnedCheckpointManifestOpenError current.ready reported
  | .checkpointManifestDataError reported => NativeReturnedCheckpointManifestDataError current.ready reported
  | .checkpointManifestRenameError reported => NativeReturnedCheckpointManifestRenameError current.ready reported
  | .interruptedCheckpoint stop => NativePendingCheckpoint current.ready stop
  | .interruptedCheckpointRunFile stop => NativePendingCheckpointRunFile current.ready stop
  | .interruptedCheckpointRunDirectory stop => NativePendingCheckpointRunDirectory current.ready stop
  | .stoppedCheckpoint (opened := opened) (position := position) (primitives := primitives) (fsync := fsync)
      (stage := stage) (reason := reason) (reached := reached) _ _ _ =>
    opened.table.UsesOpenCheckpointSchedule position.current.ready.state.session.directory opened.files opened.phase ∧
    (runCheckpointOnOpenPhaseUntilSyncStop position.current.ready.state.session.directory
      opened.phase opened.get opened.set primitives fsync).run
      (position.current.ready.state.cache, position.reached) = .error (stage, reason) reached ∧
      opened.contents reached.2 opened.phase = some .poisoned
  | .collectionError reported cause _ =>
      reported.run = .error (IO.userError s!"sync failed for '{current.ready.state.session.directory.path}': {cause}")
        (.poisoned, ⟨(current.ready.state.cache, reported.pending.image), reported.pending.owners⟩) ∧
      ∀ sealed ∈ reported.pending.image.crashSealed,
        Nonempty (CoveredWalRetrySelection current.ready.state.writer { reported.pending.image.visible with sealed })
  | .coveredWalUnlinkError reported => NativeReturnedCoveredWalUnlinkError current.ready reported
  | .interruptedCoveredWalDirectory stop => NativeCoveredWalDirectoryStopped current.ready stop
  | .interruptedCoveredWalUnlink stop =>
      (∀ barrier, stop.run barrier = .error stop.path
        (.poisoned, ⟨(current.ready.state.cache, stop.census, stop.after), current.ready.state.files.owners⟩)) ∧
      stop.census = current.ready.state.census ∧
      current.ready.state.files.owners.Owns current.ready.state.session.directory current.ready.state.session.descriptor ∧
      current.ready.state.owner ∈ stop.census.slots ∧ current.ready.state.directorySlot ∈ stop.census.slots ∧
      ∀ sealed ∈ stop.after.crashSealed,
        WalSegmentCollectionRetry current.ready.state.writer.wal { stop.after.visible with sealed }
  | .interruptedObsoleteRunUnlink cut stop =>
      (∀ barrier, stop.runFromReady barrier = .error cut.path
        (.ready current.ready.state.writer.installed,
          ⟨(current.ready.state.cache, cut.reachedCensus, cut.reached), current.ready.state.files.owners⟩)) ∧
      current.ready.state.files.owners.Owns current.ready.state.session.directory current.ready.state.session.descriptor ∧
      (∀ candidate ∈ cut.reached.crashImages,
        SelectedIntegrityCheckpoint candidate current.ready.state.writer.target.pair.manifest current.ready.state.writer.checkpoint) ∧
      ∀ generation index bytes,
        current.ready.state.writer.installed.generation ≤ generation ∨ generation ∈ cut.plan.reports.held →
        cut.plan.initial.guaranteed generation index = some bytes →
        cut.reached.guaranteed generation index = some bytes
  | .interruptedRotation stop => NativePendingRotation current.ready stop
  | .rotationError cause failure => NativeReturnedRotationError current.ready cause failure

theorem reached (ending : NativeExecutionEnd current) : ending.Reached := by
  cases ending with
  | ready => exact current.ready.readPrefix.frames.1
  | uncertainWrite pending => exact pending.returned
  | callsAfterUncertainWrite pending calls => exact ⟨pending.returned, (pending.rejectsCalls calls).2.1⟩
  | callsAfterPoisonedClose _ reported unlocked calls =>
    obtain ⟨pending, closed, rejected, _⟩ := reported.rejectsCalls unlocked calls
    exact ⟨pending, closed, rejected⟩
  | callsAfterReadyClose reported unlocked calls =>
    obtain ⟨closed, rejected, _⟩ := current.ready.rejectsCallsAfterClose reported unlocked calls
    exact ⟨closed, rejected⟩
  | interruptedFirstAppend stop => exact current.ready.stopsAtFirstAppend stop
  | interruptedKeeperSync stop => exact current.ready.stopsAtKeeperSync stop
  | interruptedMarkerStageWrite stop => exact current.ready.stopsAtMarkerStageWrite stop
  | interruptedStagedMarkerSync stop => exact current.ready.stopsAtStagedMarkerSync stop
  | interruptedMarkerRename stop => exact current.ready.stopsAtMarkerRename stop
  | interruptedMarkerDirectory stop => exact current.ready.stopsAtMarkerDirectory stop
  | closeAfterUncertainWrite pending close =>
    refine ⟨pending.returned, ?_⟩
    have result := close.returns
    cases status : close.report.result with
    | ok value =>
      cases value
      rw [status] at result
      simpa only [status] using result.1
    | error cause =>
      rw [status] at result
      simpa only [status] using result.1
  | close reported => exact (current.ready.closes reported).returned
  | rejectedOpensAfterClose sequence =>
    obtain ⟨closed, phase, census, _, inodes, files, vacant, count, _⟩ :=
      current.ready.rejectedOpensAfterClose sequence.close sequence.closed sequence.reported
    exact ⟨closed, phase, census, inodes, files, vacant, count⟩
  | interruptedClose cut owner =>
    refine ⟨?_, cut.admitsAfterDrops⟩
    intro clear
    obtain ⟨stopped, phase, files, inventory, _, _, bound, _⟩ := current.ready.stopsDuringClose cut owner clear
    exact ⟨stopped, phase, files, inventory, bound⟩
  | interruptedCloseAfterUncertainWrite pending cut owner =>
    refine ⟨pending.returned, ?_, cut.admitsAfterDrops⟩
    intro clear
    obtain ⟨stopped, phase, files, inventory, _, _, bound, _⟩ := pending.stopsDuringClose cut owner clear
    exact ⟨stopped, phase, files, inventory, bound⟩
  | checkpointError reported physical => exact current.ready.readPrefix.checkpointDirectoryError reported physical
  | checkpointRunDirectoryError reported => exact current.ready.checkpointRunDirectoryError reported
  | checkpointRunFileError reported => exact current.ready.checkpointRunFileError reported
  | checkpointRunDataError reported => exact current.ready.checkpointRunDataError reported
  | checkpointManifestSyncError reported => exact current.ready.checkpointManifestSyncError reported
  | checkpointManifestOpenError reported => exact current.ready.checkpointManifestOpenError reported
  | checkpointManifestDataError reported => exact current.ready.checkpointManifestDataError reported
  | checkpointManifestRenameError reported => exact current.ready.checkpointManifestRenameError reported
  | interruptedCheckpoint stop => exact current.ready.stopsDuringCheckpoint stop
  | interruptedCheckpointRunFile stop => exact current.ready.stopsAtCheckpointRunFile stop
  | interruptedCheckpointRunDirectory stop => exact current.ready.stopsAtCheckpointRunDirectory stop
  | stoppedCheckpoint _ stop poisoned => exact ⟨stop.source, stop.stoppedCall, poisoned⟩
  | collectionError reported _ failed =>
    obtain ⟨returned, _, _, _, _, _, _, _, _, _, _, _, _, survivors, _⟩ :=
      current.ready.readPrefix.collectionBarrierFailed reported failed
    exact ⟨returned, survivors⟩
  | coveredWalUnlinkError reported => exact current.ready.returnsCoveredWalUnlinkError reported
  | interruptedCoveredWalDirectory stop => exact current.ready.stopsAtCoveredWalDirectory stop
  | interruptedCoveredWalUnlink stop =>
    have valid := current.ready.readPrefix.refines.1
    have custody := stop.retainsCustody valid
    exact ⟨stop.stops valid, stop.sameCensus.2, valid.retained.held, custody.1, custody.2.1, (stop.selections valid).2⟩
  | interruptedObsoleteRunUnlink cut stop =>
    obtain ⟨stopped, held, selected, protectedRuns, _⟩ := current.ready.stopsDuringObsoleteRunUnlink cut stop
    exact ⟨stopped, held, selected, protectedRuns⟩
  | interruptedRotation stop => exact current.ready.stopsDuringRotation stop
  | rotationError cause failure => exact current.ready.rotationReturnsError cause failure

def ReadyReplay : NativeExecutionEnd current → Prop
  | .ready => InstalledClientReplay current.submissions current.ready.reads current.history
      current.ready.state.writer.installed current.ready.state.session
  | .close reported => ∀ cause, reported.report.result = .error cause →
      InstalledClientReplay current.submissions current.ready.reads current.history
        current.ready.state.writer.installed reported.session
  | _ => True

theorem guarded (ending : NativeExecutionEnd current) : ending.ReadyReplay := by
  cases ending
  case ready => exact current.ready.readPrefix.guardedReplay
  case close reported => exact (current.ready.closes reported).readyOnError
  all_goals trivial

def allows (ending : NativeExecutionEnd current) (chosen : List WAL.Write) : Prop :=
  chosen = current.history ∨ ∃ group, ending.uncertainBatch = some group ∧ chosen = current.history ++ group

/-- At the end of the execution, a pending write's live marker selects
the old history or the whole submission. Each earlier recorded read
keeps its committed bound in the selected history. -/
theorem selectsAtEnd (ending : NativeExecutionEnd current) :
    ∃ chosen, ending.allows chosen ∧ PendingClientReplay ending.submissions current.ready.reads chosen ∧
      ∀ read ∈ current.ready.reads, read.BoundedBy chosen.length := by
  cases ending with
  | uncertainWrite pending =>
    obtain ⟨chosen, allowed, _, replay, bounded⟩ := pending.selectsAtReturn
    exact ⟨chosen, allowed.imp id (fun whole => ⟨_, rfl, whole⟩), replay, bounded⟩
  | callsAfterUncertainWrite pending =>
    obtain ⟨chosen, allowed, _, replay, bounded⟩ := pending.selectsAtReturn
    exact ⟨chosen, allowed.imp id (fun whole => ⟨_, rfl, whole⟩), replay, bounded⟩
  | callsAfterPoisonedClose _ reported =>
    obtain ⟨chosen, allowed, _, replay, bounded⟩ := reported.selectsAtReturn
    exact ⟨chosen, allowed.imp id (fun whole => ⟨_, rfl, whole⟩), replay, bounded⟩
  | interruptedFirstAppend stop =>
    have reached := current.ready.stopsAtFirstAppend stop
    exact ⟨current.history, .inl rfl, reached.replay, reached.bounded⟩
  | interruptedKeeperSync stop =>
    have reached := current.ready.stopsAtKeeperSync stop
    exact ⟨current.history, .inl rfl, reached.replay, reached.bounded⟩
  | interruptedStagedMarkerSync stop =>
    have reached := current.ready.stopsAtStagedMarkerSync stop
    exact ⟨current.history, .inl rfl, reached.replay, reached.bounded⟩
  | interruptedMarkerStageWrite stop =>
    have reached := current.ready.stopsAtMarkerStageWrite stop
    exact ⟨current.history, .inl rfl, reached.replay, reached.bounded⟩
  | interruptedMarkerRename stop =>
    have reached := current.ready.stopsAtMarkerRename stop
    obtain ⟨retained, allowed, _, _, _, replay, bounded⟩ := reached.selections _ (List.mem_cons_self ..)
    refine ⟨current.history ++ retained, ?_, replay, bounded⟩
    rcases allowed with rfl | rfl
    · exact .inl (List.append_nil _)
    · exact .inr ⟨_, rfl, rfl⟩
  | interruptedMarkerDirectory stop =>
    have reached := current.ready.stopsAtMarkerDirectory stop
    exact ⟨_, .inr ⟨_, rfl, rfl⟩, reached.liveReplay, reached.liveBounds⟩
  | closeAfterUncertainWrite pending close =>
    obtain ⟨chosen, allowed, _, replay, bounded⟩ := close.selectsAtReturn
    exact ⟨chosen, allowed.imp id (fun whole => ⟨_, rfl, whole⟩), replay, bounded⟩
  | interruptedCloseAfterUncertainWrite pending =>
    obtain ⟨chosen, allowed, _, replay, bounded⟩ := pending.selectsAtReturn
    exact ⟨chosen, allowed.imp id (fun whole => ⟨_, rfl, whole⟩), replay, bounded⟩
  | ready | close | callsAfterReadyClose | rejectedOpensAfterClose | interruptedClose | checkpointError | interruptedCheckpoint
  | interruptedCheckpointRunFile | interruptedCheckpointRunDirectory | stoppedCheckpoint
  | checkpointRunDirectoryError | checkpointRunFileError | checkpointRunDataError
  | checkpointManifestSyncError | checkpointManifestOpenError | checkpointManifestDataError | checkpointManifestRenameError
  | collectionError | coveredWalUnlinkError | interruptedCoveredWalUnlink
  | interruptedCoveredWalDirectory | interruptedObsoleteRunUnlink | interruptedRotation | rotationError =>
    refine ⟨current.history, .inl rfl, ?_, current.ready.readPrefix.readsBounded⟩
    all_goals simpa [submissions, uncertainBatch] using current.ready.readPrefix.refines.2.2

end NativeExecutionEnd

/-- The next terminal instruction uses reports at the reached position.
The pending write and its exact cache are derived before the caller's
reported close is interpreted. -/
inductive NativeExecutionEndObservation (current : NativeExecutionPosition) :
    NativeExecutionEndInstruction → Type 1 where
  | ready : NativeExecutionEndObservation current .ready
  | uncertainWrite (write : NativeReadyWriteFailure current.ready.state)
      (inspect : ∀ cache, write.returnedAt cache → Nonempty (NativePendingWriteCensus current.ready.state cache)) :
      NativeExecutionEndObservation current (.write write.request)
  | callsAfterUncertainWrite (failedWrite : NativeReadyWriteFailure current.ready.state)
      (calls : List NativeInactiveRequest)
      (inspect : ∀ cache, failedWrite.returnedAt cache → Nonempty (NativePendingWriteCensus current.ready.state cache)) :
      NativeExecutionEndObservation current (.writeThenInactiveCalls failedWrite.request calls)
  | callsAfterPoisonedClose (failedWrite : NativeReadyWriteFailure current.ready.state)
      (calls : List NativeInactiveRequest)
      (inspect : ∀ cache, failedWrite.returnedAt cache → Nonempty (NativePendingWriteCensus current.ready.state cache))
      (close : ∀ pending : NativePendingWrite current.ready, pending.write = failedWrite →
        ∃ reported : NativePendingClose pending, reported.report.result = .ok ()) :
      NativeExecutionEndObservation current (.writeThenCloseThenInactiveCalls failedWrite.request calls)
  | callsAfterReadyClose (reported : NativeReadyClose current.ready.state) (unlocked : reported.report.result = .ok ())
      (calls : List NativeInactiveRequest) : NativeExecutionEndObservation current (.closeThenInactiveCalls calls)
  | interruptedFirstAppend {prepared : NativeReadyWritePreparation current.ready.state}
      (stop : NativeFirstAppendStop prepared) : NativeExecutionEndObservation current (.write stop.request)
  | interruptedKeeperSync {prepared : NativeReadyWritePreparation current.ready.state}
      (stop : NativeWriteKeeperSyncStop prepared) : NativeExecutionEndObservation current (.write stop.request)
  | interruptedMarkerStageWrite {prepared : NativeReadyWritePreparation current.ready.state}
      (stop : NativeMarkerStageWriteStop prepared) : NativeExecutionEndObservation current (.write stop.request)
  | interruptedStagedMarkerSync {prepared : NativeReadyWritePreparation current.ready.state}
      (stop : NativeWriteStagedMarkerSyncStop prepared) : NativeExecutionEndObservation current (.write stop.request)
  | interruptedMarkerRename {prepared : NativeReadyWritePreparation current.ready.state}
      (stop : NativeWriteMarkerRenameStop prepared) : NativeExecutionEndObservation current (.write stop.request)
  | interruptedMarkerDirectory {prepared : NativeReadyWritePreparation current.ready.state}
      (stop : NativeWriteMarkerDirectoryStop prepared) : NativeExecutionEndObservation current (.write stop.request)
  | closeAfterUncertainWrite (write : NativeReadyWriteFailure current.ready.state)
      (inspect : ∀ cache, write.returnedAt cache → Nonempty (NativePendingWriteCensus current.ready.state cache))
      (close : ∀ pending : NativePendingWrite current.ready, pending.write = write → Nonempty (NativePendingClose pending)) :
      NativeExecutionEndObservation current (.writeThenClose write.request)
  | close (reported : NativeReadyClose current.ready.state) : NativeExecutionEndObservation current .close
  | rejectedOpensAfterClose (sequence : NativeRejectedOpenSequence current) :
      NativeExecutionEndObservation current (.closeThenOpenAttempts sequence.inputs)
  | interruptedClose
      (cut : NativeCloseUnlockInterruption current.ready.state.session.directory
        current.ready.state.session.descriptor current.ready.state.closeState)
      (owner : cut.slot = current.ready.state.owner) : NativeExecutionEndObservation current .close
  | interruptedCloseAfterUncertainWrite (write : NativeReadyWriteFailure current.ready.state)
      (inspect : ∀ cache, write.returnedAt cache → Nonempty (NativePendingWriteCensus current.ready.state cache))
      (stop : ∀ pending : NativePendingWrite current.ready, pending.write = write →
        ∃ cut : NativeCloseUnlockInterruption current.ready.state.session.directory
          current.ready.state.session.descriptor pending.poisoned, cut.slot = current.ready.state.owner) :
      NativeExecutionEndObservation current (.writeThenClose write.request)
  | checkpointError {image : Type} {cut : CheckpointPowerCut current.ready.state.session.directory current.ready.state.writer}
      (reported : NativeCheckpointDirectoryError (image := image) current.ready.state cut) (physical : reported.Physical) :
      NativeExecutionEndObservation current .checkpoint
  | checkpointRunDirectoryError {image : Type}
      {cut : CheckpointPowerCut current.ready.state.session.directory current.ready.state.writer}
      (reported : NativeCheckpointRunDirectoryError (image := image) current.ready.state cut) : NativeExecutionEndObservation current .checkpoint
  | checkpointManifestSyncError {image : Type}
      {cut : CheckpointPowerCut current.ready.state.session.directory current.ready.state.writer}
      (reported : NativeCheckpointManifestSyncError (image := image) current.ready.state cut) : NativeExecutionEndObservation current .checkpoint
  | checkpointManifestOpenError {image : Type}
      {cut : CheckpointPowerCut current.ready.state.session.directory current.ready.state.writer}
      (reported : NativeCheckpointManifestOpenError (image := image) current.ready.state cut) : NativeExecutionEndObservation current .checkpoint
  | checkpointManifestDataError {image : Type}
      {cut : CheckpointPowerCut current.ready.state.session.directory current.ready.state.writer}
      (reported : NativeCheckpointManifestDataError (image := image) current.ready.state cut) : NativeExecutionEndObservation current .checkpoint
  | checkpointManifestRenameError {image : Type}
      {cut : CheckpointPowerCut current.ready.state.session.directory current.ready.state.writer}
      (reported : NativeCheckpointManifestRenameError (image := image) current.ready.state cut) : NativeExecutionEndObservation current .checkpoint
  | checkpointRunDataError {image : Type}
      {cut : CheckpointPowerCut current.ready.state.session.directory current.ready.state.writer}
      (reported : NativeCheckpointRunDataError (image := image) current.ready.state cut) : NativeExecutionEndObservation current .checkpoint
  | checkpointRunFileError {image : Type}
      {cut : CheckpointPowerCut current.ready.state.session.directory current.ready.state.writer}
      (reported : NativeCheckpointRunFileError (image := image) current.ready.state cut) : NativeExecutionEndObservation current .checkpoint
  | interruptedCheckpoint {image : Type} {cut : CheckpointPowerCut current.ready.state.session.directory current.ready.state.writer}
      (stop : NativeCheckpointDirectoryStop (image := image) current.ready.state cut) :
      NativeExecutionEndObservation current .checkpoint
  | interruptedCheckpointRunFile {image : Type}
      {cut : CheckpointPowerCut current.ready.state.session.directory current.ready.state.writer}
      (stop : NativeCheckpointRunFileStop (image := image) current.ready.state cut) :
      NativeExecutionEndObservation current .checkpoint
  | interruptedCheckpointRunDirectory {image : Type}
      {cut : CheckpointPowerCut current.ready.state.session.directory current.ready.state.writer}
      (stop : NativeCheckpointRunDirectoryStop (image := image) current.ready.state cut) :
      NativeExecutionEndObservation current .checkpoint
  | collectionError (reported : NativeReadyWalCollection current.ready.state) (cause : IO.Error)
      (failed : reported.barrier.outcome = .errorBeforeEffect cause ∨ reported.barrier.outcome = .errorAfterEffect cause) :
      NativeExecutionEndObservation current .collectCoveredWal
  | coveredWalUnlinkError (reported : NativeCoveredWalUnlinkError current.ready.state) : NativeExecutionEndObservation current .collectCoveredWal
  | interruptedCoveredWalUnlink (stop : NativeCoveredWalUnlinkStop current.ready.state) :
      NativeExecutionEndObservation current .collectCoveredWal
  | interruptedCoveredWalDirectory (stop : NativeCoveredWalDirectoryStop current.ready.state) :
      NativeExecutionEndObservation current .collectCoveredWal
  | interruptedObsoleteRunUnlink (cut : NativeObsoleteRunUnlinkCut current.ready.state)
      (stop : NativeObsoleteRunUnlinkStop cut) : NativeExecutionEndObservation current (.collectObsoleteRuns cut.plan.reports.held)
  | interruptedRotation (stop : NativeRotationDirectoryStop current.ready.state) :
      NativeExecutionEndObservation current .rotateWal
  | rotationError (cause : IO.Error) (failure : NativeRotationDirectoryFailure current.ready.state (some cause)) :
      NativeExecutionEndObservation current .rotateWal

/-- Attach a pending write whose exact return and census have already
been derived. The returned cache is uniquely determined by the call. -/
def NativePendingWrite.endObservation {current : NativeExecutionPosition}
    (pending : NativePendingWrite current.ready) :
    NativeExecutionEndObservation current (.write pending.write.request) := by
  refine .uncertainWrite pending.write (fun cache returned => ?_)
  have exactResult := pending.returned.symm.trans returned
  have sameCache : pending.cache = cache :=
    congrArg (fun result => result.2.image.1) (EStateM.Result.error.inj exactResult).2
  exact ⟨sameCache ▸ pending.observed⟩

theorem NativeExecutionEndObservation.reaches (observed : NativeExecutionEndObservation current requested) :
    ∃ ending : NativeExecutionEnd current, ending.instruction = requested ∧ ending.Reached := by
  cases observed with
  | ready => exact ⟨.ready, rfl, NativeExecutionEnd.reached _⟩
  | uncertainWrite write inspect =>
    obtain ⟨pending, same, _⟩ := current.ready.stopsAtUncertainWrite write inspect
    refine ⟨.uncertainWrite pending, ?_, pending.returned⟩
    change NativeExecutionEndInstruction.write pending.write.request = .write write.request
    rw [same]
  | callsAfterUncertainWrite failedWrite calls inspect =>
    obtain ⟨pending, same, _⟩ := current.ready.stopsAtUncertainWrite failedWrite inspect
    refine ⟨.callsAfterUncertainWrite pending calls, ?_, NativeExecutionEnd.reached _⟩
    change NativeExecutionEndInstruction.writeThenInactiveCalls pending.write.request calls = _
    rw [same]
  | callsAfterPoisonedClose failedWrite calls inspect close =>
    obtain ⟨pending, same, _⟩ := current.ready.stopsAtUncertainWrite failedWrite inspect
    obtain ⟨reported, unlocked⟩ := close pending same
    refine ⟨.callsAfterPoisonedClose pending reported unlocked calls, ?_, NativeExecutionEnd.reached _⟩
    change NativeExecutionEndInstruction.writeThenCloseThenInactiveCalls pending.write.request calls = _
    rw [same]
  | callsAfterReadyClose reported unlocked calls =>
    exact ⟨.callsAfterReadyClose reported unlocked calls, rfl, NativeExecutionEnd.reached _⟩
  | interruptedFirstAppend stop => exact ⟨.interruptedFirstAppend stop, rfl, NativeExecutionEnd.reached _⟩
  | interruptedKeeperSync stop => exact ⟨.interruptedKeeperSync stop, rfl, NativeExecutionEnd.reached _⟩
  | interruptedMarkerStageWrite stop => exact ⟨.interruptedMarkerStageWrite stop, rfl, NativeExecutionEnd.reached _⟩
  | interruptedStagedMarkerSync stop => exact ⟨.interruptedStagedMarkerSync stop, rfl, NativeExecutionEnd.reached _⟩
  | interruptedMarkerRename stop => exact ⟨.interruptedMarkerRename stop, rfl, NativeExecutionEnd.reached _⟩
  | interruptedMarkerDirectory stop => exact ⟨.interruptedMarkerDirectory stop, rfl, NativeExecutionEnd.reached _⟩
  | closeAfterUncertainWrite write inspect close =>
    obtain ⟨pending, same, _⟩ := current.ready.stopsAtUncertainWrite write inspect
    obtain ⟨closed⟩ := close pending same
    refine ⟨.closeAfterUncertainWrite pending closed, ?_, NativeExecutionEnd.reached _⟩
    change NativeExecutionEndInstruction.writeThenClose pending.write.request = .writeThenClose write.request
    rw [same]
  | close reported => exact ⟨.close reported, rfl, NativeExecutionEnd.reached _⟩
  | rejectedOpensAfterClose sequence => exact ⟨.rejectedOpensAfterClose sequence, rfl, NativeExecutionEnd.reached _⟩
  | interruptedClose cut owner => exact ⟨.interruptedClose cut owner, rfl, NativeExecutionEnd.reached _⟩
  | interruptedCloseAfterUncertainWrite write inspect stop =>
    obtain ⟨pending, same, _⟩ := current.ready.stopsAtUncertainWrite write inspect
    obtain ⟨cut, owner⟩ := stop pending same
    refine ⟨.interruptedCloseAfterUncertainWrite pending cut owner, ?_, NativeExecutionEnd.reached _⟩
    change NativeExecutionEndInstruction.writeThenClose pending.write.request = .writeThenClose write.request
    rw [same]
  | checkpointError reported physical => exact ⟨.checkpointError reported physical, rfl, NativeExecutionEnd.reached _⟩
  | checkpointRunDirectoryError reported => exact ⟨.checkpointRunDirectoryError reported, rfl, NativeExecutionEnd.reached _⟩
  | checkpointRunFileError reported => exact ⟨.checkpointRunFileError reported, rfl, NativeExecutionEnd.reached _⟩
  | checkpointRunDataError reported => exact ⟨.checkpointRunDataError reported, rfl, NativeExecutionEnd.reached _⟩
  | checkpointManifestSyncError reported => exact ⟨.checkpointManifestSyncError reported, rfl, NativeExecutionEnd.reached _⟩
  | checkpointManifestOpenError reported => exact ⟨.checkpointManifestOpenError reported, rfl, NativeExecutionEnd.reached _⟩
  | checkpointManifestDataError reported => exact ⟨.checkpointManifestDataError reported, rfl, NativeExecutionEnd.reached _⟩
  | checkpointManifestRenameError reported => exact ⟨.checkpointManifestRenameError reported, rfl, NativeExecutionEnd.reached _⟩
  | interruptedCheckpoint stop => exact ⟨.interruptedCheckpoint stop, rfl, NativeExecutionEnd.reached _⟩
  | interruptedCheckpointRunFile stop => exact ⟨.interruptedCheckpointRunFile stop, rfl, NativeExecutionEnd.reached _⟩
  | interruptedCheckpointRunDirectory stop => exact ⟨.interruptedCheckpointRunDirectory stop, rfl, NativeExecutionEnd.reached _⟩
  | collectionError reported cause failed => exact ⟨.collectionError reported cause failed, rfl, NativeExecutionEnd.reached _⟩
  | coveredWalUnlinkError reported => exact ⟨.coveredWalUnlinkError reported, rfl, NativeExecutionEnd.reached _⟩
  | interruptedCoveredWalUnlink stop => exact ⟨.interruptedCoveredWalUnlink stop, rfl, NativeExecutionEnd.reached _⟩
  | interruptedCoveredWalDirectory stop => exact ⟨.interruptedCoveredWalDirectory stop, rfl, NativeExecutionEnd.reached _⟩
  | interruptedObsoleteRunUnlink cut stop => exact ⟨.interruptedObsoleteRunUnlink cut stop, rfl, NativeExecutionEnd.reached _⟩
  | interruptedRotation stop => exact ⟨.interruptedRotation stop, rfl, NativeExecutionEnd.reached _⟩
  | rotationError cause failure => exact ⟨.rotationError cause failure, rfl, NativeExecutionEnd.reached _⟩

/-- The ending belongs to the last state of the executed instruction
prefix, so it can use that state even when its last call cannot return. -/
structure NativeReachedExecutionPrefix (start : NativeExecutionPosition)
    (instructions : List NativeExecutionInstruction) (requested : NativeExecutionEndInstruction) where
  events : List NativeExecutionEvent
  last : NativeExecutionPosition
  ending : NativeExecutionEnd last
  ordered : NativeExecutionInstructions instructions events
  trace : NativeExecutionTrace start events last
  requestedEnd : ending.instruction = requested
  reached : ending.Reached

/-- One replay explains the reads at the last ready position. An ending
that returns ready preserves that refinement, and an interrupted ending
has a permitted selection that still explains the earlier responses. -/
theorem NativeReachedExecutionPrefix.keyValueRefinement
    (run : NativeReachedExecutionPrefix start instructions requested) :
    (∀ event ∈ run.events, event.uncertainBatchWhole) ∧
    InstalledClientReplay run.last.submissions run.last.ready.reads run.last.history
      run.last.ready.state.writer.installed run.last.ready.state.session ∧
    run.ending.ReadyReplay ∧
    ∃ chosen, run.ending.allows chosen ∧ PendingClientReplay run.ending.submissions run.last.ready.reads chosen ∧
      ∀ read ∈ run.last.ready.reads, read.BoundedBy chosen.length :=
  ⟨run.trace.uncertainBatchesWhole, run.trace.keyValueRefinement.2.2.2,
    run.ending.guarded, run.ending.selectsAtEnd⟩

theorem NativeExecutionTrace.reachesPrefix (start : NativeExecutionPosition)
    (instructions : List NativeExecutionInstruction) (requested : NativeExecutionEndInstruction)
    (reports : NativeExecutionTrace.Reports start instructions)
    (terminal : ∀ events last, NativeExecutionInstructions instructions events → NativeExecutionTrace start events last →
      Nonempty (NativeExecutionEndObservation last requested)) :
    Nonempty (NativeReachedExecutionPrefix start instructions requested) := by
  obtain ⟨events, last, ordered, trace, _⟩ := NativeExecutionTrace.executes start instructions reports
  obtain ⟨observed⟩ := terminal events last ordered trace
  obtain ⟨ending, request, reached⟩ := observed.reaches
  exact ⟨⟨events, last, ending, ordered, trace, request, reached⟩⟩

/-- The exact returned bootstrap or marked recovery can seed the same
execution. The marked route starts with the ledger justified by its
checkpoint and WAL. Future reports and the ending use the reached state
of that execution. -/
theorem NativeOpenSuccessReports.reachesExecutionPrefix
    {input : FilePath} {directory : DiskDirectory} {history : List WAL.Write}
    {log : List DatabaseSubmissions} {recorded : List RecordedSnapshotRead}
    (opened : NativeOpenSuccessReports input directory history log recorded) :
    opened.markerRead = .ok opened.marker ∧ opened.Selects ∧
    ∃ (start : NativeExecutionPosition) (files : opened.Image),
      opened.run = .ok start.ready.state.session files ∧ start.ready.state.session.directory = directory ∧
      opened.UsesReachedState start.ready.state files ∧
      start.history = history ∧ start.submissions = log ∧ start.ready.reads = recorded ∧
      ∀ instructions requested, NativeExecutionTrace.Reports start instructions →
        (∀ events last, NativeExecutionInstructions instructions events → NativeExecutionTrace start events last →
          Nonempty (NativeExecutionEndObservation last requested)) →
        Nonempty (NativeReachedExecutionPrefix start instructions requested) := by
  obtain ⟨marker, selected, state, files, returned, path, reached, _, _, ready⟩ := opened.returnsReady
  let start : NativeExecutionPosition :=
    ⟨history, log, ⟨.ok state.session (state.census, state.files), state, state, recorded, ready⟩⟩
  exact ⟨marker, selected, start, files, returned, path, reached, rfl, rfl, rfl,
    NativeExecutionTrace.reachesPrefix start⟩

/-- The ready position of the common execution uses the same installed
state, lock and reference identities as the reported native installation
suffix. The heap and primitive allocation effects at that suffix remain
part of the report. -/
theorem NativeOpenSuccessReports.reachesExecutionPrefixWithReferences
    {heap : Type} {input : FilePath} {directory : DiskDirectory} {history : List WAL.Write}
    {log : List DatabaseSubmissions} {recorded : List RecordedSnapshotRead}
    (opened : NativeOpenSuccessReports input directory history log recorded)
    {lock : IO.FS.Handle} {syncFiles : DiskTable.OpenSyncFiles}
    {assemble : IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable}
    (constructor : DiskTable.OpenReferenceAssembly directory lock syncFiles assemble)
    (lockIdentity : IO.FS.Handle → Nat) (phaseIdentity : IO.Ref (Phase Installed) → Nat)
    (tokenIdentity : IO.Ref Unit → Nat)
    (allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed)))
    (allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit))
    (phaseContents : heap → IO.Ref (Phase Installed) → Option (Phase Installed))
    (heapAtInstall : heap)
    (observe : ∀ (session : SegmentedSession) (files : opened.Image) (installed : Installed),
      opened.run = .ok session files → session.phase = .ready installed →
      ∃ allocation : OpenReferenceAllocations allocatePhase allocateToken phaseContents installed heapAtInstall,
        lockIdentity lock = session.descriptor ∧ phaseIdentity allocation.phase = session.phaseRef ∧
        tokenIdentity allocation.token = session.sessionRef) :
    opened.markerRead = .ok opened.marker ∧ opened.Selects ∧
    ∃ (start : NativeExecutionPosition) (files : opened.Image)
      (allocation : OpenReferenceAllocations allocatePhase allocateToken phaseContents
        start.ready.state.writer.installed heapAtInstall) (db : DiskTable),
      opened.run = .ok start.ready.state.session files ∧ start.ready.state.session.directory = directory ∧
      opened.UsesReachedState start.ready.state files ∧
      installReady start.ready.state.writer.installed allocatePhase allocateToken (fun phase token => pure (assemble phase token))
        heapAtInstall = .ok db allocation.afterToken ∧
      db.UsesOpenReferences directory lock syncFiles allocation.phase allocation.token ∧
      phaseContents allocation.afterToken allocation.phase = some start.ready.state.session.phase ∧
      lockIdentity lock = start.ready.state.session.descriptor ∧ phaseIdentity allocation.phase = start.ready.state.session.phaseRef ∧
      tokenIdentity allocation.token = start.ready.state.session.sessionRef ∧
      start.history = history ∧ start.submissions = log ∧ start.ready.reads = recorded ∧
      ∀ instructions requested, NativeExecutionTrace.Reports start instructions →
        (∀ events last, NativeExecutionInstructions instructions events → NativeExecutionTrace start events last →
          Nonempty (NativeExecutionEndObservation last requested)) →
        Nonempty (NativeReachedExecutionPrefix start instructions requested) := by
  obtain ⟨marker, selected, state, files, allocation, db, returned, path, reached, ready, installed,
    references, contents, sameLock, samePhase, sameToken⟩ :=
    opened.returnsReadyWithReferences constructor lockIdentity phaseIdentity tokenIdentity allocatePhase allocateToken
      phaseContents heapAtInstall observe
  let start : NativeExecutionPosition :=
    ⟨history, log, ⟨.ok state.session (state.census, state.files), state, state, recorded, ready⟩⟩
  exact ⟨marker, selected, start, files, allocation, db, returned, path, reached, installed, references, contents,
    sameLock, samePhase, sameToken, rfl, rfl, rfl, NativeExecutionTrace.reachesPrefix start⟩

/-- The exact empty bootstrap starts one native execution. Completed
instructions retain their ordered replay. The final report retains
the reached native state and permitted history, including when it
stops at an issued unlock or directory barrier. -/
theorem BootstrapKeeperMarkerHandoff.executesPrefixFromEmpty
    {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
    {calls : BootstrapOpenCalls (Cache (DescriptorInventory × DescriptorSlot × Nat)) directory before}
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
      ∀ instructions requested, NativeExecutionTrace.Reports start instructions →
        (∀ events last, NativeExecutionInstructions instructions events → NativeExecutionTrace start events last →
          Nonempty (NativeExecutionEndObservation last requested)) →
        ∃ events last, ∃ ending : NativeExecutionEnd last,
          NativeExecutionInstructions instructions events ∧ NativeExecutionTrace start events last ∧
          last.history = events.flatMap NativeExecutionEvent.writes ∧
          last.submissions = events.flatMap NativeExecutionEvent.submissions ∧
          last.ready.reads = events.flatMap NativeExecutionEvent.reads ∧
          (∀ event ∈ events, event.uncertainBatchWhole) ∧
          ending.instruction = requested ∧ ending.Reached ∧ ending.ReadyReplay ∧
          ∃ chosen, ending.allows chosen ∧ PendingClientReplay ending.submissions last.ready.reads chosen ∧
            ∀ read ∈ last.ready.reads, read.BoundedBy chosen.length := by
  obtain ⟨boot, returned, _, _, _, _, _, _, _, _, ready⟩ :=
    bootstrap.startsNativeReadPrefixFromEmpty admission empty effects
  let state : NativeReadyState :=
    ⟨boot.session, boot.writer, effects.reached, captured.cache, calls.slot, captured.cached⟩
  let start : NativeExecutionPosition :=
    ⟨[], [], ⟨.ok state.session (state.census, state.files), state, state, [], ready⟩⟩
  refine ⟨boot, start, returned, rfl, rfl, rfl, ?_⟩
  intro instructions requested reports terminal
  obtain ⟨run⟩ := NativeExecutionTrace.reachesPrefix start instructions requested reports terminal
  obtain ⟨writes, submissions, reads⟩ := run.trace.ledgers
  obtain ⟨whole, _, guarded, selection⟩ := run.keyValueRefinement
  exact ⟨run.events, run.last, run.ending, run.ordered, run.trace,
    by simpa [start] using writes, by simpa [start] using submissions, by simpa [start] using reads,
    whole, run.requestedEnd, run.reached, guarded, selection⟩

end Alvoki.Storage.DiskSession
