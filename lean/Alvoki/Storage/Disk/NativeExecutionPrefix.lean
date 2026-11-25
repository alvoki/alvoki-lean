import Alvoki.Storage.Disk.NativeExecutionTrace
import Alvoki.Storage.Disk.NativeExecutionPendingClose
import Alvoki.Storage.Disk.NativeExecutionOrdinaryClose
import Alvoki.Storage.Disk.NativeCloseUnlockInterruption
import Alvoki.Storage.Disk.NativePendingRotation
import Alvoki.Storage.Disk.NativeRejectedOpenLineage
import Alvoki.Storage.Disk.NativeCheckpointDirectoryError

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

inductive NativeExecutionEndInstruction where
  | ready
  | write (request : WriteRequest)
  | writeThenClose (request : WriteRequest)
  | close
  | closeThenOpenAttempts (inputs : List FilePath)
  | checkpoint
  | collectCoveredWal
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
  | collectionError (reported : NativeReadyWalCollection current.ready.state) (cause : IO.Error)
      (failed : reported.barrier.outcome = .errorBeforeEffect cause ∨ reported.barrier.outcome = .errorAfterEffect cause)
  | interruptedRotation (stop : NativeRotationDirectoryStop current.ready.state)

namespace NativeExecutionEnd

def instruction : NativeExecutionEnd current → NativeExecutionEndInstruction
  | .ready => .ready
  | .uncertainWrite pending => .write pending.write.request
  | .closeAfterUncertainWrite pending _ => .writeThenClose pending.write.request
  | .close _ => .close
  | .rejectedOpensAfterClose sequence => .closeThenOpenAttempts sequence.inputs
  | .interruptedClose _ _ => .close
  | .interruptedCloseAfterUncertainWrite pending _ _ => .writeThenClose pending.write.request
  | .checkpointError _ _ => .checkpoint
  | .collectionError _ _ _ => .collectCoveredWal
  | .interruptedRotation _ => .rotateWal

def uncertainBatch : NativeExecutionEnd current → Option (List WAL.Write)
  | .uncertainWrite pending | .closeAfterUncertainWrite pending _ => some pending.write.failure.batch
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
  | .collectionError reported cause _ =>
      reported.run = .error (IO.userError s!"sync failed for '{current.ready.state.session.directory.path}': {cause}")
        (.poisoned, ⟨(current.ready.state.cache, reported.pending.image), reported.pending.owners⟩) ∧
      ∀ sealed ∈ reported.pending.image.crashSealed,
        Nonempty (CoveredWalRetrySelection current.ready.state.writer { reported.pending.image.visible with sealed })
  | .interruptedRotation stop => NativePendingRotation current.ready stop

theorem reached (ending : NativeExecutionEnd current) : ending.Reached := by
  cases ending with
  | ready => exact current.ready.readPrefix.frames.1
  | uncertainWrite pending => exact pending.returned
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
  | collectionError reported _ failed =>
    obtain ⟨returned, _, _, _, _, _, _, _, _, _, _, _, _, survivors, _⟩ :=
      current.ready.readPrefix.collectionBarrierFailed reported failed
    exact ⟨returned, survivors⟩
  | interruptedRotation stop => exact current.ready.stopsDuringRotation stop

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
  | closeAfterUncertainWrite pending close =>
    obtain ⟨chosen, allowed, _, replay, bounded⟩ := close.selectsAtReturn
    exact ⟨chosen, allowed.imp id (fun whole => ⟨_, rfl, whole⟩), replay, bounded⟩
  | interruptedCloseAfterUncertainWrite pending =>
    obtain ⟨chosen, allowed, _, replay, bounded⟩ := pending.selectsAtReturn
    exact ⟨chosen, allowed.imp id (fun whole => ⟨_, rfl, whole⟩), replay, bounded⟩
  | ready | close | rejectedOpensAfterClose | interruptedClose | checkpointError | collectionError | interruptedRotation =>
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
  | collectionError (reported : NativeReadyWalCollection current.ready.state) (cause : IO.Error)
      (failed : reported.barrier.outcome = .errorBeforeEffect cause ∨ reported.barrier.outcome = .errorAfterEffect cause) :
      NativeExecutionEndObservation current .collectCoveredWal
  | interruptedRotation (stop : NativeRotationDirectoryStop current.ready.state) :
      NativeExecutionEndObservation current .rotateWal

theorem NativeExecutionEndObservation.reaches (observed : NativeExecutionEndObservation current requested) :
    ∃ ending : NativeExecutionEnd current, ending.instruction = requested ∧ ending.Reached := by
  cases observed with
  | ready => exact ⟨.ready, rfl, NativeExecutionEnd.reached _⟩
  | uncertainWrite write inspect =>
    obtain ⟨pending, same, _⟩ := current.ready.stopsAtUncertainWrite write inspect
    refine ⟨.uncertainWrite pending, ?_, pending.returned⟩
    change NativeExecutionEndInstruction.write pending.write.request = .write write.request
    rw [same]
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
  | collectionError reported cause failed => exact ⟨.collectionError reported cause failed, rfl, NativeExecutionEnd.reached _⟩
  | interruptedRotation stop => exact ⟨.interruptedRotation stop, rfl, NativeExecutionEnd.reached _⟩

/-- The exact empty bootstrap starts one native execution. Completed
instructions retain their ordered replay. The final report retains
the reached native state and permitted history, including when it
stops at an issued unlock or WAL rotation barrier. -/
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
  obtain ⟨boot, start, opened, session, writer, census, executes⟩ := bootstrap.executesFromEmpty admission empty effects
  refine ⟨boot, start, opened, session, writer, census, ?_⟩
  intro instructions requested reports terminal
  obtain ⟨events, last, matched, trace, writes, submissions, reads, whole, _⟩ := executes instructions reports
  obtain ⟨observed⟩ := terminal events last matched trace
  obtain ⟨ending, request, reached⟩ := observed.reaches
  exact ⟨events, last, ending, matched, trace, writes, submissions, reads, whole, request, reached,
    ending.guarded, ending.selectsAtEnd⟩

end Alvoki.Storage.DiskSession
