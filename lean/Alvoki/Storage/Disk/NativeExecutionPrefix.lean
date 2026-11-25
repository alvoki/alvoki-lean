import Alvoki.Storage.Disk.NativeExecutionTrace
import Alvoki.Storage.Disk.NativeExecutionPendingClose
import Alvoki.Storage.Disk.NativeExecutionOrdinaryClose
import Alvoki.Storage.Disk.NativeCheckpointDirectoryError

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

inductive NativeExecutionEndInstruction where
  | ready
  | write (request : WriteRequest)
  | writeThenClose (request : WriteRequest)
  | close
  | checkpoint
  | collectCoveredWal

/-- An execution can stop at a ready session or at the exact reached
return of an operation that requires recovery. No reopen is needed to
observe the returned error, files, or ownership. -/
inductive NativeExecutionEnd (current : NativeExecutionPosition) : Type 1 where
  | ready
  | uncertainWrite (pending : NativePendingWrite current.ready)
  | closeAfterUncertainWrite (pending : NativePendingWrite current.ready) (close : NativePendingClose pending)
  | close (reported : NativeReadyClose current.ready.state)
  | checkpointError {image : Type} {cut : CheckpointPowerCut current.ready.state.session.directory current.ready.state.writer}
      (reported : NativeCheckpointDirectoryError (image := image) current.ready.state cut) (physical : reported.Physical)
  | collectionError (reported : NativeReadyWalCollection current.ready.state) (cause : IO.Error)
      (failed : reported.barrier.outcome = .errorBeforeEffect cause ∨ reported.barrier.outcome = .errorAfterEffect cause)

namespace NativeExecutionEnd

def instruction : NativeExecutionEnd current → NativeExecutionEndInstruction
  | .ready => .ready
  | .uncertainWrite pending => .write pending.write.request
  | .closeAfterUncertainWrite pending _ => .writeThenClose pending.write.request
  | .close _ => .close
  | .checkpointError _ _ => .checkpoint
  | .collectionError _ _ _ => .collectCoveredWal

def uncertainBatch : NativeExecutionEnd current → Option (List WAL.Write)
  | .uncertainWrite pending | .closeAfterUncertainWrite pending _ => some pending.write.failure.batch
  | _ => none

def submissions (ending : NativeExecutionEnd current) : List DatabaseSubmissions :=
  current.submissions ++ (ending.uncertainBatch.map DatabaseSubmissions.uncertainBatch).toList

/-- Keep the exact endpoint of the interpreted native call, including
the original write return when a close follows it. -/
def Returned : NativeExecutionEnd current → Prop
  | .ready => current.ready.opened =
      .ok current.ready.initial.session (current.ready.initial.census, current.ready.initial.files)
  | .uncertainWrite pending => pending.write.returnedAt pending.cache
  | .closeAfterUncertainWrite pending closed =>
      pending.write.returnedAt pending.cache ∧
      closed.report.run = match closed.report.result with
        | .ok () => .ok () closed.reached
        | .error cause => .error cause closed.reached
  | .close reported => reported.Returned
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

theorem returned (ending : NativeExecutionEnd current) : ending.Returned := by
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
  | checkpointError reported physical => exact current.ready.readPrefix.checkpointDirectoryError reported physical
  | collectionError reported _ failed =>
    obtain ⟨returned, _, _, _, _, _, _, _, _, _, _, _, _, survivors, _⟩ :=
      current.ready.readPrefix.collectionBarrierFailed reported failed
    exact ⟨returned, survivors⟩

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

/-- The start of recovery still has the same finite ledger. At a write
error or a subsequent close, its live marker selects the old history or
the whole pending submission. Every earlier recorded read keeps its
committed bound in the selected history. -/
theorem selectsAtReturn (ending : NativeExecutionEnd current) :
    ∃ chosen, ending.allows chosen ∧ PendingClientReplay ending.submissions current.ready.reads chosen ∧
      ∀ read ∈ current.ready.reads, read.BoundedBy chosen.length := by
  cases ending with
  | uncertainWrite pending =>
    obtain ⟨chosen, allowed, _, replay, bounded⟩ := pending.selectsAtReturn
    exact ⟨chosen, allowed.imp id (fun whole => ⟨_, rfl, whole⟩), replay, bounded⟩
  | closeAfterUncertainWrite pending close =>
    obtain ⟨chosen, allowed, _, replay, bounded⟩ := close.selectsAtReturn
    exact ⟨chosen, allowed.imp id (fun whole => ⟨_, rfl, whole⟩), replay, bounded⟩
  | ready | close | checkpointError | collectionError =>
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
  | checkpointError {image : Type} {cut : CheckpointPowerCut current.ready.state.session.directory current.ready.state.writer}
      (reported : NativeCheckpointDirectoryError (image := image) current.ready.state cut) (physical : reported.Physical) :
      NativeExecutionEndObservation current .checkpoint
  | collectionError (reported : NativeReadyWalCollection current.ready.state) (cause : IO.Error)
      (failed : reported.barrier.outcome = .errorBeforeEffect cause ∨ reported.barrier.outcome = .errorAfterEffect cause) :
      NativeExecutionEndObservation current .collectCoveredWal

theorem NativeExecutionEndObservation.reaches (observed : NativeExecutionEndObservation current requested) :
    ∃ ending : NativeExecutionEnd current, ending.instruction = requested ∧ ending.Returned := by
  cases observed with
  | ready => exact ⟨.ready, rfl, NativeExecutionEnd.returned _⟩
  | uncertainWrite write inspect =>
    obtain ⟨pending, same, _⟩ := current.ready.stopsAtUncertainWrite write inspect
    refine ⟨.uncertainWrite pending, ?_, pending.returned⟩
    change NativeExecutionEndInstruction.write pending.write.request = .write write.request
    rw [same]
  | closeAfterUncertainWrite write inspect close =>
    obtain ⟨pending, same, _⟩ := current.ready.stopsAtUncertainWrite write inspect
    obtain ⟨closed⟩ := close pending same
    refine ⟨.closeAfterUncertainWrite pending closed, ?_, NativeExecutionEnd.returned _⟩
    change NativeExecutionEndInstruction.writeThenClose pending.write.request = .writeThenClose write.request
    rw [same]
  | close reported => exact ⟨.close reported, rfl, NativeExecutionEnd.returned _⟩
  | checkpointError reported physical => exact ⟨.checkpointError reported physical, rfl, NativeExecutionEnd.returned _⟩
  | collectionError reported cause failed => exact ⟨.collectionError reported cause failed, rfl, NativeExecutionEnd.returned _⟩

/-- Use one native execution from the exact empty bootstrap return.
The completed instructions retain their one ordered replay. The next
reported instruction can end that execution in a poisoned or closed
state while keeping its original response and permitted history. -/
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
          ending.instruction = requested ∧ ending.Returned ∧ ending.ReadyReplay ∧
          ∃ chosen, ending.allows chosen ∧ PendingClientReplay ending.submissions last.ready.reads chosen ∧
            ∀ read ∈ last.ready.reads, read.BoundedBy chosen.length := by
  obtain ⟨boot, start, opened, session, writer, census, executes⟩ := bootstrap.executesFromEmpty admission empty effects
  refine ⟨boot, start, opened, session, writer, census, ?_⟩
  intro instructions requested reports terminal
  obtain ⟨events, last, matched, trace, writes, submissions, reads, whole, _⟩ := executes instructions reports
  obtain ⟨observed⟩ := terminal events last matched trace
  obtain ⟨ending, request, returned⟩ := observed.reaches
  exact ⟨events, last, ending, matched, trace, writes, submissions, reads, whole, request, returned,
    ending.guarded, ending.selectsAtReturn⟩

end Alvoki.Storage.DiskSession
