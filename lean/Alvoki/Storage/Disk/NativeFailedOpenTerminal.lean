import Alvoki.Storage.Disk.NativeFailedOpenTerminalLedger
import Alvoki.Storage.Disk.NativeGroupedWriteRecovery
import Alvoki.Storage.Disk.NativeReadyCallRefinement

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentCommit WalSegmentRepair
open WAL.Boundary (WalInodeImage)

private theorem storageObservation_cast {first last : DiskDirectory} {inodes : WalInodeImage} {runs : RunUnlinkImage}
    (same : first = last) (files : RunDirectoryInodeView first inodes runs) :
    (same ▸ files : RunDirectoryInodeView last inodes runs).storageObservation = files.storageObservation := by
  subst last
  rfl

/-- The final uncertain write determines the ready prefix on the same
handle. If its file group returned the error, the sampled reboot and
actual failed opens may end execution without a successful reopen.
The incoming client ledger and the derived ready suffix adjoin at start. -/
theorem NativeOpenedPosition.stopsAfterGroupedWriteRetries
    {heap stream : Type} {opened : NativeOpenedHandle heap}
    (start : NativeOpenedPosition opened) (view : OpenCloseHeapView heap FileImage)
    (writes : NativeReadyWriteCalls opened) (issuer : opened.LatestIssuer)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView opened.directory (inodes atHeap) (runs atHeap))
    {origin : NativeExecutionPosition} {earlier : List NativeExecutionEvent}
    (prior : origin.LedgerSuffix earlier start.current)
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
    (effects : writes.ReturnEffects view inodes runs (fun atHeap => (observe atHeap).storageObservation) inode buffered)
    (initial : writes.StorageAt view (fun atHeap => (observe atHeap).storageObservation)
      (fun atHeap => (inodes atHeap).visible) start)
    (request : WriteRequest)
    {failed rebooted reached : heap} {cause : IO.Error} {calls : List (NativeReturnedCall opened)}
    (executed : NativeReturnedCalls writes issuer start.reached (start.pins.map NativeOpenedPin.raw)
      (calls ++ [.write request (.error (.commitUnknown cause))]) failed)
    {firstOffset : Nat}
    (readyNames : writes.WalWindowEffects (fun atHeap => (observe atHeap).storageObservation) firstOffset
      (start.current.history.length + (calls.map NativeReturnedCall.requestedRows).sum + request.rows.length))
    (initialWindow : start.WalWindowAt (fun atHeap => (observe atHeap).storageObservation) firstOffset
      (start.current.history.length + (calls.map NativeReturnedCall.requestedRows).sum + request.rows.length))
    (source : RawMarkedOpenInterpreter heap stream) {returns : List (FilePath × IO.Error)}
    (attempts : source.FailedCalls rebooted returns reached) (retried : returns ≠ []) :
    ∃ (current : NativeOpenedPosition opened) (events : List NativeExecutionEvent),
      NativeReturnedCalls writes issuer start.reached (start.pins.map NativeOpenedPin.raw) calls current.reached ∧
      events.length = calls.length ∧ (∀ pair ∈ calls.zip events, pair.1.Records pair.2) ∧
      origin.LedgerSuffix (earlier ++ events) current.current ∧
      (NativeReturnedCall.write request (.error (.commitUnknown cause))).Reaches
        writes issuer (current.pins.map NativeOpenedPin.raw) current.reached failed ∧
      let state := current.current.ready.state
      let dir := state.session.directory
      let installed := state.writer.installed
      let files := fun atHeap => current.directory.symm ▸ observe atHeap
      let storage := fun atHeap => (files atHeap).storageObservation
      let names := fun atHeap => (storage atHeap).files.names
      let visible := fun atHeap => (inodes atHeap).visible
      let cache := writes.cacheAtPosition current
      current.GroupedErrorEffects view cache writes.appender writes.stager writes.syncer
          inodes files inode buffered request writes.lookup failed cause →
      ∀ (reboot : RawWriteRebootEntry state view storage names visible failed rebooted),
        reboot.DurableReset →
        current.WalNameEffects writes.appender writes.stager writes.syncer cache request writes.lookup writes.rename
          storage firstOffset (current.current.history.length + request.rows.length) →
        RawOpenRetryTrace.SelectedEffects view source rebooted state.writer.target
          (fun atHeap => ⟨names atHeap, fun inode => [visible atHeap inode]⟩) state.selectedRetryPath
          (RawOpenRetryTrace.RecoveryObservations view state state.writer.target storage visible firstOffset
            (current.current.history.length + request.rows.length)) attempts →
        (∀ event ∈ earlier ++ events, event.uncertainBatchWhole) ∧
        ∃ batch table guarded poisoned,
          prepareBatch installed.table request.rows = some (batch, table) ∧
          checkActiveSegmentWith dir installed writes.lookup current.reached = .ok () guarded ∧
          opened.set opened.phase .poisoned guarded = .ok () poisoned ∧
          let keeper := dir.file (.walSegment installed.activeFirst)
          let staging := dir.file .stagedWalBoundary
          let groupFailed := ∃ appended staged,
            writes.appender.run cache.active keeper (WAL.encodeBatch batch) poisoned = .ok () appended ∧
            writes.stager.run cache.pending staging
              (WAL.Boundary.encode ((installed.walBytes + WAL.frameSize * request.rows.length).toUInt64)) appended =
                .ok () staged ∧
            writes.syncer.group dir.path cache.directory cache.active cache.pending #[keeper, staging] staged =
              .error cause failed
          ¬ groupFailed ∨ (groupFailed ∧ ∃ previous input diagnostic issued,
            returns = previous ++ [(input, diagnostic)] ∧ source.FailedCalls rebooted previous issued ∧
            source.openTable input issued = .error diagnostic reached ∧
            RawOpenRetryTrace.SelectedEntry view state state.writer.target names visible reached ∧
            state.SelectedRetryDurability state.writer.target (storage reached) ∧
            let history := origin.history ++ (earlier ++ events).flatMap NativeExecutionEvent.writes
            let submissions := (origin.submissions ++ (earlier ++ events).flatMap NativeExecutionEvent.submissions) ++
              [.uncertainBatch batch]
            let reads := origin.ready.reads ++ (earlier ++ events).flatMap NativeExecutionEvent.reads
            PendingClientReplay submissions reads history ∧ ∀ read ∈ reads, read.BoundedBy history.length) := by
  obtain ⟨current, events, ran, _, physical, length, records, suffix, window, observed⟩ :=
    executed.refinesReadyBeforeWrite (fun _ declared => by cases declared) view inodes runs
      (fun atHeap => (observe atHeap).storageObservation) inode buffered effects start rfl rfl initial readyNames initialWindow
  have through := prior.append suffix
  refine ⟨current, events, ran, length, records, through, observed, ?_⟩
  intro state dir installed files storage names visible cache groupEffects reboot reset nameEffects retryEffects
  have sameStorage : storage = fun atHeap => (observe atHeap).storageObservation := by
    funext atHeap
    exact storageObservation_cast current.directory.symm (observe atHeap)
  have ready : NativeReadyStorage state (storage current.reached) := by
    rw [sameStorage]
    exact physical.physical
  have readyWindow : current.WalWindowAt storage firstOffset (current.current.history.length + request.rows.length) :=
    sameStorage.symm ▸ window
  have nonempty := writes.commitUnknownHasRows current observed
  have returned := writes.returnedWriteAt current observed
  obtain ⟨_, batch, table, guarded, poisoned, prepared, fits, guard, assigned, classified⟩ :=
    current.selectsAfterGroupedError view cache writes.appender writes.stager writes.syncer inodes files inode buffered
      request writes.lookup writes.rename nonempty returned ready groupEffects reboot
  refine ⟨through.whole, batch, table, guarded, poisoned, prepared, guard, assigned, ?_⟩
  rcases classified with ⟨grouped, admitted, selected, _, _⟩ | other
  · refine .inr ⟨grouped, ?_⟩
    have framed := current.preservesWalNamesAfterCommitUnknown writes.appender writes.stager writes.syncer cache
      request writes.lookup writes.rename nonempty returned nameEffects
    have window := reboot.walNamespace framed readyWindow.2
    have upper : (current.current.history ++ batch).length = current.current.history.length + request.rows.length := by
      simp only [List.length_append, (prepareBatch_spec prepared).1]
    obtain ⟨_, previous, input, diagnostic, issued, reported, earlierCalls, call, plan, _, last, durable, _, _, replay, bounded⟩ :=
      NativeExecutionPosition.refinesFailedOpenTerminalLedger (current := current.current)
        through prepared fits admitted storage visible readyWindow.1 selected
        (reboot.startsRecoveryObservations reset selected (by simpa only [upper] using window))
        attempts retried (by simpa only [upper] using retryEffects)
    have old : plan.history = origin.history ++ (earlier ++ events).flatMap NativeExecutionEvent.writes :=
      plan.oldHistory.trans through.history
    exact ⟨previous, input, diagnostic, issued, reported, earlierCalls, call, last, durable, old ▸ replay, old ▸ bounded⟩
  · exact .inl other

end Alvoki.Storage.DiskSession
