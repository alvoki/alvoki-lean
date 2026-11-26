import Alvoki.Storage.Disk.NativeFailedOpenTerminalLedger
import Alvoki.Storage.Disk.NativeGroupedWriteRecovery
import Alvoki.Storage.Disk.NativeReadyCallRefinement

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentCommit WalSegmentRepair
open WAL.Boundary (WalInodeImage)

section Grouped

variable {heap stream : Type} {opened : NativeOpenedHandle heap}
  (current : NativeOpenedPosition opened) (view : OpenCloseHeapView heap FileImage)
  (writes : NativeReadyWriteCalls opened) (issuer : opened.LatestIssuer)
  (inodes : heap → WalInodeImage) {runs : heap → RunUnlinkImage}
  (observe : ∀ atHeap, RunDirectoryInodeView current.current.ready.state.session.directory (inodes atHeap) (runs atHeap))

local notation "state" => current.current.ready.state
local notation "dir" => current.current.ready.state.session.directory
local notation "installed" => current.current.ready.state.writer.installed
local notation "storage" => fun atHeap => RunDirectoryInodeView.storageObservation (observe atHeap)
local notation "names" => fun atHeap => CheckpointSurvivingFiles.names (CheckpointStorageObservation.files (storage atHeap))
local notation "visible" => fun atHeap => WalInodeImage.visible (inodes atHeap)
local notation "cache" => writes.cacheAtPosition current
local notation "appender" => writes.appender
local notation "stager" => writes.stager
local notation "syncer" => writes.syncer
local notation "lookup" => writes.lookup
local notation "rename" => writes.rename

/-- A literal grouped write error can end with the last rejected open
after its sampled reboot. The earlier table's pending submission is
recorded once and the old marker fixes the terminal replay. -/
theorem NativeOpenedPosition.stopsAfterGroupedWriteRetries
    {origin : NativeExecutionPosition} {events : List NativeExecutionEvent}
    (prior : origin.LedgerSuffix events current.current)
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
    (request : WriteRequest)
    {failed rebooted reached : heap} {cause : IO.Error} (nonempty : request.rows ≠ [])
    (observed : (NativeReturnedCall.write request (.error (.commitUnknown cause))).Reaches
      writes issuer (current.pins.map NativeOpenedPin.raw) current.reached failed)
    (initial : NativeReadyStorage state (storage current.reached))
    (groupEffects : current.GroupedErrorEffects view cache appender stager syncer inodes observe inode buffered
      request lookup failed cause)
    (reboot : RawWriteRebootEntry state view storage names visible failed rebooted)
    (reset : reboot.DurableReset)
    {firstOffset : Nat}
    (nameEffects : current.WalNameEffects appender stager syncer cache request lookup rename storage
      firstOffset (current.current.history.length + request.rows.length))
    (initialWindow : current.WalWindowAt storage firstOffset (current.current.history.length + request.rows.length))
    (source : RawMarkedOpenInterpreter heap stream) {returns : List (FilePath × IO.Error)}
    (attempts : source.FailedCalls rebooted returns reached) (retried : returns ≠ [])
    (retryEffects : RawOpenRetryTrace.SelectedEffects view source rebooted (state).writer.target
      (fun atHeap => ⟨names atHeap, fun inode => [visible atHeap inode]⟩) (state).selectedRetryPath
      (fun atHeap => (state).writer.wal.NamespaceWindow dir firstOffset
        (current.current.history.length + request.rows.length) (names atHeap) ∧
        RawOpenRetryTrace.KeeperAt view dir (state).writer.target names visible atHeap ∧
        (state).SelectedRetryDurability (state).writer.target (storage atHeap) ∧
        RawOpenRetryTrace.LaterWalAt view dir (state).writer.target names atHeap) attempts) :
    (∀ event ∈ events, event.uncertainBatchWhole) ∧
    ∃ batch table guarded poisoned,
      prepareBatch (installed).table request.rows = some (batch, table) ∧
      checkActiveSegmentWith dir installed lookup current.reached = .ok () guarded ∧
      opened.set opened.phase .poisoned guarded = .ok () poisoned ∧
      let keeper := (dir).file (.walSegment (installed).activeFirst)
      let staging := (dir).file .stagedWalBoundary
      let groupFailed := ∃ appended staged,
        writes.appender.run (cache).active keeper (WAL.encodeBatch batch) poisoned = .ok () appended ∧
        writes.stager.run (cache).pending staging
          (WAL.Boundary.encode ((installed).walBytes + WAL.frameSize * request.rows.length).toUInt64) appended = .ok () staged ∧
        writes.syncer.group (dir).path (cache).directory (cache).active (cache).pending #[keeper, staging] staged =
          .error cause failed
      ¬ groupFailed ∨ (groupFailed ∧ ∃ earlier input diagnostic issued,
        returns = earlier ++ [(input, diagnostic)] ∧ source.FailedCalls rebooted earlier issued ∧
        source.openTable input issued = .error diagnostic reached ∧
        RawOpenRetryTrace.SelectedEntry view state (state).writer.target names visible reached ∧
        (state).SelectedRetryDurability (state).writer.target (storage reached) ∧
        let history := origin.history ++ events.flatMap NativeExecutionEvent.writes
        let submissions := (origin.submissions ++ events.flatMap NativeExecutionEvent.submissions) ++ [.uncertainBatch batch]
        let reads := origin.ready.reads ++ events.flatMap NativeExecutionEvent.reads
        PendingClientReplay submissions reads history ∧ ∀ read ∈ reads, read.BoundedBy history.length) := by
  have returned := writes.returnedWriteAt current observed
  obtain ⟨_, batch, table, guarded, poisoned, prepared, fits, guard, assigned, classified⟩ :=
    current.selectsAfterGroupedError view cache appender stager syncer inodes observe inode buffered
      request lookup rename nonempty returned initial groupEffects reboot
  refine ⟨prior.whole, batch, table, guarded, poisoned, prepared, guard, assigned, ?_⟩
  rcases classified with ⟨grouped, admitted, selected, _, _⟩ | other
  · refine .inr ⟨grouped, ?_⟩
    have framed := current.preservesWalNamesAfterCommitUnknown appender stager syncer cache request lookup rename
      nonempty returned nameEffects
    have window := reboot.walNamespace framed initialWindow.2
    have upper : (current.current.history ++ batch).length = current.current.history.length + request.rows.length := by
      simp only [List.length_append, (prepareBatch_spec prepared).1]
    obtain ⟨_, earlier, input, diagnostic, issued, reported, previous, call, plan, _, last, physical, _, _, replay, bounded⟩ :=
      NativeExecutionPosition.refinesFailedOpenTerminalLedger (current := current.current)
        prior prepared fits admitted storage visible initialWindow.1 selected
        (by simpa only [upper] using window) (reboot.startsDurableRetry reset selected).2
        (reboot.laterNames selected.valid.selected.symm) attempts retried (by simpa only [upper] using retryEffects)
    have old : plan.history = origin.history ++ events.flatMap NativeExecutionEvent.writes :=
      plan.oldHistory.trans prior.history
    exact ⟨earlier, input, diagnostic, issued, reported, previous, call, last, physical, old ▸ replay, old ▸ bounded⟩
  · exact .inl other

end Grouped

end Alvoki.Storage.DiskSession
