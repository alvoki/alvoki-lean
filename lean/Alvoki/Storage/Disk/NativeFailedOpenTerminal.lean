import Alvoki.Storage.Disk.NativeFailedOpenTerminalLedger
import Alvoki.Storage.Disk.NativeGroupedWriteRecovery

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentCommit WalSegmentRepair
open WAL.Boundary (WalInodeImage)

section Grouped

variable {heap stream : Type} {opened : NativeOpenedHandle heap}
  (current : NativeOpenedPosition opened) (view : OpenCloseHeapView heap FileImage)
  (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)
  (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap) (syncer : RawSyncCalls heap)
  (inodes : heap → WalInodeImage) {runs : heap → RunUnlinkImage}
  (observe : ∀ atHeap, RunDirectoryInodeView current.current.ready.state.session.directory (inodes atHeap) (runs atHeap))

local notation "state" => current.current.ready.state
local notation "dir" => current.current.ready.state.session.directory
local notation "installed" => current.current.ready.state.writer.installed
local notation "storage" => fun atHeap => RunDirectoryInodeView.storageObservation (observe atHeap)
local notation "names" => fun atHeap => CheckpointSurvivingFiles.names (CheckpointStorageObservation.files (storage atHeap))
local notation "visible" => fun atHeap => WalInodeImage.visible (inodes atHeap)

/-- A literal grouped write error can end with the last rejected open
after its sampled reboot. The earlier table's pending submission is
recorded once and the old marker fixes the terminal replay. -/
theorem NativeOpenedPosition.stopsAfterGroupedWriteRetries
    {origin : NativeExecutionPosition} {events : List NativeExecutionEvent}
    (prior : origin.LedgerSuffix events current.current)
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
    (request : WriteRequest) (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {failed rebooted reached : heap} {cause : IO.Error} (nonempty : request.rows ≠ [])
    (returned : request.runOnRawOpenPhase dir lookup (appender.run cache.active) (stager.run cache.pending)
      (syncer.group (dir).path cache.directory cache.active cache.pending) rename opened.phase opened.get opened.set
      current.reached = .error (.commitUnknown cause) failed)
    (initial : NativeReadyStorage state (storage current.reached))
    (groupEffects : current.GroupedErrorEffects view cache appender stager syncer inodes observe inode buffered
      request lookup failed cause)
    (reboot : RawWriteRebootEntry state view storage names visible failed rebooted)
    (reset : reboot.DurableReset)
    {firstOffset : Nat} (covers : ∀ offset ∈ (state).writer.wal.segments.map WalSegment.first, firstOffset ≤ offset)
    (nameEffects : current.WalNameEffects appender stager syncer cache request lookup rename storage
      firstOffset (current.current.history.length + request.rows.length))
    (initialWindow : (state).writer.wal.SettledNamespaceWindow dir firstOffset
      (current.current.history.length + request.rows.length) (storage current.reached))
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
        appender.run cache.active keeper (WAL.encodeBatch batch) poisoned = .ok () appended ∧
        stager.run cache.pending staging
          (WAL.Boundary.encode ((installed).walBytes + WAL.frameSize * request.rows.length).toUInt64) appended = .ok () staged ∧
        syncer.group (dir).path cache.directory cache.active cache.pending #[keeper, staging] staged = .error cause failed
      ¬ groupFailed ∨ (groupFailed ∧ ∃ earlier input diagnostic issued,
        returns = earlier ++ [(input, diagnostic)] ∧ source.FailedCalls rebooted earlier issued ∧
        source.openTable input issued = .error diagnostic reached ∧
        RawOpenRetryTrace.SelectedEntry view state (state).writer.target names visible reached ∧
        (state).SelectedRetryDurability (state).writer.target (storage reached) ∧
        let history := origin.history ++ events.flatMap NativeExecutionEvent.writes
        let submissions := (origin.submissions ++ events.flatMap NativeExecutionEvent.submissions) ++ [.uncertainBatch batch]
        let reads := origin.ready.reads ++ events.flatMap NativeExecutionEvent.reads
        PendingClientReplay submissions reads history ∧ ∀ read ∈ reads, read.BoundedBy history.length) := by
  obtain ⟨_, batch, table, guarded, poisoned, prepared, fits, guard, assigned, classified⟩ :=
    current.selectsAfterGroupedError view cache appender stager syncer inodes observe inode buffered
      request lookup rename nonempty returned initial groupEffects reboot
  refine ⟨prior.whole, batch, table, guarded, poisoned, prepared, guard, assigned, ?_⟩
  rcases classified with ⟨grouped, admitted, selected, _, _⟩ | other
  · refine .inr ⟨grouped, ?_⟩
    have framed := current.preservesWalNamesAfterCommitUnknown appender stager syncer cache request lookup rename
      nonempty returned nameEffects
    have window := reboot.walNamespace framed initialWindow
    have upper : (current.current.history ++ batch).length = current.current.history.length + request.rows.length := by
      simp only [List.length_append, (prepareBatch_spec prepared).1]
    obtain ⟨_, earlier, input, diagnostic, issued, reported, previous, call, plan, _, last, physical, _, _, replay, bounded⟩ :=
      NativeExecutionPosition.refinesFailedOpenTerminalLedger (current := current.current)
        prior prepared fits admitted storage visible covers selected
        (by simpa only [upper] using window) (reboot.startsDurableRetry reset selected).2
        (reboot.laterNames selected.valid.selected.symm) attempts retried (by simpa only [upper] using retryEffects)
    have old : plan.history = origin.history ++ events.flatMap NativeExecutionEvent.writes :=
      plan.oldHistory.trans prior.history
    exact ⟨earlier, input, diagnostic, issued, reported, previous, call, last, physical, old ▸ replay, old ▸ bounded⟩
  · exact .inl other

end Grouped

end Alvoki.Storage.DiskSession
