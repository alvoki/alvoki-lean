import Alvoki.Storage.Disk.MarkedSessionTrace
import Alvoki.Storage.Disk.SegmentedCollectionPowerLoss
import Alvoki.Storage.Disk.SegmentedCollectionRetry
import Alvoki.Storage.Disk.SegmentedCollectionLiveReopen
import Alvoki.Storage.Disk.SegmentedAppendRecovery
import Alvoki.Storage.Disk.SegmentedAppendPowerLoss
import Alvoki.Storage.Disk.SegmentedCheckpointRecovery
import Alvoki.Storage.Disk.SegmentedCheckpointPowerLoss
import Alvoki.Storage.Disk.SegmentedCleanReopen
import Alvoki.Storage.Disk.SegmentedMarkerPowerLoss
import Alvoki.Storage.Disk.SegmentedReadyPowerLoss
import Alvoki.Storage.Disk.SegmentedRotationRecovery
import Alvoki.Storage.Disk.SegmentedRotationPowerLoss
import Alvoki.Storage.Disk.SegmentedRotationStep
import Alvoki.Storage.Disk.SegmentedWriterTrace
import Alvoki.Storage.Disk.SessionReadGuards

namespace Alvoki.Storage.DiskSession

open System WAL.Boundary WalSegmentRepair Sequential
open scoped List

/-- Completed stretches and reported reopenings of one directory. A
recovered writer is the exact predecessor of its next operation. The log
accounts for write submissions separately from ownership changes.
The collection-free specialization also preserves the full WAL chain. -/
inductive SegmentedDatabaseTrace (directory : DiskDirectory) (initialDescriptor : Nat)
    (initial : SegmentedWriterState) (allowCollection : Bool) : List MarkedSessionWrites → Nat → SegmentedWriterState → Prop where
  | start : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection [] initialDescriptor initial
  | writes {log descriptor before after acknowledged checkpoints}
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor before)
      (writer : SegmentedWriterTrace directory descriptor before acknowledged checkpoints after) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection (log ++ [⟨acknowledged, none⟩]) descriptor after
  | rotate {log descriptor before target}
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor before)
      (report : SegmentedRotationReport directory before) (selected : report.Selects target) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor (report.next target)
  | close {log writer descriptor before after}
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedCleanReopenReport directory before writer descriptor)
      (observed : report.Valid) (endpoint : report.Installs after) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after
  | powerLoss {log writer descriptor before after}
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedReadyPowerLossReport directory before writer descriptor)
      (observed : report.Valid) (endpoint : report.Installs after) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after
  | appendError {log writer descriptor before after}
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedAppendRecoveryReport directory before writer descriptor)
      (endpoint : report.Installs after) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection (log ++ [⟨[], some report.failure.event⟩]) descriptor after
  | appendPowerLoss {log writer descriptor before after}
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedAppendPowerLossReport directory before writer descriptor)
      (observed : report.Valid) (endpoint : report.Installs after) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection (log ++ [⟨[], some report.event⟩]) descriptor after
  | markerPowerLoss {log writer descriptor before after}
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedMarkerPowerLossReport directory before writer descriptor)
      (observed : report.Valid) (endpoint : report.Installs after) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection (log ++ [⟨[], some report.event⟩]) descriptor after
  | checkpointError {log writer descriptor before after}
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedCheckpointFailure directory before writer descriptor)
      (endpoint : report.Installs after) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after
  | checkpointPowerLoss {log writer descriptor before after}
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedCheckpointPowerLossReport directory before writer descriptor)
      (observed : report.Valid) (endpoint : report.Installs after) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after
  | rotationError {log writer descriptor before after}
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedRotationRecoveryReport directory before descriptor)
      (release : SegmentedFailureRelease writer)
      (observed : release.Observed (directory := directory) report.failure.poisoned report.failure.released)
      (endpoint : SegmentedRotationReopened directory descriptor before after report.run) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after
  | rotationPowerLoss {log writer descriptor before after}
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedRotationPowerLossReport directory before descriptor)
      (endpoint : report.Installs after) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after
  | collectionPowerLoss {log writer descriptor before after}
      (enabled : allowCollection = true)
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedCollectionPowerLossReport directory before writer descriptor)
      (observed : report.Valid) (endpoint : report.Installs after) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after
  | collection {log descriptor before after}
      (enabled : allowCollection = true)
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor before)
      (report : SegmentedCollectionReport directory before) (endpoint : report.Installs after) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after
  | collectionRetry {log descriptor before reached remaining}
      (enabled : allowCollection = true)
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor before)
      (failed : SegmentedCollectionErrors directory before reached)
      (report : SegmentedCollectionReport directory before) (returned : report.runFrom reached = .ok () remaining) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor
        (before.afterWalCollection remaining)
  | collectionReopen {log writer descriptor before after}
      (enabled : allowCollection = true)
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedCollectionReopenReport directory before writer descriptor)
      (observed : report.Valid) (endpoint : report.Installs after) :
      SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor after

private theorem retainsInterruptedAppend {initial before after : List WAL.Write} {log retained event}
    (history : before = initial ++ retained) (submitted : MarkedSessionRetention log retained)
    (survived : after = before ∨ after = before ++ [event]) :
    ∃ suffix, after = initial ++ suffix ∧ MarkedSessionRetention (log ++ [⟨[], some event⟩]) suffix := by
  rcases survived with lost | kept
  · exact ⟨retained ++ [], by simpa using lost.trans history, submitted.append (Or.inl rfl)⟩
  · refine ⟨retained ++ [event], by rw [kept, history, List.append_assoc], ?_⟩
    exact submitted.append (Or.inr ⟨event, rfl, rfl⟩)

theorem SegmentedDatabaseTrace.preservesReady {directory initialDescriptor initial log descriptor last}
    (trace : SegmentedDatabaseTrace directory initialDescriptor initial false log descriptor last)
    (ready : initial.Ready directory initialDescriptor) :
    last.Ready directory descriptor ∧
      ∃ retained, last.history = initial.history ++ retained ∧ MarkedSessionRetention log retained := by
  induction trace with
  | start => exact ⟨ready, [], by simp, .start⟩
  | writes _ writer ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    obtain ⟨ready, appended, _, _⟩ := writer.preservesReady before
    exact ⟨ready, _, by rw [appended, history, List.append_assoc], submitted.append (Or.inl rfl)⟩
  | rotate _ report selected ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    exact ⟨report.preservesReady before selected, retained, history, submitted⟩
  | close _ _ observed endpoint ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    exact ⟨endpoint.preservesReady observed before, retained, endpoint.history.trans history, submitted⟩
  | powerLoss _ _ observed endpoint ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    exact ⟨endpoint.preservesReady observed before, retained, endpoint.history.trans history, submitted⟩
  | appendError _ _ endpoint ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    exact ⟨endpoint.preservesReady before, retainsInterruptedAppend history submitted endpoint.history⟩
  | appendPowerLoss _ _ observed endpoint ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    exact ⟨endpoint.preservesReady observed before, retainsInterruptedAppend history submitted (.inl endpoint.history)⟩
  | markerPowerLoss _ _ observed endpoint ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    exact ⟨endpoint.preservesReady observed before, retainsInterruptedAppend history submitted endpoint.history⟩
  | checkpointError _ _ endpoint ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    exact ⟨endpoint.preservesReady before, retained, endpoint.history.trans history, submitted⟩
  | checkpointPowerLoss _ _ observed endpoint ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    exact ⟨endpoint.preservesReady observed before, retained, endpoint.history.trans history, submitted⟩
  | rotationError _ _ _ _ endpoint ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    exact ⟨endpoint.preservesReady before, retained, endpoint.history.trans history, submitted⟩
  | rotationPowerLoss _ _ endpoint ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    exact ⟨endpoint.preservesReady before, retained, endpoint.history.trans history, submitted⟩
  | collectionPowerLoss enabled => cases enabled
  | collection enabled => cases enabled
  | collectionRetry enabled => cases enabled
  | collectionReopen enabled => cases enabled

theorem SegmentedDatabaseTrace.preservesRetained {directory initialDescriptor initial allowCollection log descriptor last}
    (trace : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor last)
    (ready : initial.RetainedReady directory initialDescriptor) :
    last.RetainedReady directory descriptor ∧
      ∃ retained, last.history = initial.history ++ retained ∧ MarkedSessionRetention log retained := by
  induction trace with
  | start => exact ⟨ready, [], by simp, .start⟩
  | writes _ writer ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    obtain ⟨ready, appended⟩ := writer.preservesRetained before
    exact ⟨ready, _, by rw [appended, history, List.append_assoc], submitted.append (Or.inl rfl)⟩
  | rotate _ report selected ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    exact ⟨report.preservesRetainedReady before selected, retained, history, submitted⟩
  | close _ _ observed endpoint ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    exact ⟨endpoint.preservesRetained observed before, retained, endpoint.history.trans history, submitted⟩
  | powerLoss _ _ observed endpoint ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    exact ⟨endpoint.preservesRetained observed before, retained, endpoint.history.trans history, submitted⟩
  | appendError _ _ endpoint ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    exact ⟨endpoint.preservesRetained before, retainsInterruptedAppend history submitted endpoint.history⟩
  | appendPowerLoss _ _ observed endpoint ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    exact ⟨endpoint.preservesRetained observed before, retainsInterruptedAppend history submitted (.inl endpoint.history)⟩
  | markerPowerLoss _ _ observed endpoint ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    exact ⟨endpoint.preservesRetained observed before, retainsInterruptedAppend history submitted endpoint.history⟩
  | checkpointError _ _ endpoint ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    exact ⟨endpoint.preservesRetained before, retained, endpoint.history.trans history, submitted⟩
  | checkpointPowerLoss _ _ observed endpoint ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    exact ⟨endpoint.preservesRetained observed before, retained, endpoint.history.trans history, submitted⟩
  | rotationError _ _ _ _ endpoint ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    exact ⟨endpoint.preservesRetainedReady before, retained, endpoint.history.trans history, submitted⟩
  | rotationPowerLoss _ _ endpoint ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    exact ⟨endpoint.preservesRetainedReady before, retained, endpoint.history.trans history, submitted⟩
  | collectionPowerLoss _ _ _ observed endpoint ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    exact ⟨endpoint.preservesRetained observed before, retained, endpoint.history.trans history, submitted⟩
  | collection _ _ _ endpoint ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    exact ⟨endpoint.preservesRetained before, retained, endpoint.history.trans history, submitted⟩
  | collectionRetry _ _ failed report returned ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    exact ⟨(failed.settles before report returned).2, retained, history, submitted⟩
  | collectionReopen _ _ _ observed endpoint ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    exact ⟨endpoint.preservesRetained observed before, retained, endpoint.history.trans history, submitted⟩

/-- A history from the first installed empty writer retains all
acknowledgements in order. It may retain the uncertain append at a
session boundary, and every retained frame is one that was submitted. -/
theorem SegmentedDatabaseTrace.fromBootstrap {directory initialDescriptor allowCollection log descriptor last}
    {first : LockedFileState WalSegmentRotation.State} (bootstrap : BootstrapReady first.image)
    (held : first.owners.Owns directory initialDescriptor)
    (trace : SegmentedDatabaseTrace directory initialDescriptor (bootstrap.writerState first.owners) allowCollection log descriptor last) :
    last.RetainedReady directory descriptor ∧ MarkedSessionRetention log last.history ∧
      log.flatMap MarkedSessionWrites.acknowledged <+ last.history ∧
      last.history <+ log.flatMap MarkedSessionWrites.submitted := by
  obtain ⟨ready, retained, exactHistory, history⟩ := trace.preservesRetained (bootstrap.writerReady held).toRetained
  change last.history = [] ++ retained at exactHistory
  simp only [List.nil_append] at exactHistory
  subst retained
  exact ⟨ready, history, history.orderedSubmissions⟩

/-- Start the mixed history from the actual shared bootstrap attempt and
its returned session, using only the reached native callback reports. -/
theorem SegmentedDatabaseTrace.fromBootstrapRun (directory : DiskDirectory) (descriptor nextRef : Nat)
    (before : LockedFileState WalSegmentRotation.State) (valid : BootstrapValid before.image)
    (acquired : Except IO.Error Bool) (acquisition : TryLockObserves before.owners directory acquired)
    (unlock : UnlockReport) (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (readEmpty : FilePath → Except IO.Error (Option ByteArray))
    (metadata : FilePath → Except IO.Error (Option IO.FS.Metadata))
    (seen : ∀ empty, readEmpty (directory.file (.walSegment 0)) = .ok empty → before.image.observeSuccessor = empty)
    (createEmpty : FilePath → EStateM IO.Error WalSegmentRotation.State Unit)
    (write : FilePath → ByteArray → EStateM IO.Error WalSegmentRotation.State Unit)
    (sync : Array FilePath → EStateM IO.Error WalSegmentRotation.State Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error WalSegmentRotation.State Unit)
    (rotation : WalSegmentRotation.EffectReports
      (WalSegmentRotation.performPaths directory 0 createEmpty (fun path => sync #[path])))
    (marker : BootstrapMarkerReports (Publication.performReplacement (write · (WAL.Boundary.encode 0))
      sync renameFile (directory.file .stagedWalBoundary) directory.path (fun _ => directory.file .walBoundary) #[]))
    {session : SegmentedSession} {after : LockedFileState WalSegmentRotation.State} :
    let recover := bootstrapSegmentedWith directory
      (fun path => liftExcept (list path)) (fun path => liftExcept (readEmpty path))
      (fun path => liftExcept (metadata path)) createEmpty write sync renameFile
    runOpenWithInstallation directory descriptor nextRef acquired unlock recover before = .ok session after →
    ∃ bootstrap : BootstrapReady after.image,
      session = ⟨directory, descriptor, .ready (bootstrap.writerState after.owners).installed, nextRef, nextRef + 1⟩ ∧
      ∀ {allowCollection log next last},
        SegmentedDatabaseTrace directory descriptor (bootstrap.writerState after.owners) allowCollection log next last →
        last.RetainedReady directory next ∧ MarkedSessionRetention log last.history ∧
          log.flatMap MarkedSessionWrites.acknowledged <+ last.history ∧
          last.history <+ log.flatMap MarkedSessionWrites.submitted := by
  intro recover opened
  obtain ⟨returned, _, owners, _, bootstrap⟩ := runOpenWithInstallation_bootstrapReady directory descriptor nextRef
    before valid acquired acquisition unlock list readEmpty metadata seen createEmpty write sync renameFile rotation
    marker opened
  refine ⟨bootstrap, returned, fun trace => trace.fromBootstrap bootstrap ?_⟩
  simp [owners, LockOwners.Owns, LockOwners.set]

/-- Reads with a pin belonging to the current writer match replay of the
retained history from the empty abstract table. -/
theorem SegmentedDatabaseTrace.pinnedReads {directory initialDescriptor initial allowCollection log descriptor last}
    (trace : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor last)
    (initialReady : initial.RetainedReady directory initialDescriptor) :
    ∃ reference : SnapshotTable UInt64, SnapshotWalReplay .empty last.history reference ∧
      ∀ pin ∈ last.installed.table.pins.active,
        (∀ key, last.installed.table.lookup pin.handle key = some (reference.table.lookup key pin.sequence)) ∧
        ∀ start stop, last.installed.table.range pin.handle start stop =
          some (reference.table.range start stop pin.sequence) :=
  (trace.preservesRetained initialReady).1.pinnedReads

/-- Interpret the adapter's reported session comparison on the installed
writer. A foreign token yields no result even if its handle number is in use. -/
theorem SegmentedDatabaseTrace.guardedPinnedReads {directory initialDescriptor initial allowCollection log descriptor last}
    (trace : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor last)
    (initialReady : initial.RetainedReady directory initialDescriptor) {sameSession : Bool} {issuer current : Nat}
    (compared : sameSession = decide (issuer = current)) :
    ∃ reference : SnapshotTable UInt64, SnapshotWalReplay .empty last.history reference ∧
      ∀ pin ∈ last.installed.table.pins.active,
        (∀ key, readWithHandle (.ready last.installed.table) sameSession (·.lookup pin.handle key) =
          .ok (if issuer = current then some (reference.table.lookup key pin.sequence) else none)) ∧
        ∀ start stop, readWithHandle (.ready last.installed.table) sameSession (·.range pin.handle start stop) =
          .ok (if issuer = current then some (reference.table.range start stop pin.sequence) else none) := by
  obtain ⟨reference, replayed, pinned⟩ := trace.pinnedReads initialReady
  refine ⟨reference, replayed, ?_⟩
  intro pin active
  by_cases localHandle : issuer = current
  · simp only [compared.trans (decide_eq_true localHandle), ite_eq_left localHandle]
    obtain ⟨lookup, range⟩ := pinned pin active
    exact ⟨fun key => congrArg Except.ok (lookup key), fun start stop => congrArg Except.ok (range start stop)⟩
  · simp only [ite_eq_right localHandle]
    exact ⟨fun key => readWithHandle_foreign _ (·.lookup pin.handle key) compared localHandle,
      fun start stop => readWithHandle_foreign _ (·.range pin.handle start stop) compared localHandle⟩

/-- After any covered reopen, every supported sequence can be acquired
against the returned table and reads the same snapshot as abstract replay. -/
theorem SegmentedDatabaseTrace.acquireReads {directory initialDescriptor initial allowCollection log descriptor last}
    (trace : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor last)
    (initialReady : initial.RetainedReady directory initialDescriptor) {snapshot : UInt64}
    (retained : last.installed.table.pins.floor ≤ snapshot) (committed : snapshot ≤ last.installed.table.committed) :
    ∃ reference : SnapshotTable UInt64, SnapshotWalReplay .empty last.history reference ∧
      ∃ pin pinned, last.installed.table.acquireAt snapshot = some (pin, pinned) ∧
        (∀ key, pinned.lookup pin.handle key = some (reference.table.lookup key snapshot)) ∧
        ∀ start stop, pinned.range pin.handle start stop = some (reference.table.range start stop snapshot) :=
  (trace.preservesRetained initialReady).1.acquireReads retained committed

/-- An earlier pin's sequence reads the same values after reacquiring it
in the final session, provided the final writer still retains it. -/
theorem SegmentedDatabaseTrace.reacquireReadsStable {directory initialDescriptor initial allowCollection log descriptor last}
    (trace : SegmentedDatabaseTrace directory initialDescriptor initial allowCollection log descriptor last)
    (initialReady : initial.RetainedReady directory initialDescriptor) {oldPin : SnapshotPin}
    (active : oldPin ∈ initial.installed.table.pins.active)
    (retained : last.installed.table.pins.floor ≤ oldPin.sequence) :
    ∃ newPin pinned, last.installed.table.acquireAt oldPin.sequence = some (newPin, pinned) ∧
      newPin.sequence = oldPin.sequence ∧
      (∀ key, pinned.lookup newPin.handle key = initial.installed.table.lookup oldPin.handle key) ∧
      ∀ start stop, pinned.range newPin.handle start stop = initial.installed.table.range oldPin.handle start stop := by
  obtain ⟨ready, _, history, _⟩ := trace.preservesRetained initialReady
  exact initialReady.reacquireReadsStable ready history active retained

end Alvoki.Storage.DiskSession
