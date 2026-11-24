import Alvoki.Storage.Disk.MarkedSessionTrace
import Alvoki.Storage.Disk.SegmentedAppendRecovery
import Alvoki.Storage.Disk.SegmentedCheckpointRecovery
import Alvoki.Storage.Disk.SegmentedCleanReopen
import Alvoki.Storage.Disk.SegmentedRotationRecovery
import Alvoki.Storage.Disk.SegmentedWriterTrace

namespace Alvoki.Storage.DiskSession

open WAL.Boundary WalSegmentRepair Sequential
open scoped List

/-- Completed stretches and reported reopenings of one directory. A
recovered writer is the exact predecessor of its next operation. The log
accounts for write submissions separately from ownership changes. -/
inductive SegmentedDatabaseTrace (directory : DiskDirectory) (initialDescriptor : Nat)
    (initial : SegmentedWriterState) : List MarkedSessionWrites → Nat → SegmentedWriterState → Prop where
  | start : SegmentedDatabaseTrace directory initialDescriptor initial [] initialDescriptor initial
  | writes {log descriptor before after acknowledged checkpoints}
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial log descriptor before)
      (writer : SegmentedWriterTrace directory descriptor before acknowledged checkpoints after) :
      SegmentedDatabaseTrace directory initialDescriptor initial (log ++ [⟨acknowledged, none⟩]) descriptor after
  | close {log writer descriptor before after}
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial log writer before)
      (report : SegmentedCleanReopenReport directory before writer descriptor)
      (observed : report.Valid) (endpoint : report.Installs after) :
      SegmentedDatabaseTrace directory initialDescriptor initial log descriptor after
  | appendError {log writer descriptor before after}
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial log writer before)
      (report : SegmentedAppendRecoveryReport directory before writer descriptor)
      (endpoint : report.Installs after) :
      SegmentedDatabaseTrace directory initialDescriptor initial (log ++ [⟨[], some report.failure.event⟩]) descriptor after
  | checkpointError {log writer descriptor before after}
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial log writer before)
      (report : SegmentedCheckpointFailure directory before writer descriptor)
      (endpoint : report.Installs after) :
      SegmentedDatabaseTrace directory initialDescriptor initial log descriptor after
  | rotationError {log writer descriptor before after}
      (prior : SegmentedDatabaseTrace directory initialDescriptor initial log writer before)
      (report : SegmentedRotationRecoveryReport directory before descriptor)
      (release : SegmentedFailureRelease writer)
      (observed : release.Observed (directory := directory) report.failure.poisoned report.failure.released)
      (endpoint : SegmentedRotationReopened directory descriptor before after report.run) :
      SegmentedDatabaseTrace directory initialDescriptor initial log descriptor after

theorem SegmentedDatabaseTrace.preservesReady {directory initialDescriptor initial log descriptor last}
    (trace : SegmentedDatabaseTrace directory initialDescriptor initial log descriptor last)
    (ready : initial.Ready directory initialDescriptor) :
    last.Ready directory descriptor ∧
      ∃ retained, last.history = initial.history ++ retained ∧ MarkedSessionRetention log retained := by
  induction trace with
  | start => exact ⟨ready, [], by simp, .start⟩
  | writes _ writer ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    obtain ⟨ready, appended, _, _⟩ := writer.preservesReady before
    exact ⟨ready, _, by rw [appended, history, List.append_assoc], submitted.append (Or.inl rfl)⟩
  | close _ _ observed endpoint ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    exact ⟨endpoint.preservesReady observed before, retained, endpoint.history.trans history, submitted⟩
  | appendError _ report endpoint ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    refine ⟨endpoint.preservesReady before, ?_⟩
    rcases endpoint.history with lost | kept
    · exact ⟨retained ++ [], by simpa using lost.trans history, submitted.append (Or.inl rfl)⟩
    · refine ⟨retained ++ [report.failure.event], by rw [kept, history, List.append_assoc], ?_⟩
      exact submitted.append (Or.inr ⟨report.failure.event, rfl, rfl⟩)
  | checkpointError _ _ endpoint ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    exact ⟨endpoint.preservesReady before, retained, endpoint.history.trans history, submitted⟩
  | rotationError _ _ _ _ endpoint ih =>
    obtain ⟨before, retained, history, submitted⟩ := ih
    exact ⟨endpoint.preservesReady before, retained, endpoint.history.trans history, submitted⟩

/-- A history from the first installed empty writer retains all
acknowledgements in order. It may retain the uncertain append at a
session boundary, and every retained frame is one that was submitted. -/
theorem SegmentedDatabaseTrace.fromBootstrap {directory initialDescriptor log descriptor last}
    {first : LockedFileState WalSegmentRotation.State} (bootstrap : BootstrapReady first.image)
    (held : first.owners.Owns directory initialDescriptor)
    (trace : SegmentedDatabaseTrace directory initialDescriptor (bootstrap.writerState first.owners) log descriptor last) :
    last.Ready directory descriptor ∧ MarkedSessionRetention log last.history ∧
      log.flatMap MarkedSessionWrites.acknowledged <+ last.history ∧
      last.history <+ log.flatMap MarkedSessionWrites.submitted := by
  obtain ⟨ready, retained, exactHistory, history⟩ := trace.preservesReady (bootstrap.writerReady held)
  change last.history = [] ++ retained at exactHistory
  simp only [List.nil_append] at exactHistory
  subst retained
  exact ⟨ready, history, history.orderedSubmissions⟩

/-- Reads with a pin belonging to the current writer match replay of the
retained history from the empty abstract table. -/
theorem SegmentedDatabaseTrace.pinnedReads {directory initialDescriptor initial log descriptor last}
    (trace : SegmentedDatabaseTrace directory initialDescriptor initial log descriptor last)
    (initialReady : initial.Ready directory initialDescriptor) :
    ∃ reference : SnapshotTable UInt64, SnapshotWalReplay .empty last.history reference ∧
      ∀ pin ∈ last.installed.table.pins.active,
        (∀ key, last.installed.table.lookup pin.handle key = some (reference.table.lookup key pin.sequence)) ∧
        ∀ start stop, last.installed.table.range pin.handle start stop =
          some (reference.table.range start stop pin.sequence) := by
  have ready := (trace.preservesReady initialReady).1
  obtain ⟨model, refined, represented⟩ := ready.resumed.canonical
  obtain ⟨reference, replayed⟩ := SnapshotWalReplay.fromEmpty last.history ready.resumed.ordered
  exact ⟨reference, replayed, fun _ active => represented.packedPinnedReads refined replayed active⟩

end Alvoki.Storage.DiskSession
