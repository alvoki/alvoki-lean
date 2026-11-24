import Alvoki.Storage.Disk.SegmentedDatabaseTrace
import Alvoki.Storage.Disk.SegmentedBatchAppend
import Alvoki.Storage.Disk.WalBatchSession

namespace Alvoki.Storage.DiskSession

open WalSegmentRepair WAL.Boundary Sequential
open scoped List

/-- Preserve the boundary of an uncertain batch in the trace index. A run
of ordinary database operations keeps its existing submission log. -/
inductive DatabaseSubmissions where
  | ordinary (log : List MarkedSessionWrites)
  | acknowledgedBatch (batch : List WAL.Write)
  | uncertainBatch (batch : List WAL.Write)

def DatabaseSubmissions.Retains : DatabaseSubmissions → List WAL.Write → Prop
  | .ordinary log, suffix => MarkedSessionRetention log suffix
  | .acknowledgedBatch batch, suffix => suffix = batch
  | .uncertainBatch batch, suffix => suffix = [] ∨ suffix = batch

/-- Every entry accounts for its own suffix before proceeding to the next
entry. An uncertain batch has one retention choice for all of its frames. -/
inductive DatabaseBatchRetention : List DatabaseSubmissions → List WAL.Write → Prop where
  | start : DatabaseBatchRetention [] []
  | append (prior : DatabaseBatchRetention log retained) (one : entry.Retains suffix) :
      DatabaseBatchRetention (log ++ [entry]) (retained ++ suffix)

def DatabaseSubmissions.acknowledged : DatabaseSubmissions → List WAL.Write
  | .ordinary log => log.flatMap MarkedSessionWrites.acknowledged
  | .acknowledgedBatch batch => batch
  | .uncertainBatch _ => []

def DatabaseSubmissions.submitted : DatabaseSubmissions → List WAL.Write
  | .ordinary log => log.flatMap MarkedSessionWrites.submitted
  | .acknowledgedBatch batch | .uncertainBatch batch => batch

theorem DatabaseBatchRetention.orderedSubmissions (retention : DatabaseBatchRetention log retained) :
    log.flatMap DatabaseSubmissions.acknowledged <+ retained ∧
      retained <+ log.flatMap DatabaseSubmissions.submitted := by
  induction retention with
  | start => exact ⟨.slnil, .slnil⟩
  | @append log retained entry suffix _ one ih =>
    have bounds : entry.acknowledged <+ suffix ∧ suffix <+ entry.submitted := by
      cases entry with
      | ordinary log => exact MarkedSessionRetention.orderedSubmissions one
      | acknowledgedBatch batch =>
        change suffix = batch at one
        subst suffix
        exact ⟨List.Sublist.refl _, List.Sublist.refl _⟩
      | uncertainBatch batch =>
        change suffix = [] ∨ suffix = batch at one
        rcases one with rfl | rfl <;> simp [DatabaseSubmissions.acknowledged, DatabaseSubmissions.submitted]
    exact ⟨by simpa using ih.1.append bounds.1, by simpa using ih.2.append bounds.2⟩

private theorem sameTarget {left right : Target} (pair : left.pair = right.pair)
    (first : left.first = right.first) (contents : left.trimmed = right.trimmed) : left = right := by
  have range := Option.some.inj (left.decoded.symm.trans (pair ▸ right.decoded))
  cases left
  cases right
  cases pair
  cases range
  cases first
  cases contents
  rfl

inductive SegmentedBatchDatabaseTrace (directory : DiskDirectory) (initialDescriptor : Nat)
    (initial : SegmentedWriterState) (allowCollection : Bool) :
    List DatabaseSubmissions → Nat → SegmentedWriterState → Prop where
  | start : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection [] initialDescriptor initial
  | ordinary (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (step : SegmentedDatabaseTrace directory writer before allowCollection submissions descriptor after) :
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.ordinary submissions]) descriptor after
  | acknowledgedBatch
      (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedBatchAppendReport directory before) (selected : report.Selects target) :
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.acknowledgedBatch report.batch]) writer (report.next target)
  | batchError
      (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedBatchRecoveryReport directory before writer descriptor)
      (installed : report.Installs after) :
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.uncertainBatch report.failure.batch]) descriptor after

theorem SegmentedBatchDatabaseTrace.preservesRetained
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log descriptor last)
    (ready : initial.RetainedReady directory initialDescriptor) :
    last.RetainedReady directory descriptor ∧
      ∃ retained, last.history = initial.history ++ retained ∧ DatabaseBatchRetention log retained := by
  induction trace with
  | start => exact ⟨ready, [], by simp, .start⟩
  | ordinary _ step ih =>
    obtain ⟨beforeReady, retained, beforeHistory, retention⟩ := ih
    obtain ⟨afterReady, suffix, extended, kept⟩ := step.preservesRetained beforeReady
    exact ⟨afterReady, retained ++ suffix, by rw [extended, beforeHistory, List.append_assoc],
      .append retention kept⟩
  | acknowledgedBatch _ report selected ih =>
    obtain ⟨beforeReady, retained, beforeHistory, retention⟩ := ih
    obtain ⟨chosen, selectedChosen, afterReady⟩ := report.preservesRetained beforeReady
    have first := selected.2.1.trans selectedChosen.2.1.symm
    have contents := selected.2.2.trans ((congrArg (fun first => WAL.encode (List.drop first _)) first).trans
      selectedChosen.2.2.symm)
    have same := sameTarget (selected.1.trans selectedChosen.1.symm) first contents
    cases same
    refine ⟨afterReady, _, ?_, .append retention rfl⟩
    change _ ++ _ = _
    rw [beforeHistory, List.append_assoc]
  | batchError _ report installed ih =>
    obtain ⟨_, retained, beforeHistory, retention⟩ := ih
    refine ⟨installed.retained, ?_⟩
    rcases installed.history with lost | kept
    · exact ⟨retained ++ [], by simpa using lost.trans beforeHistory, .append retention (.inl rfl)⟩
    · exact ⟨retained ++ report.failure.batch, by rw [kept, beforeHistory, List.append_assoc],
        .append retention (.inr rfl)⟩

/-- Extend the trace using the actual failed commit, lock release and
bounded reopen reports. Retained readiness is derived from the prior trace. -/
theorem SegmentedBatchDatabaseTrace.reopenAfterBatchError
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (ready : initial.RetainedReady directory initialDescriptor)
    (report : SegmentedBatchRecoveryReport directory before writer descriptor) :
    ∃ after, report.Installs after ∧
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.uncertainBatch report.failure.batch]) descriptor after := by
  obtain ⟨after, installed, _⟩ := report.installsRetained (trace.preservesRetained ready).1
  exact ⟨after, installed, .batchError trace report installed⟩

/-- Current-session reads after any covered sequence agree with replay of
the retained history, including after an uncertain batch. -/
theorem SegmentedBatchDatabaseTrace.pinnedReads
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log descriptor last)
    (ready : initial.RetainedReady directory initialDescriptor) :
    ∃ reference : SnapshotTable UInt64, SnapshotWalReplay .empty last.history reference ∧
      ∀ pin ∈ last.installed.table.pins.active,
        (∀ key, last.installed.table.lookup pin.handle key = some (reference.table.lookup key pin.sequence)) ∧
        ∀ start stop, last.installed.table.range pin.handle start stop =
          some (reference.table.range start stop pin.sequence) :=
  (trace.preservesRetained ready).1.pinnedReads

end Alvoki.Storage.DiskSession
