import Alvoki.Storage.Disk.SegmentedDatabaseTrace
import Alvoki.Storage.Disk.SegmentedCheckpointObservedReopen
import Alvoki.Storage.Disk.SessionReadGuards
import Alvoki.Storage.Disk.SegmentedBatchAppend
import Alvoki.Storage.Disk.SegmentedBatchAppendProcessExit
import Alvoki.Storage.Disk.SegmentedBatchCachedPowerLoss
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
  | checkpointPowerLossObserved {files : Type}
      (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (cut : CheckpointPowerCut directory before) {published : CheckpointPublication.Image}
      (projected : before.published.executeVersioned cut.checkpoint.plan cut.checkpoint.cut = some published)
      {pair : DirectoryPublication.Bindings}
      (survives : pair ∈ (published.segmentedCheckpointView before.wal).directory.crashImages)
      {retry : LockedFileState FileImage}
      (failures : BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
        ⟨(CheckpointPowerCut.physical before published).crash pair (some before.wal.active.bytes) [],
          before.owners.set (directory.file .lock) none⟩ retry)
      (selected : retry.image.directory.active = pair)
      {layout : CanonicalKeeperLayout retry.image before.history}
      {observed : MarkedRetryChunkReports files directory layout published}
      (installed : CheckpointChunkWriter directory before published observed after) :
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log observed.slot.description after
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
  | batchPowerLoss
      (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (cut : SegmentedBatchMarkerPowerLossReport directory before writer) (observed : cut.Valid)
      (report : cut.CachedReopenReports descriptor) (installed : report.Installs after) :
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.uncertainBatch cut.batch]) descriptor after
  | batchMarkerProcessExit
      (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (cut : SegmentedBatchMarkerPowerLossReport directory before writer) (observed : cut.Reached)
      (report : cut.ProcessExitCachedReopenReports descriptor) (installed : report.reopen.InstallsFromCut after) :
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.uncertainBatch cut.batch]) descriptor after
  | batchAppendPowerLoss
      (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedBatchAppendPowerLossReport directory before descriptor) (observed : report.Valid)
      (installed : report.Installs after) :
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.uncertainBatch report.reopen.batch]) descriptor after
  | batchAppendProcessExit
      (prior : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
      (report : SegmentedBatchAppendProcessExitReport directory before writer descriptor) (observed : report.reopen.Valid)
      (installed : report.reopen.Installs after) :
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.uncertainBatch report.reopen.batch]) descriptor after

private theorem appendUncertainBatch {initial before after batch retained : List WAL.Write}
    {log : List DatabaseSubmissions} (retention : DatabaseBatchRetention log retained)
    (history : before = initial ++ retained) (selected : after = before ∨ after = before ++ batch) :
    ∃ suffix, after = initial ++ suffix ∧ DatabaseBatchRetention (log ++ [.uncertainBatch batch]) suffix := by
  rcases selected with lost | kept
  · exact ⟨retained ++ [], by simpa using lost.trans history, .append retention (.inl rfl)⟩
  · exact ⟨retained ++ batch, by rw [kept, history, List.append_assoc], .append retention (.inr rfl)⟩

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
  | checkpointPowerLossObserved _ _ _ _ _ _ installed ih =>
    obtain ⟨_, retained, history, retention⟩ := ih
    exact ⟨installed.retained, retained, installed.history.trans history, retention⟩
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
  | batchError _ _ installed ih
  | batchPowerLoss _ _ _ _ installed ih
  | batchMarkerProcessExit _ _ _ _ installed ih =>
    obtain ⟨_, _, history, retention⟩ := ih
    exact ⟨installed.retained, appendUncertainBatch retention history installed.history⟩
  | batchAppendPowerLoss _ _ _ installed ih
  | batchAppendProcessExit _ _ _ installed ih =>
    obtain ⟨_, _, history, retention⟩ := ih
    exact ⟨installed.retained, appendUncertainBatch retention history (.inl installed.history)⟩

/-- Publish the observed checkpoint recovery as a step in the mixed trace.
Checkpointing changes the reachable run map but adds no write submission. -/
theorem SegmentedBatchDatabaseTrace.reopenAfterCheckpointPowerLossChunks {files : Type}
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (ready : initial.RetainedReady directory initialDescriptor) (cut : CheckpointPowerCut directory before)
    (published : CheckpointPublication.Image)
    (projected : before.published.executeVersioned cut.checkpoint.plan cut.checkpoint.cut = some published)
    (pair : DirectoryPublication.Bindings) (survives : pair ∈ (published.segmentedCheckpointView before.wal).directory.crashImages)
    (retry : LockedFileState FileImage)
    (failures : BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
      ⟨(CheckpointPowerCut.physical before published).crash pair (some before.wal.active.bytes) [],
        before.owners.set (directory.file .lock) none⟩ retry)
    (observes : ∀ layout : CanonicalKeeperLayout retry.image before.history,
      layout.keeper = before.wal.active → layout.tail = ByteArray.empty →
      layout.sealed ++ [layout.keeper] = (published.segmentedCheckpointView before.wal).readDescriptors layout.range.watermark →
      Nonempty (MarkedRetryChunkReports files directory layout published)) :
    ∃ (layout : CanonicalKeeperLayout retry.image before.history)
      (observed : MarkedRetryChunkReports files directory layout published) (after : SegmentedWriterState),
      CheckpointChunkWriter directory before published observed after ∧
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log observed.slot.description after ∧
      after.target.pair = pair ∧
      ((after.installed.generation = before.installed.generation ∧ pair.manifest = before.wal.directory.active.manifest) ∨
        (after.installed.generation = SegmentedCheckpointReport.generation before ∧ pair.manifest = some cut.checkpoint.manifest)) := by
  have beforeReady := (trace.preservesRetained ready).1
  obtain ⟨_, layout, observed, _, _, _, _, _, _, _, _, _, _, _, selected, _, _, _, _, generation,
    _, _, _, _, _, _, _, after, installed, _, installedPayload⟩ :=
    cut.reopensFromChunks beforeReady published projected pair survives retry failures observes
  exact ⟨layout, observed, after, installed,
    .checkpointPowerLossObserved trace cut projected survives failures selected installed,
    (congrArg Target.pair installed.target).trans selected, installedPayload.symm ▸ generation⟩

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

/-- Extend the mixed trace through a batch interrupted by machine power
loss and the next healthy cached installation. The batch contributes one
uncertain submission even when none of its frames survive selection. -/
theorem SegmentedBatchDatabaseTrace.reopenAfterBatchPowerLoss
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (ready : initial.RetainedReady directory initialDescriptor)
    (cut : SegmentedBatchMarkerPowerLossReport directory before writer) (observed : cut.Valid)
    (report : cut.CachedReopenReports descriptor) :
    ∃ after, report.Installs after ∧
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.uncertainBatch cut.batch]) descriptor after := by
  obtain ⟨after, installed⟩ := report.installs observed (trace.preservesRetained ready).1
  exact ⟨after, installed, .batchPowerLoss trace cut observed report installed⟩

/-- Process exit during marker publication records one uncertain batch.
The exact final cached installation supplies the next writer in the trace. -/
theorem SegmentedBatchDatabaseTrace.reopenAfterBatchMarkerProcessExit
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (ready : initial.RetainedReady directory initialDescriptor)
    (cut : SegmentedBatchMarkerPowerLossReport directory before writer) (observed : cut.Reached)
    (report : cut.ProcessExitCachedReopenReports descriptor) :
    ∃ after, report.reopen.InstallsFromCut after ∧
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.uncertainBatch cut.batch]) descriptor after := by
  obtain ⟨after, installed⟩ := report.installs observed (trace.preservesRetained ready).1
  exact ⟨after, installed, .batchMarkerProcessExit trace cut observed report installed⟩

/-- A batch interrupted before marker publication contributes one uncertain
submission and no retained frames. The next cached open installs the old
history and supports the same remaining trace operations. -/
theorem SegmentedBatchDatabaseTrace.reopenAfterBatchAppendPowerLoss
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (ready : initial.RetainedReady directory initialDescriptor)
    (report : SegmentedBatchAppendPowerLossReport directory before descriptor) (observed : report.Valid) :
    ∃ after, report.Installs after ∧
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.uncertainBatch report.reopen.batch]) descriptor after := by
  obtain ⟨after, installed⟩ := report.installs observed (trace.preservesRetained ready).1
  exact ⟨after, installed, .batchAppendPowerLoss trace report observed installed⟩

/-- Process exit before marker publication records an uncertain batch and
installs the old history from the live WAL and observed lock transitions. -/
theorem SegmentedBatchDatabaseTrace.reopenAfterBatchAppendProcessExit
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (ready : initial.RetainedReady directory initialDescriptor)
    (report : SegmentedBatchAppendProcessExitReport directory before writer descriptor)
    (observed : report.reopen.Valid) :
    ∃ after, report.reopen.Installs after ∧
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.uncertainBatch report.reopen.batch]) descriptor after := by
  obtain ⟨after, installed⟩ := report.installs observed (trace.preservesRetained ready).1
  exact ⟨after, installed, .batchAppendProcessExit trace report observed installed⟩

/-- Reads through active snapshot pins in the current session agree with
replay of the retained history, including after an uncertain batch. -/
theorem SegmentedBatchDatabaseTrace.pinnedReads
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log descriptor last)
    (ready : initial.RetainedReady directory initialDescriptor) :
    ∃ reference : SnapshotTable UInt64, SnapshotWalReplay .empty last.history reference ∧
      ∀ pin ∈ last.installed.table.pins.active,
        (∀ key, last.installed.table.lookup pin.handle key = some (reference.table.lookup key pin.sequence)) ∧
        ∀ start stop, last.installed.table.range pin.handle start stop =
          some (reference.table.range start stop pin.sequence) :=
  (trace.preservesRetained ready).1.pinnedReads

/-- A supported snapshot can be acquired against the installed table and
reads the corresponding version of the retained history. -/
theorem SegmentedBatchDatabaseTrace.acquireReads
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log descriptor last)
    (ready : initial.RetainedReady directory initialDescriptor) {snapshot : UInt64}
    (retained : last.installed.table.pins.floor ≤ snapshot) (committed : snapshot ≤ last.installed.table.committed) :
    ∃ reference : SnapshotTable UInt64, SnapshotWalReplay .empty last.history reference ∧
      ∃ pin pinned, last.installed.table.acquireAt snapshot = some (pin, pinned) ∧
        (∀ key, pinned.lookup pin.handle key = some (reference.table.lookup key snapshot)) ∧
        ∀ start stop, pinned.range pin.handle start stop = some (reference.table.range start stop snapshot) :=
  (trace.preservesRetained ready).1.acquireReads retained committed

/-- From the installed empty writer, one abstract replay explains the retained
history and every supported snapshot. Each acknowledged batch is retained in
full, and each uncertain batch contributes all its frames or none. -/
theorem SegmentedBatchDatabaseTrace.keyValueRefinement
    {directory initialDescriptor allowCollection log descriptor last}
    {first : LockedFileState WalSegmentRotation.State} (bootstrap : BootstrapReady first.image)
    (held : first.owners.Owns directory initialDescriptor)
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log descriptor last) :
    ∃ reference : SnapshotTable UInt64,
      SnapshotWalReplay .empty last.history reference ∧
      DatabaseBatchRetention log last.history ∧
      log.flatMap DatabaseSubmissions.acknowledged <+ last.history ∧
      last.history <+ log.flatMap DatabaseSubmissions.submitted ∧
      ∀ snapshot, last.installed.table.pins.floor ≤ snapshot → snapshot ≤ last.installed.table.committed →
        ∃ pin pinned, last.installed.table.acquireAt snapshot = some (pin, pinned) ∧
          (∀ key, pinned.lookup pin.handle key = some (reference.table.lookup key snapshot)) ∧
          ∀ start stop, pinned.range pin.handle start stop = some (reference.table.range start stop snapshot) := by
  obtain ⟨ready, retained, history, retention⟩ := trace.preservesRetained (bootstrap.writerReady held).toRetained
  change last.history = [] ++ retained at history
  simp only [List.nil_append] at history
  subst retained
  obtain ⟨acknowledged, submitted⟩ := retention.orderedSubmissions
  obtain ⟨reference, replayed⟩ := SnapshotWalReplay.fromEmpty last.history ready.resumed.ordered
  refine ⟨reference, replayed, retention, acknowledged, submitted, ?_⟩
  intro snapshot floor committed
  obtain ⟨other, sameReplay, pin, pinned, acquired, lookup, range⟩ := ready.acquireReads floor committed
  have same := replayed.deterministic sameReplay
  cases same
  exact ⟨pin, pinned, acquired, lookup, range⟩

/-- The final writer uses the same snapshot guard as the adapter. The
observed session comparison determines whether the newly acquired pin
can read its exact abstract snapshot through that guard. -/
theorem SegmentedBatchDatabaseTrace.guardedKeyValueRefinement
    {directory initialDescriptor allowCollection log descriptor last}
    {first : LockedFileState WalSegmentRotation.State} (bootstrap : BootstrapReady first.image)
    (held : first.owners.Owns directory initialDescriptor)
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log descriptor last) :
    ∃ reference : SnapshotTable UInt64,
      SnapshotWalReplay .empty last.history reference ∧
      DatabaseBatchRetention log last.history ∧
      log.flatMap DatabaseSubmissions.acknowledged <+ last.history ∧
      last.history <+ log.flatMap DatabaseSubmissions.submitted ∧
      ∀ snapshot, last.installed.table.pins.floor ≤ snapshot → snapshot ≤ last.installed.table.committed →
        ∃ pin pinned, last.installed.table.acquireAt snapshot = some (pin, pinned) ∧
          ∀ (sameSession : Bool) (issuer current : Nat), sameSession = decide (issuer = current) →
            (∀ key, readWithHandle (.ready pinned) sameSession (fun table => table.lookup pin.handle key) =
              .ok (if issuer = current then some (reference.table.lookup key snapshot) else none)) ∧
            ∀ start stop, readWithHandle (.ready pinned) sameSession (fun table => table.range pin.handle start stop) =
              .ok (if issuer = current then some (reference.table.range start stop snapshot) else none) := by
  obtain ⟨reference, replayed, retained, acknowledged, submitted, reads⟩ :=
    trace.keyValueRefinement bootstrap held
  refine ⟨reference, replayed, retained, acknowledged, submitted, ?_⟩
  intro snapshot floor committed
  obtain ⟨pin, pinned, acquired, lookup, range⟩ := reads snapshot floor committed
  refine ⟨pin, pinned, acquired, ?_⟩
  intro sameSession issuer current compared
  by_cases localToken : issuer = current
  · rw [compared.trans (decide_eq_true localToken)]
    simp only [localToken, ↓reduceIte]
    exact ⟨fun key => congrArg Except.ok (lookup key), fun start stop => congrArg Except.ok (range start stop)⟩
  · simp only [localToken, ↓reduceIte]
    exact ⟨fun key => readWithHandle_foreign pinned _ compared localToken,
      fun start stop => readWithHandle_foreign pinned _ compared localToken⟩

/-- Reacquiring an earlier pin's sequence preserves its reads while the
final writer still retains that sequence. -/
theorem SegmentedBatchDatabaseTrace.reacquireReadsStable
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log descriptor last)
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
