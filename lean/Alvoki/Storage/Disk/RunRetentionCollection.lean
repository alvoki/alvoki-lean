import Alvoki.Storage.Disk.RunRetentionCheckpoint
import Alvoki.Storage.Disk.SegmentedBatchDatabaseTrace
import Alvoki.Storage.Disk.IntegrityRunCollectionSpace

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair
open Compaction.Model (retentionRowBound)

private theorem namedCurrentRunBytes {runs : RunFiles} {generation : UInt64} {files : List ByteArray}
    (atIndex : ∀ index (within : index < files.length), runs generation index = some files[index]) :
    runs.namedRunTotal ByteArray.size ((List.range files.length).map fun index => (generation, index)) =
      (files.map ByteArray.size).sum := by
  unfold RunFiles.namedRunTotal
  congr 1
  apply List.ext_getElem?
  intro index
  by_cases within : index < files.length
  · simp [List.getElem?_map, List.getElem?_range within, atIndex index within, List.getElem?_eq_getElem within]
  · have absent : (List.range files.length)[index]? = none :=
      List.getElem?_eq_none_iff.mpr (by simpa only [List.length_range] using Nat.le_of_not_gt within)
    rw [List.getElem?_map, List.getElem?_map, absent, List.getElem?_map,
      List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt within)]
    rfl

/-- After an uninterrupted retention pass over the current runs and a successful
checkpoint, the native collector can durably remove every older unheld name.
The settled namespace still selects the exact published run bytes, with the
same aggregate bound. Known durable current, held, and newer bindings survive.
The inventory and successful native effects are supplied by the caller. -/
theorem SegmentedCheckpointReport.Installs.collectRetainedRunPayload {directory descriptor}
    {before published : SegmentedWriterState} {table : PackedTable}
    (ready : before.RetainedReady directory descriptor)
    (pass : PackedTable.RunRetentionSteps 0 before.installed.table.runs.length before.installed.table table)
    (empty : table.memoryIsEmpty = true)
    {attempt : SegmentedCheckpointReport directory (before.withTable table)}
    (observed : attempt.Valid) (installed : attempt.Installs published)
    {runs : RunUnlinkImage} (reports : SegmentedRunCollectionReports directory published runs)
    (complete : ∀ generation index bytes, runs.visible generation index = some bytes →
      generation < published.installed.generation → generation ∉ reports.held →
      renderRunFileName generation index ∈ reports.inventory.names ∧
        reports.inventory.kindAt (directory.file (.run generation index)) = .ok .file)
    (healthy : RunUnlinkScheduleHealthy runs (RunCollection.steps reports.selected) reports.perform) :
    let collected := runs.finishPass reports.selected
    let after := published.afterRunCollection collected.guaranteed
    let files := table.runs.map (·.run.bytes)
    reports.run = .ok () collected ∧
    reports.reached = collected ∧
    collected.crashImages = [collected.visible] ∧
    after.RetainedReady directory descriptor ∧
    SelectedIntegrityCheckpoint collected.visible (some attempt.manifest) published.checkpoint ∧
    (∀ generation index, generation < published.installed.generation → generation ∉ reports.held →
      collected.DurablyAbsent (generation, index)) ∧
    (∀ generation index bytes, published.installed.generation ≤ generation ∨ generation ∈ reports.held →
      runs.guaranteed generation index = some bytes → collected.guaranteed generation index = some bytes) ∧
    (∀ index (within : index < files.length),
      collected.visible published.installed.generation index = some files[index]) ∧
    collected.visible.namedRunTotal ByteArray.size
      ((List.range files.length).map fun index => (published.installed.generation, index)) =
      (files.map ByteArray.size).sum ∧
    (files.map ByteArray.size).sum ≤
      16 * before.installed.table.runs.length +
        32 * (before.installed.table.runs.map (fun run =>
          retentionRowBound run.history.rows before.installed.table.pins.floor)).sum := by
  intro collected after files
  have retained : SegmentedWriterTrace directory descriptor before [] 0 (before.withTable table) :=
    SegmentedWriterTrace.empty.retainRuns pass
  have publishedReady := (installed.preservesRetained observed (retained.preservesRetained ready).1).1
  obtain ⟨settled, written, payloadBound⟩ := installed.retainedRunPayload pass empty observed
  have generation : published.installed.generation = SegmentedCheckpointReport.generation before :=
    congrArg Installed.generation installed.installed
  have eligible : ∀ address ∈ reports.selected,
      address.1 < published.installed.generation ∧ address.1 ∉ reports.held := by
    rintro ⟨generation, index⟩ selected
    obtain ⟨_, older, unheld, _⟩ := (reports.selected_eligible publishedReady).mp selected
    exact ⟨older, unheld⟩
  obtain ⟨returned, _, crash, guaranteed, _, absent, kept, nextReady, checkpoint⟩ :=
    reports.completeAfterRetries publishedReady (.start runs) eligible (fun _ selected => selected) complete healthy
  have manifest : published.target.pair.manifest = some attempt.manifest := by
    have projection := congrArg Publication.Image.active publishedReady.manifestFiles
    change published.published.manifest.active = published.files.directory.active.manifest at projection
    rw [publishedReady.directoryFiles, settled] at projection
    exact (congrArg DirectoryPublication.Bindings.manifest publishedReady.walPair).symm.trans projection.symm
  have exactFiles (index : Nat) (within : index < files.length) :
      collected.visible published.installed.generation index = some files[index] := by
    have stored : published.published.durable published.installed.generation index = some files[index] := by
      rw [generation, written index]
      exact List.getElem?_eq_getElem within
    rw [← guaranteed, kept _ _ _ (.inl (UInt64.le_refl _)) (reports.known index (files[index]) stored)]
  exact ⟨returned, by rw [SegmentedRunCollectionReports.reached, returned], crash, nextReady, manifest ▸ checkpoint,
    absent, kept, exactFiles, namedCurrentRunBytes exactFiles, payloadBound⟩

/-- The admitted open after a healthy collection starts from the namespace
left by that very call. It restores the rewritten runs byte for byte and
reacquires any previously active snapshot with its original read results. -/
theorem SegmentedBatchDatabaseTrace.reopenAfterRetainedRunCollection {files : Type}
    {directory initialDescriptor initial allowCollection log writer input before published}
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection log writer before)
    (initialReady : initial.RetainedReady directory initialDescriptor) (enabled : allowCollection = true)
    {table : PackedTable}
    (pass : PackedTable.RunRetentionSteps 0 before.installed.table.runs.length before.installed.table table)
    (empty : table.memoryIsEmpty = true)
    {attempt : SegmentedCheckpointReport directory (before.withTable table)}
    (observed : attempt.Valid) (installed : attempt.Installs published)
    {runs : RunUnlinkImage} (reports : SegmentedRunCollectionReports directory published runs)
    (complete : ∀ generation index bytes, runs.visible generation index = some bytes →
      generation < published.installed.generation → generation ∉ reports.held →
      renderRunFileName generation index ∈ reports.inventory.names ∧
        reports.inventory.kindAt (directory.file (.run generation index)) = .ok .file)
    (healthy : RunUnlinkScheduleHealthy runs (RunCollection.steps reports.selected) reports.perform)
    (closed : CleanUnlockReports directory writer)
    (reads : closed.ReopenObservations files input (published.afterRunCollection reports.reached.guaranteed)) :
    let collected := published.afterRunCollection reports.reached.guaranteed
    reports.run = .ok () (runs.finishPass reports.selected) ∧
    ∃ (layout : CanonicalKeeperLayout (SegmentedCleanReopenReport.released directory collected).image collected.history)
      (reopening : MarkedRetryChunkReports files directory layout collected.published)
      (admission : OpenAdmissionReports input directory reopening.slot) (after : SegmentedWriterState)
      (session : SegmentedSession) (final : LockedFileState FileImage),
      reopening.runWithAdmission admission = .ok session final ∧
      session.phase = .ready after.installed ∧ after.files = final.image ∧ after.owners = final.owners ∧
      SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
        (log ++ [.ordinary [⟨[], none⟩]]) reopening.slot.description after ∧
      after.published.durable = (runs.finishPass reports.selected).visible ∧
      after.installed.table.runs = table.runs ∧ after.history = before.history ∧
      after.installed.generation = SegmentedCheckpointReport.generation before ∧
      ∀ oldPin ∈ before.installed.table.pins.active,
        ∃ newPin pinned, after.installed.table.acquireAt oldPin.sequence = some (newPin, pinned) ∧
          newPin.sequence = oldPin.sequence ∧
          (∀ key, pinned.lookup newPin.handle key = before.installed.table.lookup oldPin.handle key) ∧
          ∀ start stop, pinned.range newPin.handle start stop = before.installed.table.range oldPin.handle start stop := by
  intro collected
  have ready := (trace.preservesRetained initialReady).1
  obtain ⟨ran, reached, _, _, _, _, _, _, _, _⟩ :=
    installed.collectRetainedRunPayload ready pass empty observed reports complete healthy
  have retained : SegmentedWriterTrace directory writer before [] 0 (before.withTable table) :=
    SegmentedWriterTrace.empty.retainRuns pass
  have publishedTrace := trace.ordinary (SegmentedDatabaseTrace.writes .start
    (.checkpoint retained attempt observed installed))
  have collectedTrace : SegmentedBatchDatabaseTrace directory initialDescriptor initial allowCollection
      (log ++ [.ordinary [⟨[], none⟩]]) writer collected :=
    .collectRuns enabled publishedTrace reports
  obtain ⟨layout, reopening, admission, after, endpoint, continued⟩ :=
    collectedTrace.reopenAfterCleanCloseAdmission initialReady closed reads
  obtain ⟨session, final, opened, _, _, phase, _, finalFiles, owners⟩ := endpoint.reopenEffect
  obtain ⟨base, selected, sameData, baseClock⟩ := installed.restored
  have replayed := endpoint.replay
  change recoverSelected (published.checkpoint.getD (.empty, 0)).1 (WAL.encode published.history) =
    .ok after.installed.table at replayed
  rw [selected] at replayed
  have fullyCovered : recoverSelected base (WAL.encode published.history) = .ok base := by
    have publishedReady := (installed.preservesRetained observed (retained.preservesRetained ready).1).1
    simpa only [List.append_nil, replay, List.foldlM_nil, Pure.pure, Except.pure] using
      recoverSelected_encoded base published.history [] (by simpa using publishedReady.resumed.ordered) baseClock.symm
  have restored : after.installed.table = base := Except.ok.inj (replayed.symm.trans fullyCovered)
  have checkpointTable : attempt.table = table := by
    have flushed := observed.flushed
    change (flushForCheckpoint table id : Except String PackedTable) = .ok attempt.table at flushed
    simpa [flushForCheckpoint, empty, Pure.pure, Except.pure] using flushed.symm
  have exactState : after.published.durable = (runs.finishPass reports.selected).visible := by
    rw [endpoint.writer.durable]
    change reports.reached.guaranteed = _
    rw [reached]
    exact congrArg Image.durable (RunUnlinkImage.project_settled
      (runs.finishPass reports.selected).visible published.published.manifest)
  have history : after.history = before.history := endpoint.writer.history.trans installed.history
  have floor : after.installed.table.pins.floor = before.installed.table.pins.floor := by
    rw [restored, sameData.floor, checkpointTable, pass.preservesReads.2.2.1]
  refine ⟨ran, layout, reopening, admission, after, session, final, opened, phase, finalFiles, owners,
    continued, exactState, restored ▸ sameData.runs.trans (congrArg PackedTable.runs checkpointTable),
    history, endpoint.generation.trans (congrArg Installed.generation installed.installed), ?_⟩
  intro oldPin active
  exact ready.reacquireReadsStable endpoint.writer.retained (suffix := []) (by simpa using history) active
    (floor.symm ▸ before.installed.table.pins.safe oldPin active)

end Alvoki.Storage.DiskSession
