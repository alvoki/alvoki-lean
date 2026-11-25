import Alvoki.Storage.Disk.NativeExecutionClose
import Alvoki.Storage.Disk.NativeReadyCheckpoint
import Alvoki.Storage.Disk.NativeRunMaintenance

namespace Alvoki.Storage.DiskSession

open System Manifest CheckpointPublication WalSegmentRepair
open Compaction.Model (retentionRowBound)

variable {state : NativeReadyState} {image : Type}
  {attempt : SegmentedCheckpointReport state.session.directory state.writer}
  {reports : CheckpointCompletionReports (CensusDirectoryCache × image) attempt}

namespace NativeReadyCheckpoint

/-- The chosen generation/index is observed at its actual run write and
sync. Each later run pair and publication callback preserves that name. -/
structure RunBinding (checkpoint : NativeReadyCheckpoint state reports) (index : Nat) where
  wroteAndSynced : ∀ (run : Compaction.CheckedRun)
    (file : CompletedCheckpointTemporaryFile checkpoint.descriptors checkpoint.primitives.cached
      checkpoint.primitives.cached.writeRun (state.session.directory.file (.run attempt.prepared.generation index))
      run.run.bytes (reports.observed.atRun index).2 (reports.observed.atRun (index + 1)).2),
    let path := state.session.directory.file (.run attempt.prepared.generation index)
    checkpoint.bindings file.flushed path = some (file.handle.1.inode file.handle.2.1.description) ∧
    checkpoint.bindings (reports.observed.atRun (index + 1)).2 path = checkpoint.bindings file.flushed path
  laterPairs : ∀ later, index < later → later < attempt.table.runs.length →
    let path := state.session.directory.file (.run attempt.prepared.generation index)
    checkpoint.bindings (reports.observed.atRun (later + 1)).2 path =
      checkpoint.bindings (reports.observed.atRun later).2 path
  runDirectory :
    let path := state.session.directory.file (.run attempt.prepared.generation index)
    checkpoint.bindings reports.observed.runsSettled.2 path =
      checkpoint.bindings (reports.observed.atRun attempt.table.runs.length).2 path
  stageManifest :
    let path := state.session.directory.file (.run attempt.prepared.generation index)
    checkpoint.bindings reports.observed.staged.2 path = checkpoint.bindings reports.observed.runsSettled.2 path
  syncManifest :
    let path := state.session.directory.file (.run attempt.prepared.generation index)
    checkpoint.bindings reports.observed.stagedSynced.2 path = checkpoint.bindings reports.observed.staged.2 path
  renameManifest :
    let path := state.session.directory.file (.run attempt.prepared.generation index)
    checkpoint.bindings reports.observed.renamed.2 path = checkpoint.bindings reports.observed.stagedSynced.2 path
  manifestDirectory :
    let path := state.session.directory.file (.run attempt.prepared.generation index)
    checkpoint.bindings reports.observed.completed.2 path = checkpoint.bindings reports.observed.renamed.2 path

/-- The same temporary handle wrote and fsynced the selected bytes.
Its descriptor is released. Its canonical binding persists through the
rest of the actual successful checkpoint schedule. -/
theorem RunBinding.completes {checkpoint : NativeReadyCheckpoint state reports} {index : Nat}
    (binding : checkpoint.RunBinding index) {run : Compaction.CheckedRun}
    (selected : attempt.table.runs[index]? = some run) :
    let path := state.session.directory.file (.run attempt.prepared.generation index)
    ∃ file : CompletedCheckpointTemporaryFile checkpoint.descriptors checkpoint.primitives.cached
      checkpoint.primitives.cached.writeRun path run.run.bytes
      (reports.observed.atRun index).2 (reports.observed.atRun (index + 1)).2,
      checkpoint.bindings reports.observed.completed.2 path = some (file.handle.1.inode file.handle.2.1.description) ∧
      (checkpoint.descriptors (reports.observed.atRun (index + 1)).2).references file.handle.2.1.description = [] := by
  intro path
  have within := (List.getElem?_eq_some_iff.mp selected).1
  obtain ⟨actual, atIndex, ⟨file⟩⟩ := checkpoint.runLifetime index within
  rw [List.getElem?_toArray, selected] at atIndex
  obtain rfl := Option.some.inj atIndex
  have later (last : Nat) (first : index + 1 ≤ last) (bounded : last ≤ attempt.table.runs.length) :
      checkpoint.bindings (reports.observed.atRun last).2 path =
        checkpoint.bindings (reports.observed.atRun (index + 1)).2 path := by
    induction last with
    | zero => omega
    | succ last ih =>
      by_cases same : index + 1 = last + 1
      · rw [same]
      · exact (binding.laterPairs last (by omega) (by omega)).trans (ih (by omega) (by omega))
  obtain ⟨atFlush, atClose⟩ := binding.wroteAndSynced run file
  have afterRuns := later _ (by omega) (Nat.le_refl _)
  exact ⟨file, binding.manifestDirectory.trans (binding.renameManifest.trans (binding.syncManifest.trans
    (binding.stageManifest.trans (binding.runDirectory.trans (afterRuns.trans (atClose.trans atFlush)))))), file.keepsCensus.2.2⟩

end NativeReadyCheckpoint

/-- The selected replay gives the table of the same chronological aligned
return, with its checkpoint loaded from the reached manifest. -/
private theorem NativeCloseAlignedReads.replayTable
    {files : NativeCloseFiles state} {input : FilePath} {inventory : DescriptorInventory}
    (plan : ClosedReadyReopenLayout state.writer state.releasedFiles)
    {selected : SelectedIntegrityCheckpoint state.writer.published.durable
      state.releasedFiles.image.directory.active.manifest state.writer.checkpoint}
    (seen : NativeCloseAlignedReads files input inventory plan.layout selected)
    (ready : state.writer.RetainedReady state.session.directory state.session.descriptor) :
    ∃ (session : SegmentedSession) (final : CensusOpenState) (opened : Reopened),
      seen.run = .ok session final ∧ session.phase = .ready opened.installed ∧
      recoverSelected (state.writer.checkpoint.getD (.empty, 0)).1 (WAL.encode state.writer.history) = .ok opened.table := by
  let opening := seen.opening
  let finish : CapturedKeeperFinish opening.callbacks opening.reads state.releasedVacant selected := .aligned opening.finish
  have manifest := congrArg DirectoryPublication.Bindings.manifest
    (plan.prepared.pair.trans (congrArg Target.pair plan.target))
  have accepted := manifest.symm ▸ ready.resumed.accepted
  obtain ⟨session, final, returned, _, _, _, installed⟩ := finish.installsFromCensus seen.chronology opening.markerFound
    plan.prepared (opening.reads.walReads.selectedAfterWatermark plan.offsets plan.descriptors)
    accepted ready.resumed.ordered
  obtain ⟨reopened, loaded, _, installedSession, installedFinal, actual, _, _, phase, _, _, _, _, _, _, _, _, _,
    _, loadedSelected, replayed, _⟩ := installed
  obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj actual
  have checkpoint := loadedSelected.uniqueResult selected
  exact ⟨session, (opening.finish.census, final), reopened, returned, phase, checkpoint ▸ replayed⟩

private theorem preservesRunAtFlush {before checkpoint : PackedTable} {index : Nat} {run : Compaction.CheckedRun}
    (flushed : (flushForCheckpoint before id : Except String PackedTable) = .ok checkpoint)
    (selected : before.runs[index]? = some run) :
    checkpoint.runs[index]? = some run := by
  unfold flushForCheckpoint at flushed
  split at flushed
  · exact Except.ok.inj flushed ▸ selected
  · change before.flush = .ok checkpoint at flushed
    obtain ⟨_, _, _, _, runs, _⟩ := PackedTable.flush_spec flushed
    rw [runs]
    exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp selected).1).trans selected

variable {history : List WAL.Write} {log : List DatabaseSubmissions}

/-- The rewrite, checkpoint return and reopen are reports from consecutive
reached states. The selected run in the returned table comes from the
same inode that was synced for the new generation. -/
structure NativeRetainedRunReopen (current : NativeReadPosition history log) (index : Nat)
    {rewritten : PackedTable} {image : Type}
    {attempt : SegmentedCheckpointReport current.state.session.directory (current.state.withTable rewritten).writer}
    {reports : CheckpointCompletionReports (CensusDirectoryCache × image) attempt}
    (checkpoint : NativeReadyCheckpoint (current.state.withTable rewritten) reports)
    (input : FilePath) (next : NativeReadPosition history log) : Prop where
  replay : InstalledClientReplay log current.reads history next.state.writer.installed next.state.session
  reads : next.reads = current.reads
  rewrite : ∃ rewrittenPosition, NativeRunMaintenanceStep current (.retainRunVersions index) true rewrittenPosition ∧
    rewrittenPosition.state = current.state.withTable rewritten
  generation : next.state.writer.installed.generation = SegmentedCheckpointReport.generation current.state.writer
  table : next.state.writer.installed.table.SameData attempt.table
  floor : next.state.writer.installed.table.pins.floor = current.state.writer.installed.table.pins.floor
  reacquires : ∀ oldPin ∈ current.state.writer.installed.table.pins.active,
    ∃ newPin pinned, next.state.writer.installed.table.acquireAt oldPin.sequence = some (newPin, pinned) ∧
      newPin.sequence = oldPin.sequence ∧
      (∀ key, pinned.lookup newPin.handle key = current.state.writer.installed.table.lookup oldPin.handle key) ∧
      ∀ start stop, pinned.range newPin.handle start stop = current.state.writer.installed.table.range oldPin.handle start stop
  exactRun : ∃ (source output : Compaction.CheckedRun) (checkpointed : NativeReadPosition history log)
    (close : NativeCloseReopenObservation checkpointed.state input),
    current.state.writer.installed.table.runs[index]? = some source ∧
    output.history = source.history.retain current.state.writer.installed.table.pins.floor ∧
    output.run.bytes.size ≤ 16 + 32 * retentionRowBound source.history.rows current.state.writer.installed.table.pins.floor ∧
    next.state.writer.installed.table.runs[index]? = some output ∧
    next.state.writer.published.durable (SegmentedCheckpointReport.generation current.state.writer) index =
      some output.run.bytes ∧
    close.close.report.result = .ok () ∧ NativeCloseReopenStep checkpointed close next ∧
    ∃ (_completed : checkpoint.Completed checkpointed.state.writer)
      (file : CompletedCheckpointTemporaryFile checkpoint.descriptors checkpoint.primitives.cached
        checkpoint.primitives.cached.writeRun (current.state.session.directory.file (.run attempt.prepared.generation index))
        output.run.bytes (reports.observed.atRun index).2 (reports.observed.atRun (index + 1)).2),
      checkpointed.state = checkpoint.next checkpointed.state.writer ∧
      let path := current.state.session.directory.file (.run attempt.prepared.generation index)
      let inode := file.handle.1.inode file.handle.2.1.description
      checkpoint.bindings reports.observed.completed.2 path = some inode ∧
      (reports.runs reports.observed.completed).guaranteed attempt.prepared.generation index = some output.run.bytes ∧
      (checkpoint.descriptors (reports.observed.atRun (index + 1)).2).references file.handle.2.1.description = [] ∧
      close.files.names path = some inode ∧ close.files.bytes inode = some output.run.bytes ∧
      ∃ (plan : ClosedReadyReopenLayout checkpointed.state.writer checkpointed.state.releasedFiles)
        (selected : SelectedIntegrityCheckpoint checkpointed.state.writer.published.durable
          checkpointed.state.releasedFiles.image.directory.active.manifest checkpointed.state.writer.checkpoint)
        (opened : NativeCloseAlignedReads close.files input close.inventory plan.layout selected)
        (read : opened.opening.reads.reads.ObservesFile path output.run.bytes),
        opened.run = next.opened ∧ read.object = inode

/-- A successful native retention rewrite publishes its exact output at
the same index, even when checkpoint preparation appends a flushed run.
The healthy close and aligned reopen read that inode and install the
retained table. Supported pins reacquire their prior point and range reads. -/
theorem NativeReadPosition.retainsRunCheckpointAndReopens
    (current : NativeReadPosition history log) {index : Nat} {rewritten : PackedTable}
    (retained : current.state.writer.installed.table.retainRunVersions index = some rewritten)
    {image : Type}
    {attempt : SegmentedCheckpointReport current.state.session.directory (current.state.withTable rewritten).writer}
    {reports : CheckpointCompletionReports (CensusDirectoryCache × image) attempt}
    (checkpoint : NativeReadyCheckpoint (current.state.withTable rewritten) reports)
    (binding : checkpoint.RunBinding index) (input : FilePath)
    (observe : ∀ writer, checkpoint.Completed writer →
      ∃ close : NativeCloseReopenObservation (checkpoint.next writer) input,
        close.close.report.result = .ok () ∧
        let path := current.state.session.directory.file (.run attempt.prepared.generation index)
        close.files.names path = checkpoint.bindings reports.observed.completed.2 path) :
    ∃ next, NativeRetainedRunReopen current index checkpoint input next := by
  obtain ⟨_, rewrittenPosition, rewrite⟩ := current.rewritesRun (.retainRunVersions index)
  have reached := rewrite.reached
  change (match current.state.writer.installed.table.retainRunVersions index with
    | none => _ ∧ _
    | some table => _ ∧ rewrittenPosition.state = current.state.withTable table) at reached
  rw [retained] at reached
  obtain ⟨rfl, rewrittenState⟩ := reached
  obtain ⟨priorValid, historyEq, pending⟩ := current.readPrefix.refines
  have rewriteValid := rewrittenState ▸ rewrittenPosition.readPrefix.refines.1
  obtain ⟨writer, completed, published⟩ := checkpoint.completesWithPublication rewriteValid
  let checkpointed : NativeReadPosition history log :=
    let state := checkpoint.next writer
    ⟨.ok state.session (state.census, state.files), state, state, current.reads,
      .installed rfl completed.valid (completed.sameHistory.trans historyEq) pending current.readPrefix.readsBounded⟩
  obtain ⟨close, closeOK, sameName⟩ := observe writer completed
  obtain ⟨next, reopened⟩ := checkpointed.closesAndReopens close
  obtain ⟨_, _, rewritePins, older, source, output, newer, length, original, updated, wroteRetained, ownHistory⟩ :=
    PackedTable.retainRunVersions_spec retained
  have atIndex (run : Compaction.CheckedRun) : (older ++ run :: newer)[index]? = some run := by
    rw [List.getElem?_append_right (Nat.le_of_eq length), ← length, Nat.sub_self]
    rfl
  have outputAt : rewritten.runs[index]? = some output := updated.symm ▸ atIndex output
  have publishedAt : attempt.table.runs[index]? = some output :=
    preservesRunAtFlush reports.preflight.preparedFacts.1 outputAt
  obtain ⟨file, physical, released⟩ := binding.completes publishedAt
  obtain ⟨base, checkpointBase, data, baseClock⟩ := published.restored
  have reopenedValid := next.readPrefix.refines.1
  have sameHistory : next.state.writer.history = current.state.writer.history :=
    next.readPrefix.refines.2.1.trans historyEq.symm
  have foundGeneration : next.state.writer.installed.generation = SegmentedCheckpointReport.generation current.state.writer := by
    rw [reopenedValid.retained.resumed.generation, reopened.frame.checkpoint]
    change (writer.checkpoint.getD (.empty, 0)).2 = _
    rw [checkpointBase]
    rfl
  obtain ⟨plan, selected, opened, actual, returned, _, _, _, _, _, reads⟩ := reopened.exactOpen
  obtain ⟨session, final, recovered, ran, phase, replayed⟩ := opened.replayTable plan completed.valid.retained
  have sameSession := (EStateM.Result.ok.inj (ran.symm.trans actual)).1
  have loaded := Phase.ready.inj (reopenedValid.phase.symm.trans (sameSession ▸ phase))
  have noWalReplay : recoverSelected base (WAL.encode writer.history) = .ok base := by
    have ordered : WAL.OrdinalsFrom 1 writer.history := completed.valid.retained.resumed.ordered
    simpa only [List.append_nil, replay, List.foldlM_nil, Pure.pure, Except.pure] using
      recoverSelected_encoded base writer.history [] (by simpa using ordered) baseClock.symm
  change recoverSelected (writer.checkpoint.getD (.empty, 0)).1 (WAL.encode writer.history) = _ at replayed
  rw [checkpointBase] at replayed
  have exactTable : next.state.writer.installed.table = base :=
    (congrArg Installed.table loaded).trans (Except.ok.inj (replayed.symm.trans noWalReplay))
  have loadedOutput : next.state.writer.installed.table.runs[index]? = some output := by
    rw [exactTable, data.runs]
    exact publishedAt
  have durableOutput : writer.published.durable (SegmentedCheckpointReport.generation current.state.writer) index =
      some output.run.bytes := by
    change writer.published.durable (SegmentedCheckpointReport.generation (current.state.withTable rewritten).writer)
      index = _
    rw [published.runs index]
    change (attempt.table.runs.map (·.run.bytes))[index]? = _
    rw [List.getElem?_map, publishedAt]
    rfl
  have completedBytes : (reports.runs reports.observed.completed).guaranteed attempt.prepared.generation index =
      some output.run.bytes := by
    have written := completed.runs index (List.getElem?_eq_some_iff.mp publishedAt).1
    rw [published.installed] at written
    exact written.trans ((published.runs index).symm.trans durableOutput)
  have manifest : writer.target.pair.manifest = some attempt.manifest := by
    have named := completed.manifestBinding
    rw [completed.files] at named
    change writer.files.directory.active.manifest = _ at named
    have pair : writer.files.directory.active = writer.target.pair := completed.valid.retained.resumed.ready.selected
    exact (congrArg DirectoryPublication.Bindings.manifest pair).symm.trans named
  have declared : index < (IntegrityCheckpoint.fromRuns
      (checkpointHeader attempt.table (SegmentedCheckpointReport.generation current.state.writer)) attempt.plan.files).header.runCount.toNat := by
    have count : attempt.table.runs.length.toUInt64.toNat = attempt.table.runs.length :=
      UInt64.toNat_ofNat_of_lt' reports.preflight.preparedFacts.2.2.1
    change index < attempt.table.runs.length.toUInt64.toNat
    rw [count]
    exact (List.getElem?_eq_some_iff.mp publishedAt).1
  obtain ⟨raw, rawBound, rawBytes⟩ := reads.runs attempt.manifest _ manifest published.decodedManifest
    index declared output.run.bytes durableOutput
  let inode := file.handle.1.inode file.handle.2.1.description
  have object : raw.object = inode := Option.some.inj (rawBound.symm.trans (sameName.trans physical))
  have pins : writer.installed.table.pins = current.state.writer.installed.table.pins := completed.pins.trans rewritePins
  have floor : next.state.writer.installed.table.pins.floor = current.state.writer.installed.table.pins.floor := by
    rw [published.installed] at pins
    rw [exactTable, data.floor]
    exact congrArg Sequential.SnapshotPins.floor pins
  have readHistory : next.reads = current.reads := reopened.reads
  have path : next.state.session.directory = current.state.session.directory := reopened.frame.directory
  have foundDurable := (congrFun (congrFun reopened.frame.durable
    (SegmentedCheckpointReport.generation current.state.writer)) index).trans durableOutput
  have readBytes : close.files.bytes inode = some output.run.bytes := by rw [← object]; exact rawBytes
  refine ⟨next, readHistory ▸ next.readPrefix.guardedReplay, readHistory, ⟨rewrittenPosition, rewrite, rewrittenState⟩,
    foundGeneration, exactTable.symm ▸ data, floor, ?_, ?_⟩
  · intro oldPin active
    exact priorValid.retained.reacquireReadsStable (path ▸ reopenedValid.retained) (suffix := [])
      (by simpa using sameHistory) active (floor.symm ▸ current.state.writer.installed.table.pins.safe oldPin active)
  · exact ⟨source, output, checkpointed, close, original.symm ▸ atIndex source, ownHistory,
      Compaction.CheckedRun.retainVersions_byteSize_le wroteRetained, loadedOutput,
      foundDurable, closeOK, reopened, completed, file, rfl, physical, completedBytes, released,
      sameName.trans physical, readBytes, plan, selected, opened, raw, returned.symm, object⟩

end Alvoki.Storage.DiskSession
