import Alvoki.Storage.Disk.Proofs.Collection.NativeObsoleteRunCollection
import Alvoki.Storage.Disk.NativeRunMaintenanceReopen

namespace Alvoki.Storage.DiskSession

open System Manifest CheckpointPublication

variable {state : NativeReadyState} {image : Type}
  {attempt : SegmentedCheckpointReport state.session.directory state.writer}
  {reports : CheckpointCompletionReports (CensusDirectoryCache × image) attempt}

/-- The collector begins at the exact completed run image. These raw path
observations concern only generations that the caller's holds or the
current checkpoint protect. Each unlink frame uses the ordered, reached
callback and the final frame uses the actual directory barrier. -/
structure CheckpointRunCollectionReports (checkpoint : NativeReadyCheckpoint state reports)
    (writer : SegmentedWriterState) (held : List UInt64) where
  collector : NativeObsoleteRunCollection (checkpoint.next writer)
  initial : collector.initial = reports.runs reports.observed.completed
  holds : collector.reports.held = held
  atEntry : ∀ generation index, writer.installed.generation ≤ generation ∨ generation ∈ held →
    let path := state.session.directory.file (.run generation index)
    (collector.pathObject ((checkpoint.next writer).census, collector.initial) path).map
      collector.lifetime.namespaceView.modelObject =
      checkpoint.bindings reports.observed.completed.2 path
  unlink : ∀ (done : List RunAddress) target remaining before after,
    collector.reports.selected = done ++ target :: remaining →
    ((done.map RunCollection.Step.unlink).forM collector.reports.perform) collector.initial = .ok () before →
    collector.reports.perform (.unlink target) before = .ok () after →
    ∀ generation index, writer.installed.generation ≤ generation ∨ generation ∈ held →
      let path := state.session.directory.file (.run generation index)
      collector.pathObject ((checkpoint.next writer).census, after) path =
        collector.pathObject ((checkpoint.next writer).census, before) path
  barrier : ∀ generation index, writer.installed.generation ≤ generation ∨ generation ∈ held →
    let path := state.session.directory.file (.run generation index)
    collector.pathObject (collector.toNativeObsoleteRunPass.returnCensus, collector.atBarrier.syncDirectory) path =
      collector.pathObject (collector.toNativeObsoleteRunPass.issueCensus, collector.atBarrier) path

private theorem preservesUnlinkFrame {view : Type}
    (perform : RunCollection.Step RunAddress → EStateM IO.Error RunUnlinkImage Unit) (project : RunUnlinkImage → view)
    {targets : List RunAddress} {initial final : RunUnlinkImage}
    (ran : ((targets.map RunCollection.Step.unlink).forM perform) initial = .ok () final)
    (frame : ∀ (done : List RunAddress) target remaining before after, targets = done ++ target :: remaining →
      ((done.map RunCollection.Step.unlink).forM perform) initial = .ok () before →
      perform (.unlink target) before = .ok () after → project after = project before) :
    project final = project initial := by
  induction targets generalizing initial with
  | nil => cases ran; rfl
  | cons target remaining ih =>
    change EStateM.bind (perform (.unlink target)) (fun _ =>
      (remaining.map RunCollection.Step.unlink).forM perform) initial = _ at ran
    cases next : perform (.unlink target) initial with
    | error cause reached => simp only [EStateM.bind, next] at ran; cases ran
    | ok value reached =>
      cases value
      simp only [EStateM.bind, next] at ran
      have tail := ih ran (by
        intro done address todo before after order earlier returned
        apply frame (target :: done) address todo before after (congrArg (List.cons target) order) ?_ returned
        change EStateM.bind (perform (.unlink target)) (fun _ => (done.map RunCollection.Step.unlink).forM perform)
          initial = _
        simpa only [EStateM.bind, next] using earlier)
      exact tail.trans (frame [] target remaining initial reached rfl rfl next)

namespace CheckpointRunCollectionReports

variable {checkpoint : NativeReadyCheckpoint state reports} {writer : SegmentedWriterState} {held : List UInt64}

/-- Every protected binding continues from the checkpoint's final raw
observation through the actual selected unlink prefix and barrier return. -/
theorem preservesBindings (seen : CheckpointRunCollectionReports checkpoint writer held) {generation : UInt64}
    (index : Nat) (protectedGeneration : writer.installed.generation ≤ generation ∨ generation ∈ held) :
    let path := state.session.directory.file (.run generation index)
    (seen.collector.pathObject (seen.collector.toNativeObsoleteRunPass.returnCensus,
      seen.collector.atBarrier.syncDirectory) path).map seen.collector.lifetime.namespaceView.modelObject =
      checkpoint.bindings reports.observed.completed.2 path := by
  intro path
  have prefixFrame := preservesUnlinkFrame seen.collector.reports.perform
    (fun reached => seen.collector.pathObject ((checkpoint.next writer).census, reached) path)
    seen.collector.unlinked (fun done target remaining before after order preceding returned =>
      seen.unlink done target remaining before after order preceding returned generation index protectedGeneration)
  have barrier := seen.barrier generation index protectedGeneration
  rw [seen.collector.toNativeObsoleteRunPass.barrierCensus.1] at barrier
  exact (congrArg (Option.map seen.collector.lifetime.namespaceView.modelObject)
    (barrier.trans prefixFrame)).trans (seen.atEntry generation index protectedGeneration)

/-- The completed pass retains every known byte binding of the exact
checkpoint image under the same hold list and settles every older
unheld name absent. Its directory and lock slots are still live. -/
theorem completes (seen : CheckpointRunCollectionReports checkpoint writer held)
    (completed : checkpoint.Completed writer) :
    seen.collector.run = .ok () (seen.collector.next.session.phase,
      ⟨(seen.collector.next.cache, seen.collector.atBarrier.syncDirectory), seen.collector.next.files.owners⟩) ∧
    (∀ generation index, generation < writer.installed.generation → generation ∉ held →
      seen.collector.atBarrier.syncDirectory.DurablyAbsent (generation, index)) ∧
    (∀ generation index bytes, writer.installed.generation ≤ generation ∨ generation ∈ held →
      (reports.runs reports.observed.completed).guaranteed generation index = some bytes →
      seen.collector.atBarrier.syncDirectory.guaranteed generation index = some bytes) ∧
    (checkpoint.next writer).directorySlot ∈ seen.collector.toNativeObsoleteRunPass.returnCensus.slots ∧
    (checkpoint.next writer).owner ∈ seen.collector.toNativeObsoleteRunPass.returnCensus.slots := by
  obtain ⟨_, obsolete, retained, _, _⟩ := seen.collector.reclaims completed.valid
  have custody := seen.collector.toNativeObsoleteRunPass.custody completed.valid
  exact ⟨(seen.collector.returns completed.valid).2.1, by simpa only [seen.holds, NativeReadyCheckpoint.next] using obsolete,
    by simpa only [seen.holds, seen.initial, NativeReadyCheckpoint.next] using retained, custody.2.2.2.2.2.1, custody.2.2.2.2.2.2.1⟩

variable {history : List WAL.Write} {log : List DatabaseSubmissions}

/-- Reports for the next explicit close of the actually collected state.
The close begins from the same selected run name that survived the
collector's final directory barrier. -/
def ObservesClose (seen : CheckpointRunCollectionReports checkpoint writer held)
    (current : NativeReadPosition history log) (completed : checkpoint.Completed writer)
    (sameHistory : writer.history = history) (index : Nat) (input : FilePath) : Prop :=
  ∀ collected, NativeObsoleteRunCollectionStep (current.afterCheckpoint checkpoint completed sameHistory)
    seen.collector collected →
    ∃ close : NativeCloseReopenObservation collected.state input,
      close.close.report.result = .ok () ∧
      let path := state.session.directory.file (.run attempt.prepared.generation index)
      close.files.names path = (seen.collector.pathObject (seen.collector.toNativeObsoleteRunPass.returnCensus,
        seen.collector.atBarrier.syncDirectory) path).map seen.collector.lifetime.namespaceView.modelObject

/-- The exact collection return, close and physical read of the protected
checkpoint run in the new session. -/
def SelectedRunReopen (seen : CheckpointRunCollectionReports checkpoint writer held)
    (current : NativeReadPosition history log) (completed : checkpoint.Completed writer)
    (sameHistory : writer.history = history) (index : Nat) (run : Compaction.CheckedRun) (input : FilePath)
    (next : NativeReadPosition history log) : Prop :=
    let path := state.session.directory.file (.run attempt.prepared.generation index)
    ∃ (collected : NativeReadPosition history log) (close : NativeCloseReopenObservation collected.state input),
      NativeObsoleteRunCollectionStep (current.afterCheckpoint checkpoint completed sameHistory) seen.collector collected ∧
      close.close.report.result = .ok () ∧ NativeCloseReopenStep collected close next ∧
      next.reads = current.reads ∧ InstalledClientReplay log current.reads history next.state.writer.installed next.state.session ∧
      next.state.writer.installed.table.SameData attempt.table ∧
      next.state.writer.installed.generation = attempt.prepared.generation ∧
      next.state.writer.installed.table.runs[index]? = some run ∧
      next.state.writer.published.durable attempt.prepared.generation index = some run.run.bytes ∧
      ∃ (file : CompletedCheckpointTemporaryFile checkpoint.descriptors checkpoint.primitives.cached
          checkpoint.primitives.cached.writeRun path run.run.bytes
          (reports.observed.atRun index).2 (reports.observed.atRun (index + 1)).2)
        (plan : ClosedReadyReopenLayout collected.state.writer collected.state.releasedFiles)
        (selected : SelectedIntegrityCheckpoint collected.state.writer.published.durable
          collected.state.releasedFiles.image.directory.active.manifest collected.state.writer.checkpoint)
        (opened : NativeCloseAlignedReads close.files input close.inventory plan.layout selected)
        (read : opened.opening.reads.reads.ObservesFile path run.run.bytes),
        let inode := file.handle.1.inode file.handle.2.1.description
        checkpoint.bindings reports.observed.completed.2 path = some inode ∧
        (checkpoint.descriptors (reports.observed.atRun (index + 1)).2).references file.handle.2.1.description = [] ∧
        (seen.collector.pathObject (seen.collector.toNativeObsoleteRunPass.returnCensus,
          seen.collector.atBarrier.syncDirectory) path).map seen.collector.lifetime.namespaceView.modelObject = some inode ∧
        close.files.names path = some inode ∧ close.files.bytes inode = some run.run.bytes ∧
        opened.run = next.opened ∧ read.object = inode

/-- The collected writer feeds the ordinary close and actual aligned open.
The selected read opens the inode synced by the checkpoint at this index. -/
theorem reopensSelectedRun (seen : CheckpointRunCollectionReports checkpoint writer held)
    (current : NativeReadPosition history log) (completed : checkpoint.Completed writer)
    (published : attempt.Installs writer) (sameHistory : writer.history = history) {index : Nat}
    {run : Compaction.CheckedRun} (selectedRun : attempt.table.runs[index]? = some run)
    (binding : checkpoint.RunBinding index) {input : FilePath}
    (observe : seen.ObservesClose current completed sameHistory index input) :
    ∃ next, seen.SelectedRunReopen current completed sameHistory index run input next := by
  let path := state.session.directory.file (.run attempt.prepared.generation index)
  let checkpointed := current.afterCheckpoint checkpoint completed sameHistory
  obtain ⟨collected, collectedStep⟩ := checkpointed.collectsObsoleteRuns seen.collector
  obtain ⟨close, closeOK, sameName⟩ := observe collected collectedStep
  obtain ⟨next, reopened⟩ := collected.closesAndReopens close
  obtain ⟨file, checkpointInode, dropped⟩ := binding.completes selectedRun
  have protectedGeneration : writer.installed.generation ≤ attempt.prepared.generation := by
    rw [completed.installed]
    exact UInt64.le_refl _
  have survivingInode := (seen.preservesBindings index (.inl protectedGeneration)).trans checkpointInode
  have closeInode := sameName.trans survivingInode
  have beforeBytes : (reports.runs reports.observed.completed).guaranteed attempt.prepared.generation index =
      some run.run.bytes := by
    have written := completed.runs index (List.getElem?_eq_some_iff.mp selectedRun).1
    rw [completed.installed] at written
    change _ = (attempt.table.runs.map (·.run.bytes))[index]? at written
    rwa [List.getElem?_map, selectedRun] at written
  have collectedBytes : collected.state.writer.published.durable attempt.prepared.generation index = some run.run.bytes :=
    (congrFun (congrFun collectedStep.durable attempt.prepared.generation) index).trans
      ((seen.completes completed).2.2.1 _ index _ (.inl protectedGeneration) beforeBytes)
  obtain ⟨base, checkpointBase, data, baseClock⟩ := published.restored
  have collectedBase : collected.state.writer.checkpoint = some (base, attempt.prepared.generation) := by
    rw [collectedStep.state]
    exact checkpointBase
  have loaded := reopened.loadsCompleteCheckpoint collectedBase (by rw [collectedStep.state]; exact baseClock)
  have generation : next.state.writer.installed.generation = attempt.prepared.generation := by
    rw [next.readPrefix.refines.1.retained.resumed.generation, reopened.frame.checkpoint, collectedBase]
    rfl
  have sameReads : next.reads = current.reads := reopened.reads.trans collectedStep.reads
  have replay : InstalledClientReplay log current.reads history next.state.writer.installed next.state.session :=
    sameReads ▸ next.readPrefix.guardedReplay
  have foundDurable := (congrFun (congrFun reopened.frame.durable attempt.prepared.generation) index).trans collectedBytes
  have manifest : collected.state.writer.target.pair.manifest = some attempt.manifest := by
    have named := completed.manifestBinding
    rw [completed.files] at named
    change writer.files.directory.active.manifest = _ at named
    have pair : writer.files.directory.active = writer.target.pair := completed.valid.retained.resumed.ready.selected
    rw [collectedStep.state]
    exact (congrArg DirectoryPublication.Bindings.manifest pair).symm.trans named
  have count : attempt.table.runs.length.toUInt64.toNat = attempt.table.runs.length :=
    UInt64.toNat_ofNat_of_lt' reports.preflight.preparedFacts.2.2.1
  have declared : index < (IntegrityCheckpoint.fromRuns
      (checkpointHeader attempt.table (SegmentedCheckpointReport.generation state.writer)) attempt.plan.files).header.runCount.toNat := by
    change index < attempt.table.runs.length.toUInt64.toNat
    rw [count]
    exact (List.getElem?_eq_some_iff.mp selectedRun).1
  obtain ⟨plan, selected, opened, _, returned, _, _, _, _, _, reads⟩ := reopened.exactOpen
  have readPath : collected.state.session.directory.file (.run attempt.prepared.generation index) = path := by
    rw [collectedStep.state]
    rfl
  have observed := reads.runs attempt.manifest _ manifest published.decodedManifest
    index declared run.run.bytes collectedBytes
  change opened.ReadsOriginal (collected.state.session.directory.file (.run attempt.prepared.generation index))
    run.run.bytes at observed
  rw [readPath] at observed
  obtain ⟨read, rawBinding, rawBytes⟩ := observed
  have object := Option.some.inj (rawBinding.symm.trans closeInode)
  have readBytes := object ▸ rawBytes
  refine ⟨next, collected, close, collectedStep, closeOK, reopened, sameReads, replay, loaded.symm ▸ data, generation, ?_,
    foundDurable, file, plan, selected, opened, read, checkpointInode, dropped, survivingInode, closeInode, readBytes,
    returned.symm, object⟩
  rw [loaded, data.runs]
  exact selectedRun

end CheckpointRunCollectionReports

variable {history : List WAL.Write} {log : List DatabaseSubmissions}

/-- A successful retained-version rewrite or adjacent-run compaction
publishes its exact output, completes the checked collector under the
prescribed hold list, and reopens the same run through chronological
native reads. The same client replay and retention floor explain the
new session, including point and range reads of reacquired old pins. -/
theorem NativeReadPosition.rewritesRunCheckpointCollectsAndReopens
    (current : NativeReadPosition history log) (request : RunMaintenance) {rewritten : PackedTable}
    (updated : request.update current.state.writer.installed.table = some rewritten)
    {image : Type}
    {attempt : SegmentedCheckpointReport current.state.session.directory (current.state.withTable rewritten).writer}
    {reports : CheckpointCompletionReports (CensusDirectoryCache × image) attempt}
    (checkpoint : NativeReadyCheckpoint (current.state.withTable rewritten) reports)
    (binding : checkpoint.RunBinding request.index) (held : List UInt64) (input : FilePath)
    (observe : ∀ writer (completed : checkpoint.Completed writer) (sameHistory : writer.history = history),
      ∃ seen : CheckpointRunCollectionReports checkpoint writer held,
        seen.ObservesClose current completed sameHistory request.index input) :
    ∃ (writer : SegmentedWriterState) (completed : checkpoint.Completed writer) (sameHistory : writer.history = history)
      (seen : CheckpointRunCollectionReports checkpoint writer held) (source : Sequential.History UInt64)
      (output : Compaction.CheckedRun) (next : NativeReadPosition history log),
      RunMaintenance.SourceAt current.state.writer.installed.table request source ∧
      output.history = source.retain current.state.writer.installed.table.pins.floor ∧
      output.run.bytes.size ≤ 16 + 32 * Compaction.Model.retentionRowBound source.rows
        current.state.writer.installed.table.pins.floor ∧
      (∃ rewrittenPosition, NativeRunMaintenanceStep current request true rewrittenPosition ∧
        rewrittenPosition.state = current.state.withTable rewritten) ∧
      seen.SelectedRunReopen current completed sameHistory request.index output input next ∧
      next.state.writer.installed.table.pins.floor = current.state.writer.installed.table.pins.floor ∧
      ∀ oldPin ∈ current.state.writer.installed.table.pins.active,
        ∃ newPin pinned, next.state.writer.installed.table.acquireAt oldPin.sequence = some (newPin, pinned) ∧
          newPin.sequence = oldPin.sequence ∧
          (∀ key, pinned.lookup newPin.handle key = current.state.writer.installed.table.lookup oldPin.handle key) ∧
          ∀ start stop, pinned.range newPin.handle start stop =
            current.state.writer.installed.table.range oldPin.handle start stop := by
  obtain ⟨_, rewrittenPosition, rewrite⟩ := current.rewritesRun request
  have reached := rewrite.reached
  rw [updated] at reached
  obtain ⟨rfl, rewrittenState⟩ := reached
  obtain ⟨priorValid, historyEq, _⟩ := current.readPrefix.refines
  have rewriteValid := rewrittenState ▸ rewrittenPosition.readPrefix.refines.1
  obtain ⟨writer, completed, published⟩ := checkpoint.completesWithPublication rewriteValid
  have sameHistory := completed.sameHistory.trans historyEq
  obtain ⟨seen, reportsBeforeClose⟩ := observe writer completed sameHistory
  obtain ⟨source, output, sourceAt, outputAt, retained⟩ := request.outputAt updated
  have publishedAt := RunMaintenance.preservesRunAtFlush reports.preflight.preparedFacts.1 outputAt
  obtain ⟨next, selected⟩ := seen.reopensSelectedRun current completed published sameHistory publishedAt binding reportsBeforeClose
  have closure := selected
  obtain ⟨collected, _, collectedStep, _, reopened, _, _, data, _⟩ := closure
  have rewritePins := (request.update_spec updated).2.2
  have pins := completed.pins.trans rewritePins
  rw [published.installed] at pins
  have floor := data.floor.trans (congrArg Sequential.SnapshotPins.floor pins)
  have directory : next.state.session.directory = current.state.session.directory := by
    rw [reopened.frame.directory, collectedStep.state]
    rfl
  have continued := next.readPrefix.refines
  refine ⟨writer, completed, sameHistory, seen, source, output, next, sourceAt, retained,
    Compaction.CheckedRun.byteSize_le_of_retainedHistory retained, ⟨rewrittenPosition, rewrite, rewrittenState⟩,
    selected, floor, ?_⟩
  intro oldPin active
  exact priorValid.retained.reacquireReadsStable (directory ▸ continued.1.retained) (suffix := [])
    (by simpa using continued.2.1.trans historyEq.symm) active
    (floor.symm ▸ current.state.writer.installed.table.pins.safe oldPin active)

end Alvoki.Storage.DiskSession
