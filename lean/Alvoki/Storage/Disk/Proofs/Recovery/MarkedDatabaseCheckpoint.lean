import Alvoki.Storage.Disk.Proofs.Recovery.MarkedDatabaseState
import Alvoki.Storage.Disk.Proofs.Checkpoint.MarkedCheckpointReady
import Alvoki.Storage.Disk.Proofs.Recovery.MarkedCheckpointReopenReady

namespace Alvoki.WAL.Boundary
open Storage

def _root_.Alvoki.Storage.CheckpointPublication.RunSet.forTable (table : PackedTable)
    (generation : UInt64) : CheckpointPublication.RunSet :=
  ⟨checkpointHeader table generation, table.runs.map (·.run.bytes)⟩

def MarkedDatabaseState.checkpointRuns (state : MarkedDatabaseState) (table : PackedTable) :
    CheckpointPublication.RunSet :=
  .forTable table (UInt64.ofNat (state.generation.toNat + 1))

private theorem generationFromDecode {bytes : ByteArray} {header : Manifest.Checkpoint}
    (decoded : Manifest.decode bytes = .ok header) :
    (((some bytes).mapM fun found => (Manifest.decode found).map (·.generation)).map (·.getD 0) :
      Except String UInt64) = .ok header.generation := by
  simp [Option.mapM, decoded, Functor.map, Except.map]

private theorem observedGeneration {manifest : Option ByteArray} {header : Manifest.Checkpoint}
    (encoded : manifest = some (Manifest.encode header)) (floor : header.floor ≤ header.committed) :
    ((manifest.mapM fun bytes => (Manifest.decode bytes).map (·.generation)).map (·.getD 0) :
      Except String UInt64) = .ok header.generation :=
  encoded.symm ▸ generationFromDecode (Manifest.decode_encode header floor)

private theorem executedCheckpoint {initial published : CheckpointPublication.Image}
    {runs : CheckpointPublication.RunSet} {report : CheckpointPublication.Step → CheckpointPublication.StepReport}
    (reported : initial.runWithReports runs report = .ok () published) :
    initial.execute runs (CheckpointPublication.steps runs.files.length) = some published := by
  have outcome := initial.runWithReports_outcome runs report
  rw [reported] at outcome
  exact outcome

private theorem modelsAgree {table : PackedTable} {left right : Sequential.SnapshotTable UInt64}
    (first : table.Refines left) (second : table.Refines right) : left = right := by
  have sameRows := first.table.symm.trans second.table
  have sameClock := first.committed.symm.trans second.committed
  have samePins := first.pins.symm.trans second.pins
  cases left
  cases right
  cases sameRows
  cases sameClock
  cases samePins
  rfl

/-- A reported checkpoint success installs the actual prepared table, successor
generation and run set. Its original WAL and live pins remain available. -/
theorem MarkedDatabaseState.Valid.checkpointSucceeded {state : MarkedDatabaseState}
    (valid : state.Valid) {table : PackedTable} {published : CheckpointPublication.Image}
    (generationFits : state.generation.toNat + 1 < UInt64.size)
    (prepared : (flushForCheckpoint state.writer.table id : Except String PackedTable) = .ok table)
    (runCountFits : table.runs.length < UInt64.size)
    {report : CheckpointPublication.Step → CheckpointPublication.StepReport}
    (reported : (state.checkpoint.publicationInput state.writer).runWithReports
      (state.checkpointRuns table) report = .ok () published) :
    let runs := state.checkpointRuns table
    let writer : MarkedWriterState :=
      { state.writer with table := table, image := published.markedReopenImage state.writer.image }
    ∃ fixed : FixedMarkedCheckpoint, fixed.image = published ∧
      (⟨writer, fixed, runs.header.generation⟩ : MarkedDatabaseState).Valid := by
  intro runs writer
  obtain ⟨model, refines, represents⟩ := valid.live
  have executed : (state.checkpoint.publicationInput state.writer).execute
      runs (CheckpointPublication.steps runs.files.length) = some published := executedCheckpoint reported
  obtain ⟨_, fixed, manifestEq, _, imageEq, _, tableEq, coveredEq, _, ready⟩ :=
    checkpointMarked_ready valid.ready (initial := state.checkpoint.publicationInput state.writer)
      rfl valid.generationMatches generationFits prepared refines runCountFits executed
  obtain ⟨abstract, _, refined, canonical⟩ := CheckpointForRecovery.of_flushForCheckpoint_history
    prepared refines represents valid.ready.rowBounds runCountFits runs.header.generation
  have fixedRefined : table.Refines fixed.model := tableEq ▸ fixed.represents
  have abstractEq : abstract = fixed.model := modelsAgree refined fixedRefined
  have watermark : state.writer.history.length = table.committed.toNat := by
    rw [← tableEq, ← coveredEq]
    exact fixed.watermark
  have represented : RepresentsWalHistory state.writer.history fixed.model := by
    rw [← abstractEq]
    rwa [← watermark, List.take_length] at canonical
  have covered : ∃ pending, writer.history = fixed.covered ++ pending :=
    ⟨[], by rw [List.append_nil, coveredEq]⟩
  have floor : runs.header.floor ≤ runs.header.committed := by
    change table.pins.floor ≤ table.committed
    rw [fixedRefined.pins, fixedRefined.committed]
    exact fixed.model.floor_committed
  have generation := observedGeneration (header := runs.header) manifestEq floor
  have checkpointHistory : RepresentsWalHistory fixed.covered fixed.model := coveredEq ▸ represented
  exact ⟨fixed, imageEq, ⟨ready, covered, ⟨fixed.model, fixedRefined, represented⟩,
    checkpointHistory, generation⟩⟩

/-- A reported checkpoint error leaves no live writer. Only a subsequent
observed successful reopen determines the next installed state and generation. -/
theorem MarkedDatabaseState.Valid.checkpointInterrupted {state : MarkedDatabaseState}
    (valid : state.Valid) {preparedTable table : PackedTable} {published : CheckpointPublication.Image}
    (generationFits : state.generation.toNat + 1 < UInt64.size)
    (prepared : (flushForCheckpoint state.writer.table id : Except String PackedTable) = .ok preparedTable)
    (runCountFits : preparedTable.runs.length < UInt64.size)
    {checkpointReport : CheckpointPublication.Step → CheckpointPublication.StepReport}
    (reported : (state.checkpoint.publicationInput state.writer).runWithReports
      (state.checkpointRuns preparedTable) checkpointReport = .error () published)
    {reopenStart after : ReopenImage}
    (attempts : MarkedReopenAttempts (published.markedReopenImage state.writer.image) reopenStart)
    (checkpointReads : CheckpointReadObservations published reopenStart.directory.active.manifest)
    (walReads : MarkedWalReads reopenStart)
    {report : Publication.Step → RepairReport} {aligned : AlignedSyncReport}
    (opened : runMarkedReopen
      (MarkedReopenReads.mk walReads
        (checkpointReads.result.map fun loaded => (loaded.getD (.empty, 0)).1)).preflight
      report false aligned reopenStart = .ok table after) :
    ∃ next : MarkedDatabaseState, next.Valid ∧
      next.writer.history = state.writer.history ∧ next.checkpoint.image.durable = published.durable ∧
      MarkedWriterState.observeReopen table after = some next.writer ∧
      ∃ loaded, checkpointReads.result = .ok loaded ∧ next.generation = (loaded.getD (.empty, 0)).2 := by
  obtain ⟨model, refines, represents⟩ := valid.live
  obtain ⟨pending, splitHistory⟩ := valid.coveredPrefix
  obtain ⟨initialValid, cut⟩ := checkpointMarked_reported state.checkpoint valid.ready splitHistory
    valid.covered valid.generationMatches generationFits prepared refines represents runCountFits
    checkpointReport
  have exactCut : CheckpointPublication.Retry state.writer.history.length.toUInt64
      (CheckpointRepresentsPrefix state.writer.history) (state.checkpoint.publicationInput state.writer)
      published := by
    unfold MarkedDatabaseState.checkpointRuns CheckpointPublication.RunSet.forTable at reported
    rw [reported] at cut
    exact cut
  have fits : (WAL.encode state.writer.history).size < UInt64.size := valid.ready.length ▸ valid.ready.fits
  obtain ⟨fixed, nextModel, _, image, _, covered, _, coveredHistory, observed, ready, refined,
      live, _, loaded, _, read, generation, _, _⟩ :=
    CheckpointPublication.checkpointMarkedRetry_reopen_ready valid.ready.settled rfl fits
      valid.ready.ordered initialValid
      (fun _ _ ⟨checkpoint, model, written, refined, represented⟩ =>
        ⟨checkpoint, model, written.legacy, refined, represented⟩)
      exactCut attempts checkpointReads walReads opened
  let writer : MarkedWriterState := ⟨table, (WAL.encode state.writer.history).size, after, state.writer.history⟩
  let next : MarkedDatabaseState := ⟨writer, fixed, (loaded.getD (.empty, 0)).2⟩
  have durable := congrArg CheckpointPublication.Image.durable image
  refine ⟨next, ⟨ready, ?_, ⟨nextModel, refined, live⟩, coveredHistory, generation⟩, rfl,
    durable, observed, loaded, read, rfl⟩
  refine ⟨state.writer.history.drop fixed.table.committed.toNat, ?_⟩
  change state.writer.history = fixed.covered ++ state.writer.history.drop fixed.table.committed.toNat
  rw [covered, List.take_append_drop]

end Alvoki.WAL.Boundary
