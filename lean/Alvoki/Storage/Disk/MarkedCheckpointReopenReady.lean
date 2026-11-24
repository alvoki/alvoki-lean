import Alvoki.Storage.Disk.CheckpointHistory
import Alvoki.Storage.Disk.MarkedSessionTrace
import Alvoki.Storage.Disk.RecoveredPinRefinement

namespace Alvoki.Storage.CheckpointPublication
open WAL.Boundary

/-- After a checkpoint cut, the actual successful reopen determines both the
next writer and its checkpoint. The selected manifest is now settled, with
the same durable run map as the checkpoint cut. The returned table refines
a model with a fresh pin registry and represents the same whole WAL. -/
theorem checkpointMarkedRetry_reopen_ready {initial published : Image}
    {before reopenStart after : ReopenImage} {manifest : Option ByteArray}
    {history : List WAL.Write} {table : PackedTable}
    {expected : Manifest.Checkpoint → List ByteArray → Prop}
    (settled : before.SettledFor manifest history)
    (projects : initial.manifest = before.directory.project .manifest)
    (fits : (WAL.encode history).size < UInt64.size) (ordered : WAL.OrdinalsFrom 1 history)
    (initialValid : initial.Valid history.length.toUInt64 expected)
    (witness : ∀ header files, expected header files →
      ∃ checkpoint model, CheckpointForRecovery (some (Manifest.encode header)) files checkpoint ∧
        checkpoint.Refines model ∧ RepresentsWalHistory (history.take checkpoint.committed.toNat) model)
    (checkpoints : Retry history.length.toUInt64 expected initial published)
    (attempts : MarkedReopenAttempts (published.markedReopenImage before) reopenStart)
    (checkpointReads : CheckpointReadObservations published reopenStart.directory.active.manifest)
    (walReads : MarkedWalReads reopenStart)
    {report : Publication.Step → RepairReport} {aligned : AlignedSyncReport}
    (opened : runMarkedReopen
      (MarkedReopenReads.mk walReads
        (checkpointReads.result.map fun loaded => (loaded.getD (.empty, 0)).1)).preflight
      report false aligned reopenStart = .ok table after) :
    let next : MarkedWriterState := ⟨table, (WAL.encode history).size, after, history⟩
    ∃ fixed : FixedMarkedCheckpoint, ∃ model : Sequential.SnapshotTable UInt64,
      fixed.manifest = reopenStart.directory.active.manifest ∧
      fixed.image = { published with manifest := after.directory.project .manifest } ∧
      fixed.walSequence = fixed.table.committed ∧
      fixed.covered = history.take fixed.table.committed.toNat ∧
      fixed.image.readDurableCheckpointRuns fixed.manifest = some fixed.files ∧
      RepresentsWalHistory fixed.covered fixed.model ∧
      MarkedWriterState.observeReopen table after = some next ∧
      next.ReadyFor fixed.manifest ∧ next.table.Refines model ∧
      RepresentsWalHistory next.history model ∧ model.pins.active = [] := by
  obtain ⟨settledAfter, accepted, count, files, checkpoint, base, checkpointModel, _, written, durable,
    loaded, same, recovered, played, refined, represents, _, _⟩ :=
    checkpointMarkedRetry_reopen_refines settled projects fits ordered initialValid
      RepresentsWalHistory.empty witness checkpoints attempts checkpointReads walReads opened
  let covered := history.take checkpoint.committed.toNat
  let pending := history.drop checkpoint.committed.toNat
  have watermark : covered.length = checkpoint.committed.toNat :=
    represents.committed_count.symm.trans (congrArg UInt64.toNat refined.committed.symm)
  have splitHistory : covered ++ pending = history := List.take_append_drop ..
  have load : reopenStart.directory.active.manifest.elim (Except.ok PackedTable.empty)
      (fun bytes => Manifest.decode bytes >>= fun header => loadRunSet header files) = .ok base := by
    cases visible : reopenStart.directory.active.manifest <;> rw [visible] at loaded <;> exact loaded
  have applied : (reopenStart.directory.active.manifest.elim (Except.ok PackedTable.empty)
      (fun bytes => Manifest.decode bytes >>= fun header => loadRunSet header files) >>= fun replayBase =>
        recoverSelected replayBase (WAL.encode (covered ++ pending))) = .ok table := by
    rw [splitHistory, load]
    exact recovered
  obtain ⟨abstract, model, replayed, refines, data, clock, floor, pins⟩ :=
    recoverSelectedCheckpoint_refines_recoveredPins written refined watermark
      (splitHistory.symm ▸ ordered) applied
  have bounded := replay_rowBounds (same.rowBounds written.rowBounds) played
  have historyAbstract : RepresentsWalHistory history abstract := by
    rw [← splitHistory]
    exact represents.append replayed
  have historyModel := historyAbstract.preserve clock (UInt64.le_of_eq floor.symm)
    (refines.rowsBounded bounded) (fun _ _ _ => by rw [data])
  let fixed : FixedMarkedCheckpoint := {
    manifest := reopenStart.directory.active.manifest
    files := files
    image := { published with manifest := after.directory.project .manifest }
    walSequence := checkpoint.committed
    table := checkpoint
    model := checkpointModel
    covered := covered
    written := written
    accepted := written.accepts_exact_durable accepted durable
    represents := refined
    watermark := watermark
  }
  have observed : MarkedWriterState.observeReopen table after =
      some ⟨table, (WAL.encode history).size, after, history⟩ := by
    simp [MarkedWriterState.observeReopen, settledAfter.2.2.1, WAL.decodeOrdinals_encode _ ordered,
      Except.toOption]
  exact ⟨fixed, model, rfl, rfl, rfl, rfl, durable, represents, observed,
    ⟨settledAfter, ordered, count.symm, rfl, fits, bounded⟩, refines, historyModel, pins⟩

end Alvoki.Storage.CheckpointPublication
