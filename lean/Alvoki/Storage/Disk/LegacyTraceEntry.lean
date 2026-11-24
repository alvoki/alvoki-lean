import Alvoki.Storage.Disk.ObservedMarkedState
import Alvoki.Storage.Disk.RecoveryProgress

namespace Alvoki.WAL.Boundary

open Storage

/-- Enter the mixed marked trace from either admitted legacy retry image.
Successful primitive reads and the chosen durability reports determine the
actual shared open result, including the installed table and generation.
The caller supplies the provenance of the existing checkpoint as a prefix
of this WAL. The returned live refinement then follows from exact replay. -/
theorem legacyBootstrapRetry_observedReady {before : ReopenImage} (checkpoint : FixedMarkedCheckpoint)
    {history pending : List WAL.Write} (valid : before.LegacyBootstrapValid checkpoint.manifest history)
    (split : history = checkpoint.covered ++ pending)
    (checkpointHistory : RepresentsWalHistory checkpoint.covered checkpoint.model)
    (fits : (WAL.encode history).size < UInt64.size)
    (reads : RecoveryReads checkpoint.image before checkpoint.manifest)
    (reports : LegacyOpenReports)
    (success : match before.directory.active.walBoundary with
      | none => ∀ bytes, before.wal.active = some bytes → reports.Succeeds bytes.size (WAL.encode history).size
      | some _ => reports.aligned = .success) :
    ∃ loaded marker bytes, ∃ state : ObservedMarkedState,
      reads.checkpointReads.result = .ok loaded ∧
      reads.walReads.marker = .ok marker ∧ reads.walReads.wal = .ok (some bytes) ∧
      runLegacyRetryOpen loaded marker bytes reports before =
        .ok (state.writer.table, state.generation, state.writer.walBytes) state.writer.image ∧
      MarkedWriterState.observeReopen state.writer.table state.writer.image = some state.writer ∧
      state.writer.history = history ∧ state.durable = checkpoint.image.durable ∧
      state.Valid ∧ state.writer.table.pins.active = [] := by
  have within : checkpoint.table.committed.toNat ≤ history.length := by
    rw [← checkpoint.watermark, split, List.length_append]
    exact Nat.le_add_right _ _
  obtain ⟨loaded, marker, bytes, table, after, checkpointRead, markerRead, walRead, opened,
      generation, ready, replayed, observed⟩ :=
    legacyBootstrapRetry_completes checkpoint valid within fits reads.checkpointReads reads.readManifest
      reads.readRuns reads.walReads reads.readMarker reads.readWal reports success
  let writer : MarkedWriterState := ⟨table, (WAL.encode history).size, after, history⟩
  obtain ⟨model, refined, represented, fresh⟩ := replayed.refinesHistory ready split checkpointHistory
  let installed : FixedMarkedCheckpoint := { checkpoint with
    image := { checkpoint.image with manifest := after.directory.project .manifest } }
  let state : MarkedDatabaseState := ⟨writer, installed, (loaded.getD (.empty, 0)).2⟩
  have valid : state.Valid :=
    ⟨ready, ⟨pending, split⟩, ⟨model, refined, represented⟩, checkpointHistory, generation⟩
  exact ⟨loaded, marker, bytes, state.observe, checkpointRead, markerRead, walRead, opened,
    observed, rfl, rfl, valid.observe, fresh⟩

end Alvoki.WAL.Boundary
