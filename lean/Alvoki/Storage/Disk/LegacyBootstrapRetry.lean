import Alvoki.Storage.Disk.LegacyBootstrapCuts

namespace Alvoki.WAL.Boundary
open Storage

/-- Evaluate the shared native open continuation after the locked checkpoint
read. The successfully observed WAL already exists. The first marker is
published only if its lookup found no marker. -/
def runLegacyRetryOpen (checkpoint : Option (PackedTable × UInt64))
    (marker : Option ByteArray) (bytes : ByteArray) (reports : LegacyOpenReports) :
    EStateM String ReopenImage (PackedTable × UInt64 × Nat) :=
  withRecoveredOpen checkpoint (pure marker) (pure (some bytes))
    (fun result => match result with | .ok value => pure value | .error message => throw message)
    (fun message => throw message) (fun _ => throw "expected an existing legacy WAL")
    (fun selected => Publication.run (performRepair reports.repair selected))
    (fun _ => performAlignedSync false reports.aligned)
    (fun length => Publication.run (performLegacyMarker reports.marker (encode length.toUInt64)))
    (fun table generation length => pure (table, generation, length))

private theorem runLegacyRetryOpen_marked {checkpoint : Option (PackedTable × UInt64)}
    {marker bytes : ByteArray} {length : UInt64} {table : PackedTable} (reports : LegacyOpenReports)
    (decoded : decode marker = .ok length)
    (recovered : recoverMarked (checkpoint.getD (.empty, 0)).1 length bytes = .ok (bytes, table))
    (synced : reports.aligned = .success) (before : ReopenImage) :
    runLegacyRetryOpen checkpoint (some marker) bytes reports before =
      .ok (table, (checkpoint.getD (.empty, 0)).2, bytes.size) before.syncDirectory := by
  simp [runLegacyRetryOpen, withRecoveredOpen, withOpenWal, Option.mapM, Functor.map, EStateM.map,
    Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, decoded, recovered, synced,
    Publication.finishReopen, Publication.runReopen, performAlignedSync]

/-- The modeled first-marker retry completes from either admitted visible
marker choice when the locked file reads and the chosen durability reports
succeed. The watermark must fit the same complete legacy history. The
result includes the exact loaded generation and a writer ready for the
observed checkpoint and that history. -/
theorem legacyBootstrapRetry_completes {before : ReopenImage} (checkpoint : FixedMarkedCheckpoint)
    {history : List WAL.Write} (valid : before.LegacyBootstrapValid checkpoint.manifest history)
    (covered : checkpoint.table.committed.toNat ≤ history.length)
    (fits : (WAL.encode history).size < UInt64.size)
    (checkpointReads : CheckpointReadObservations checkpoint.image checkpoint.manifest)
    (manifestRead : checkpointReads.readManifest = .ok checkpoint.manifest)
    (runReads : ∀ bytes header, checkpoint.manifest = some bytes → Manifest.decode bytes = .ok header →
      ∀ index, index < header.runCount.toNat →
        ∃ payload, checkpointReads.readRun header.generation index = .ok payload)
    (walReads : MarkedWalReads before) (markerRead : walReads.marker = .ok before.directory.active.walBoundary)
    (walRead : walReads.wal = .ok before.wal.active) (reports : LegacyOpenReports)
    (success : match before.directory.active.walBoundary with
      | none => ∀ bytes, before.wal.active = some bytes → reports.Succeeds bytes.size (WAL.encode history).size
      | some _ => reports.aligned = .success) :
    ∃ loaded marker bytes table after,
      checkpointReads.result = .ok loaded ∧ walReads.marker = .ok marker ∧
      walReads.wal = .ok (some bytes) ∧ runLegacyRetryOpen loaded marker bytes reports before =
        .ok (table, (loaded.getD (.empty, 0)).2, (WAL.encode history).size) after ∧
      ((checkpoint.manifest.mapM fun bytes => (Manifest.decode bytes).map (·.generation)).map (·.getD 0) :
        Except String UInt64) = .ok (loaded.getD (.empty, 0)).2 ∧
      let writer : MarkedWriterState := ⟨table, (WAL.encode history).size, after, history⟩
      writer.ReadyFor checkpoint.manifest ∧ checkpoint.RecoveredTable writer ∧
      MarkedWriterState.observeReopen table after = some writer := by
  obtain ⟨base, loads, same⟩ := checkpoint.written.loads
  have durable := checkpoint.written.ordered_durable_runs checkpoint.accepted
  obtain ⟨loaded, checkpointLoaded, sameBase⟩ := checkpointReads.completes manifestRead runReads durable loads
  obtain ⟨_, _, readHistory⟩ := valid.wal.activeValid
  have ordered := WAL.decodeOrdinals_sound readHistory
  let oldEvents := history.take checkpoint.table.committed.toNat
  let pending := history.drop checkpoint.table.committed.toNat
  have whole : oldEvents ++ pending = history := List.take_append_drop ..
  have watermark : oldEvents.length = base.committed.toNat := by
    simp [oldEvents, List.length_take, Nat.min_eq_left covered, same.committed]
  obtain ⟨table, replayed, count⟩ :=
    recoverSelected_encoded_complete base oldEvents pending (whole.symm ▸ ordered) watermark
  rw [whole] at replayed
  have clock : table.committed.toNat = history.length := by
    rw [← whole, List.length_append]
    exact count
  have loadedReplay : recoverSelected (loaded.getD (.empty, 0)).1 (WAL.encode history) = .ok table := by
    rw [sameBase]
    exact replayed
  have bounded := recoverSelected_rowBounds (same.rowBounds checkpoint.written.rowBounds) replayed
  have generation := checkpoint.written.loaded_generation checkpoint.accepted checkpointReads checkpointLoaded
  obtain ⟨manifest, bytes, visibleWal, recovered, aligned⟩ :=
    valid.replay (List.mem_cons_self ..) (List.mem_cons_self ..) loadedReplay fits
  have opened : ∃ after, runLegacyRetryOpen loaded before.directory.active.walBoundary bytes reports before =
      .ok (table, (loaded.getD (.empty, 0)).2, (WAL.encode history).size) after ∧
      after.SettledFor checkpoint.manifest history := by
    rcases valid.metadata.activeValid.2 with absent | published
    · rw [absent] at recovered success ⊢
      obtain ⟨after, ran, active, durable, walActive, walDurable⟩ :=
        runLegacyMarkedOpen_success reports recovered visibleWal fits (success _ visibleWal)
      refine ⟨after, ?_, ⟨?_, durable, walActive, walDurable⟩⟩
      · rw [runLegacyMarkedOpen_eq_shared] at ran
        exact ran
      · rw [active]
        change (⟨before.directory.active.manifest, _⟩ : DirectoryPublication.Bindings) = _
        rw [manifest]
    · rw [published] at recovered success ⊢
      have exactBytes : bytes = WAL.encode history := aligned.resolve_left (by rw [published]; simp)
      subst bytes
      change (do
        let length ← decode (encode (WAL.encode history).size.toUInt64)
        recoverMarked (loaded.getD (.empty, 0)).1 length (WAL.encode history)) = _ at recovered
      rw [decode_encode] at recovered
      refine ⟨before.syncDirectory, runLegacyRetryOpen_marked reports (decode_encode _) recovered success _,
        ⟨?_, rfl, visibleWal, rfl⟩⟩
      change (⟨before.directory.active.manifest, before.directory.active.walBoundary⟩ :
        DirectoryPublication.Bindings) = _
      rw [manifest, published]
  obtain ⟨after, ran, settled⟩ := opened
  refine ⟨loaded, _, bytes, table, after, checkpointLoaded, markerRead, walRead.trans (congrArg Except.ok visibleWal),
    ran, generation, ⟨settled, ordered, clock.symm, rfl, fits, bounded⟩, ?_, ?_⟩
  · have load : checkpoint.manifest.elim (Except.ok PackedTable.empty)
        (fun bytes => Manifest.decode bytes >>= fun header => loadRunSet header checkpoint.files) = .ok base := by
      cases visible : checkpoint.manifest <;> rw [visible] at loads <;> exact loads
    unfold FixedMarkedCheckpoint.RecoveredTable
    rw [load]
    exact replayed
  · simp [MarkedWriterState.observeReopen, settled.2.2.1, WAL.decodeOrdinals_encode _ ordered, Except.toOption]

end Alvoki.WAL.Boundary
