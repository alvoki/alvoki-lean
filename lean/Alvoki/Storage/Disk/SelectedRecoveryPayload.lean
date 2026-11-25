import Alvoki.Storage.Disk.RetainedWriterState

namespace Alvoki.Storage.DiskSession

open Compaction WalSegmentRepair
open WAL (frameSize)

private theorem selectedLoadedFiles {durable : CheckpointPublication.RunFiles} {bytes : ByteArray}
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint durable (some bytes) checkpoint) :
    ∃ manifest files,
      Manifest.IntegrityCheckpoint.decode bytes = .ok manifest ∧
      (List.range manifest.header.runCount.toNat).mapM (durable manifest.header.generation) = some files ∧
      loadIntegrityRunSet manifest files = .ok (checkpoint.getD (.empty, 0)).1 := by
  cases selected with
  | present decoded stored loaded => exact ⟨_, _, decoded, stored, loaded⟩

private theorem loadedRunBytes {files : List ByteArray} {runs : List CheckedRun}
    (opened : files.mapM CheckedRun.openBytes = .ok runs) :
    files = runs.map (·.run.bytes) := by
  induction files generalizing runs with
  | nil =>
    cases Except.ok.inj opened
    rfl
  | cons bytes rest ih =>
    cases head : CheckedRun.openBytes bytes with
    | error cause => simp [List.mapM_cons, head, Bind.bind, Except.bind] at opened
    | ok run =>
      cases tail : rest.mapM CheckedRun.openBytes with
      | error cause => simp [List.mapM_cons, head, tail, Bind.bind, Except.bind] at opened
      | ok remaining =>
        have exactRuns : run :: remaining = runs := by
          simpa [List.mapM_cons, head, tail, Bind.bind, Except.bind, Pure.pure, Except.pure] using opened
        rw [← exactRuns, List.map_cons, (CheckedRun.openBytes_spec head).2, ih tail]

private theorem runByteSum (runs : List CheckedRun) :
    (runs.map (·.run.bytes.size)).sum =
      16 * runs.length + 32 * (runs.map (·.history.rows.length)).sum := by
  induction runs with
  | nil => rfl
  | cons run rest ih =>
    simp only [List.map_cons, List.length_cons, List.sum_cons, run.byteSize_eq_history, ih, Nat.mul_add]
    omega

private theorem runRowSum_le {runs : List CheckedRun} {budgets : List Nat}
    (length : runs.length = budgets.length)
    (bounds : ∀ pair ∈ runs.zip budgets, pair.1.history.rows.length ≤ pair.2) :
    (runs.map (·.history.rows.length)).sum ≤ budgets.sum := by
  induction runs generalizing budgets with
  | nil => simp
  | cons run rest ih =>
    cases budgets with
    | nil => simp at length
    | cons budget others =>
      have head := bounds (run, budget) (by simp)
      have tail := ih (by simpa using length) (fun pair member => bounds pair (by simp [member]))
      simpa only [List.map_cons, List.sum_cons] using Nat.add_le_add head tail

/-- The run payload is the exact list selected by a present durable
manifest. Budgets correspond to those runs in the same order. The WAL
payload is the selected segment chain, which can include a prefix of a
segment already covered by the manifest in addition to uncheckpointed
frames. The bound counts these logical payload bytes. -/
theorem SegmentedWriterState.RetainedReady.selectedRecoveryPayload {directory descriptor}
    {state : SegmentedWriterState}
    (ready : state.RetainedReady directory descriptor)
    {bytes : ByteArray} (present : state.target.pair.manifest = some bytes)
    (budgets : List Nat)
    (length : (state.checkpoint.getD (.empty, 0)).1.runs.length = budgets.length)
    (bounds : ∀ pair ∈ (state.checkpoint.getD (.empty, 0)).1.runs.zip budgets,
      pair.1.run.bytes.size ≤ 16 + 32 * pair.2) :
    ∃ (manifest : Manifest.IntegrityCheckpoint) (files : List ByteArray) (first : Nat),
      Manifest.IntegrityCheckpoint.decode bytes = .ok manifest ∧
      (List.range manifest.header.runCount.toNat).mapM
        (state.published.durable manifest.header.generation) = some files ∧
      files = (state.checkpoint.getD (.empty, 0)).1.runs.map (·.run.bytes) ∧
      (files.map ByteArray.size).sum = 16 * manifest.header.runCount.toNat +
        32 * ((state.checkpoint.getD (.empty, 0)).1.runs.map (·.history.rows.length)).sum ∧
      state.target.range.watermark = (state.checkpoint.getD (.empty, 0)).1.committed.toNat ∧
      first ≤ state.target.range.watermark ∧
      selectWalSegmentReads (state.wal.segments.map WalSegment.first) state.target.range.watermark =
        some (first, (state.wal.readDescriptors state.target.range.watermark).map WalSegment.first) ∧
      let selectedWal := WalSegment.concatenate (state.wal.readDescriptors state.target.range.watermark)
      let replayWal := WAL.encode (state.history.drop state.target.range.watermark)
      selectedWal = WAL.encode (state.history.drop first) ∧
      selectedWal.size = (state.target.range.watermark - first) * frameSize + replayWal.size ∧
      (files.map ByteArray.size).sum + selectedWal.size ≤
        16 * manifest.header.runCount.toNat + 32 * budgets.sum +
          (state.target.range.watermark - first) * frameSize + replayWal.size := by
  let table := (state.checkpoint.getD (.empty, 0)).1
  have selected : SelectedIntegrityCheckpoint state.published.durable (some bytes) state.checkpoint :=
    present ▸ ready.resumed.selected
  obtain ⟨manifest, files, decoded, stored, loaded⟩ := selectedLoadedFiles selected
  obtain ⟨checked, opened, restored⟩ := loadRunSet_restored (loadIntegrityRunSet_iff.mp loaded).2
  have exactFiles : files = table.runs.map (·.run.bytes) := by
    rw [(PackedTable.restore_spec restored).1]
    exact loadedRunBytes opened
  have count : table.runs.length = manifest.header.runCount.toNat := by
    obtain ⟨stamps, matched, _⟩ := (manifest.validateRuns_iff files).mp (loadIntegrityRunSet_iff.mp loaded).1
    rw [exactFiles, List.length_map] at matched
    exact matched.symm.trans stamps
  have runBytes : (files.map ByteArray.size).sum =
      16 * manifest.header.runCount.toNat + 32 * (table.runs.map (·.history.rows.length)).sum := by
    rw [exactFiles, List.map_map]
    change (table.runs.map (·.run.bytes.size)).sum = _
    rw [runByteSum, count]
  have chosen : state.wal.Selects state.target.pair := ready.walPair ▸ List.mem_cons_self
  obtain ⟨first, starts, _, addresses, _, payload⟩ :=
    ready.layout.selects ready.valid chosen state.target.decoded
  have clocks := DirectoryPublication.Bindings.walRange_accounting state.target.decoded
  have watermark : state.target.range.watermark = table.committed.toNat :=
    Option.some.inj (clocks.1.symm.trans ready.resumed.selected.watermark)
  have covered := clocks.2.1
  rw [ready.resumed.through] at covered
  let selectedWal := WalSegment.concatenate (state.wal.readDescriptors state.target.range.watermark)
  let replayWal := WAL.encode (state.history.drop state.target.range.watermark)
  have walBytes : selectedWal.size = (state.target.range.watermark - first) * frameSize + replayWal.size := by
    unfold selectedWal replayWal
    rw [payload, WAL.encode_size, WAL.encode_size, List.length_drop, List.length_drop,
      Nat.mul_comm (state.target.range.watermark - first), ← Nat.mul_add]
    congr 1
    omega
  refine ⟨manifest, files, first, decoded, stored, exactFiles, runBytes, watermark, starts, addresses,
    payload, walBytes, ?_⟩
  rw [runBytes, walBytes]
  have rowBounds : ∀ pair ∈ table.runs.zip budgets, pair.1.history.rows.length ≤ pair.2 := by
    intro pair member
    have limit := bounds pair member
    rw [pair.1.byteSize_eq_history] at limit
    omega
  have budget := runRowSum_le length rowBounds
  change (table.runs.map (·.history.rows.length)).sum ≤ budgets.sum at budget
  dsimp only [replayWal]
  omega

end Alvoki.Storage.DiskSession
