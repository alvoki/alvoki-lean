import Alvoki.Storage.Disk.Proofs.Write.RetainedWriterState
import Alvoki.Storage.Disk.ManifestAcquisition

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

/-- The checked run parser retains the exact input payload for each run. -/
theorem loadedRunBytes {files : List ByteArray} {runs : List CheckedRun}
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
      files.length = manifest.header.runCount.toNat ∧
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
  have fileCount : files.length = manifest.header.runCount.toNat := by
    rw [exactFiles, List.length_map, count]
  refine ⟨manifest, files, first, decoded, stored, exactFiles, fileCount, runBytes, watermark, starts, addresses,
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

private theorem readAcceptedMarker {source : ByteArray} {count : UInt64}
    {read : USize → EStateM IO.Error Nat ByteArray}
    (accepted : WAL.Boundary.decode source = .ok count)
    (observes : PrefixChunkObserves source read) (available : PrefixChunksAvailableUntilEof source read) :
    readPrefixUntilEofWith (IO.userError "invalid WAL boundary length") read WAL.Boundary.acquisitionLimit
      ByteArray.empty 0 = .ok source 24 := by
  have length : source.size = 24 := by
    rw [← WAL.Boundary.decode_reencode accepted, WAL.Boundary.encode_size]
  have fits : WAL.Boundary.acquisitionLimit < USize.size :=
    Nat.lt_of_lt_of_le (by decide) USize.le_size
  have stop : min (0 + WAL.Boundary.acquisitionLimit) source.size = source.size := by
    rw [Nat.zero_add, Nat.min_eq_right]
    rw [length]
    decide
  have completed := readPrefixUntilEofWith_completes (IO.userError "invalid WAL boundary length")
    observes available WAL.Boundary.acquisitionLimit fits (bytes := ByteArray.empty) (Nat.zero_le _)
  dsimp only at completed
  rw [stop, ByteArray.extract_zero_size, ByteArray.empty_append, length] at completed
  exact completed

private theorem checkpointAbsent {durable : CheckpointPublication.RunFiles}
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint durable none checkpoint) : checkpoint = none := by
  cases selected
  rfl

/-- Charge the accepted metadata cursors and the exact selected run and WAL
payload. File presence is supplied by the selected pair. The manifest uses the
modeled prefix acquisition. Directory scans, libc I/O, repair writes and
unsuccessful attempts are outside this byte bound. -/
theorem SegmentedWriterState.RetainedReady.selectedRecoveryAcquisition {directory descriptor}
    {state : SegmentedWriterState} (ready : state.RetainedReady directory descriptor)
    (budgets : List Nat)
    (length : (state.checkpoint.getD (.empty, 0)).1.runs.length = budgets.length)
    (bounds : ∀ pair ∈ (state.checkpoint.getD (.empty, 0)).1.runs.zip budgets,
      pair.1.run.bytes.size ≤ 16 + 32 * pair.2)
    (readManifest readMarker : USize → EStateM IO.Error Nat ByteArray)
    (manifestHealthy : ∀ source, state.target.pair.manifest = some source →
      PrefixChunkObserves source readManifest ∧ PrefixChunksAvailable source readManifest ∧
        source.size < USize.size)
    (markerHealthy : ∀ source, state.target.pair.walBoundary = some source →
      PrefixChunkObserves source readMarker ∧ PrefixChunksAvailableUntilEof source readMarker) :
    ∃ (files : List ByteArray) (marker : ByteArray) (first manifestBytes : Nat),
      files = (state.checkpoint.getD (.empty, 0)).1.runs.map (·.run.bytes) ∧
      state.target.pair.walBoundary = some marker ∧
      readPrefixUntilEofWith (IO.userError "invalid WAL boundary length") readMarker
        WAL.Boundary.acquisitionLimit ByteArray.empty 0 = .ok marker 24 ∧
      (state.target.pair.manifest.mapM fun source =>
        readIntegrityManifestPrefixWith readManifest source.size) 0 = .ok state.target.pair.manifest manifestBytes ∧
      (match state.target.pair.manifest with
        | none => manifestBytes = 0
        | some bytes => ∃ manifest, Manifest.IntegrityCheckpoint.decode bytes = .ok manifest ∧
          (List.range manifest.header.runCount.toNat).mapM
            (state.published.durable manifest.header.generation) = some files ∧
          manifestBytes = 48 + 16 * manifest.header.runCount.toNat) ∧
      first ≤ state.target.range.watermark ∧
      selectWalSegmentReads (state.wal.segments.map WalSegment.first) state.target.range.watermark =
        some (first, (state.wal.readDescriptors state.target.range.watermark).map WalSegment.first) ∧
      let selectedWal := WalSegment.concatenate (state.wal.readDescriptors state.target.range.watermark)
      let replayWal := WAL.encode (state.history.drop state.target.range.watermark)
      selectedWal = WAL.encode (state.history.drop first) ∧
      selectedWal.size = (state.target.range.watermark - first) * frameSize + replayWal.size ∧
      manifestBytes + 24 + (files.map ByteArray.size).sum + selectedWal.size ≤
        manifestBytes + 24 + 16 * files.length + 32 * budgets.sum +
          (state.target.range.watermark - first) * frameSize + replayWal.size := by
  obtain ⟨watermark, _, marker, count, marked, decodedMarker, _⟩ :=
    DirectoryPublication.Bindings.walRange_accounting state.target.decoded
  obtain ⟨observesMarker, availableMarker⟩ := markerHealthy marker marked
  have readMarkerExact := readAcceptedMarker decodedMarker observesMarker availableMarker
  cases visible : state.target.pair.manifest with
  | none =>
    have noCheckpoint := checkpointAbsent (visible ▸ ready.resumed.selected)
    have zero : state.target.range.watermark = 0 := by
      simpa [visible, selectedCheckpointWatermark] using watermark.symm
    have chosen : state.wal.Selects state.target.pair := ready.walPair ▸ List.mem_cons_self
    obtain ⟨first, starts, _, addresses, _, payload⟩ := ready.layout.selects ready.valid chosen state.target.decoded
    have firstZero : first = 0 := by omega
    refine ⟨[], marker, first, 0, ?_, marked, readMarkerExact, rfl, rfl, starts, addresses, payload, ?_, ?_⟩
    · simp [noCheckpoint, PackedTable.empty]
    · rw [payload, firstZero, zero]
      simp
    · rw [payload, firstZero, zero]
      simp
  | some bytes =>
    obtain ⟨manifest, files, first, decoded, stored, exactFiles, fileCount, _, _, starts, addresses, payload,
      walBytes, payloadLimit⟩ := ready.selectedRecoveryPayload visible budgets length bounds
    obtain ⟨observesManifest, availableManifest, fits⟩ := manifestHealthy bytes visible
    have readManifestExact := readIntegrityManifestPrefixWith_accepted decoded observesManifest availableManifest fits
    obtain ⟨encoded, _, runCount⟩ := Manifest.IntegrityCheckpoint.decode_spec decoded
    have manifestSize : bytes.size = 48 + 16 * manifest.header.runCount.toNat := by
      rw [← encoded, Manifest.IntegrityCheckpoint.encode_size, runCount]
    refine ⟨files, marker, first, bytes.size, exactFiles, marked, readMarkerExact, ?_,
      ⟨manifest, decoded, stored, manifestSize⟩, starts, addresses, payload, walBytes, ?_⟩
    · simp [Option.mapM, Functor.map, EStateM.map, readManifestExact]
    · simpa only [fileCount, Nat.add_assoc] using Nat.add_le_add_left payloadLimit (bytes.size + 24)

end Alvoki.Storage.DiskSession
