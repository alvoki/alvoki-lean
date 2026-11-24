import Alvoki.Storage.Disk.LegacyWalRecovery
import Alvoki.Storage.Disk.MarkedDatabaseState

namespace Alvoki.WAL.Boundary
open Storage

/-- Effects reported by the locked Linux callbacks when adopting an existing
unmarked WAL. Only the selected durability branch is requested. A marker
report uses the ordinary staged replacement contract, including effect before
an error. Successful syncs settle the names and contents they cover. -/
structure LegacyOpenReports where
  repair : Publication.Step → RepairReport
  aligned : AlignedSyncReport
  marker : Publication.Step → RepairReport

def LegacyOpenReports.Succeeds (reports : LegacyOpenReports) (walSize selectedSize : Nat) : Prop :=
  (selectedSize < walSize → ∀ step, reports.repair step = .success) ∧
  (¬ selectedSize < walSize → reports.aligned = .success) ∧
  ∀ step, reports.marker step = .success

/-- Validate the existing unmarked WAL using the observed checkpoint and
the same optional file lookup order as the native open. -/
def legacyPreflight (checkpoint : Except String (Option (PackedTable × UInt64)))
    (marker wal : Except String (Option ByteArray)) : Except String (MarkedPreflight × UInt64) := do
  let checkpoint ← checkpoint
  let (base, generation) := checkpoint.getD (.empty, 0)
  withOpenWal marker wal id (fun _ => .error "expected an existing legacy WAL") fun boundary bytes => do
    if boundary.isSome then throw "expected an unmarked legacy WAL"
    let (selected, table) ← recoverLegacy base bytes
    return (⟨bytes, selected, table⟩, generation)

def legacyMarkerStep (bytes : ByteArray) (before : ReopenImage) (step : Publication.Step) :
    Option ReopenImage :=
  (before.directory.step .walBoundary bytes step).map
    fun directory => { before with directory }

/-- Interpret reports from the first marker's staged replacement. An
error can retain the state before or after the reported step. -/
def performLegacyMarker (report : Publication.Step → RepairReport) (bytes : ByteArray)
    (step : Publication.Step) : EStateM String ReopenImage Unit := fun before =>
  let updated := legacyMarkerStep bytes before step
  match report step with
  | .success =>
    match updated with
    | some after => .ok () after
    | none => .error "invalid legacy marker replacement" before
  | .failure message tookEffect => .error message (if tookEffect then updated.getD before else before)

/-- The existing-WAL, absent-marker branch of `DiskTable.openLocked`, with
observations from the shared checkpoint loader and WAL lookups. The model
uses the same durability decision as marked reopen before publishing the
first marker. The other open branches have their own models. -/
def runLegacyMarkedOpen (checkpoint : Except String (Option (PackedTable × UInt64)))
    (marker wal : Except String (Option ByteArray)) (reports : LegacyOpenReports) :
    EStateM String ReopenImage (PackedTable × UInt64 × Nat) :=
  match legacyPreflight checkpoint marker wal with
  | .error message => throw message
  | .ok (validated, generation) => do
    let table ← runMarkedReopen (.ok validated) reports.repair false reports.aligned
    unless validated.selected.size < UInt64.size do throw "WAL byte count is too large"
    Publication.run (performLegacyMarker reports.marker (encode validated.selected.size.toUInt64))
    return (table, generation, validated.selected.size)

private def afterLegacyMarker (before : ReopenImage) (bytes : ByteArray) : ReopenImage :=
  let bindings := before.directory.active.replace .walBoundary bytes
  { before with directory := ⟨bindings, [bindings], fun entry =>
      if entry = .walBoundary then none else before.directory.staged entry⟩ }

private theorem publishLegacyMarker_complete (before : ReopenImage) (bytes : ByteArray)
    (report : Publication.Step → RepairReport) (published : ∀ step, report step = .success) :
    Publication.run (performLegacyMarker report bytes) before = .ok () (afterLegacyMarker before bytes) := by
  rw [show report = fun _ => .success from funext published]
  let bindings := before.directory.active.replace .walBoundary bytes
  change EStateM.Result.ok () (⟨⟨bindings, [bindings], fun entry =>
    if entry = .walBoundary then none else
    if entry = .walBoundary then some (bytes, true) else
    if entry = .walBoundary then some (bytes, false) else before.directory.staged entry⟩,
    before.wal⟩ : ReopenImage) = _
  have cleared : (fun entry : DirectoryPublication.Entry =>
      if entry = .walBoundary then none else
      if entry = .walBoundary then some (bytes, true) else
      if entry = .walBoundary then some (bytes, false) else before.directory.staged entry) =
      fun entry => if entry = .walBoundary then none else before.directory.staged entry := by
    funext entry
    cases entry <;> rfl
  rw [cleared]
  rfl

/-- An accepted legacy WAL on the aligned path is already its own selected
prefix, so the synced active binding has the selected bytes. -/
theorem recoverLegacy_selected_eq_of_aligned {base table : PackedTable} {bytes selected : ByteArray}
    (recovered : recoverLegacy base bytes = .ok (selected, table))
    (aligned : ¬ selected.size < bytes.size) : selected = bytes := by
  obtain ⟨events, decoded, canonical, _⟩ := recoverLegacy_exact recovered
  rw [canonical, WAL.decodeOrdinals_reencode decoded] at aligned ⊢
  have bounded := Nat.div_mul_le_self bytes.size WAL.frameSize
  rw [ByteArray.size_extract, Nat.sub_zero, Nat.min_eq_left bounded] at aligned
  rw [Nat.le_antisymm bounded (Nat.le_of_not_gt aligned), ByteArray.extract_zero_size]

private theorem runLegacyMarkedOpen_success {before : ReopenImage} {loaded : Option (PackedTable × UInt64)}
    {bytes selected : ByteArray} {table : PackedTable} (reports : LegacyOpenReports)
    (recovered : recoverLegacy (loaded.getD (.empty, 0)).1 bytes = .ok (selected, table))
    (visible : before.wal.active = some bytes) (fits : selected.size < UInt64.size)
    (success : reports.Succeeds bytes.size selected.size) :
    ∃ after : ReopenImage,
      runLegacyMarkedOpen (.ok loaded) (.ok none) (.ok (some bytes)) reports before =
        .ok (table, (loaded.getD (.empty, 0)).2, selected.size) after ∧
      after.directory.active = before.directory.active.replace .walBoundary (encode selected.size.toUInt64) ∧
      after.directory.crashImages = [after.directory.active] ∧
      after.wal.active = some selected ∧ after.wal.crashImages = [after.wal.active] := by
  let validated : MarkedPreflight := ⟨bytes, selected, table⟩
  have preflight : legacyPreflight (.ok loaded) (.ok none) (.ok (some bytes)) =
      .ok (validated, (loaded.getD (.empty, 0)).2) := by
    simp [legacyPreflight, withOpenWal, Option.mapM, Bind.bind, Except.bind,
      Pure.pure, Except.pure, recovered, validated]
  let durable : ReopenImage := if selected.size < bytes.size then
      ⟨before.directory.syncDirectory, .settled (some selected)⟩ else before.syncDirectory
  have finished : runMarkedReopen (.ok validated) reports.repair false reports.aligned before =
      .ok table durable :=
    runMarkedReopen_durability_success validated reports.repair reports.aligned before success.1 success.2.1
  let marker := encode selected.size.toUInt64
  let after := afterLegacyMarker durable marker
  refine ⟨after, ?_, ?_, rfl, ?_, ?_⟩
  · have markerRun := publishLegacyMarker_complete durable marker reports.marker success.2.2
    simp only [runLegacyMarkedOpen, preflight, Bind.bind, EStateM.bind, finished,
      show validated.selected = selected from rfl, fits, ite_true, Pure.pure, EStateM.pure]
    erw [markerRun]
  · by_cases shorter : selected.size < bytes.size <;>
      simp [after, afterLegacyMarker, durable, shorter, ReopenImage.syncDirectory,
        DirectoryPublication.Image.syncDirectory, marker]
  · by_cases shorter : selected.size < bytes.size
    · simp [after, afterLegacyMarker, durable, shorter, Publication.Image.settled]
    · simpa [after, afterLegacyMarker, durable, shorter, ReopenImage.syncDirectory] using
        visible.trans (congrArg some (recoverLegacy_selected_eq_of_aligned recovered shorter).symm)
  · by_cases shorter : selected.size < bytes.size <;>
      simp [after, afterLegacyMarker, durable, shorter, ReopenImage.syncDirectory, Publication.Image.settled]

/-- Successful adoption of the actual unmarked WAL establishes the invariant
used by subsequent marked writes and recovery sessions. The checkpoint
witness describes the bytes read under the lock, including manifest absence.
If present, its logical state must represent the covered prefix of the WAL.
The reports are the primitive filesystem effect contract for this open. -/
theorem legacyMarkedOpen_ready {before : ReopenImage} (checkpoint : FixedMarkedCheckpoint)
    (manifest : before.directory.active.manifest = checkpoint.manifest)
    (checkpointReads : CheckpointReadObservations checkpoint.image checkpoint.manifest)
    (walReads : MarkedWalReads before) {loaded : Option (PackedTable × UInt64)}
    (loadedResult : checkpointReads.result = .ok loaded)
    (unmarked : walReads.marker = .ok none) {bytes selected : ByteArray} {table : PackedTable}
    (readWal : walReads.wal = .ok (some bytes))
    (recovered : recoverLegacy (loaded.getD (.empty, 0)).1 bytes = .ok (selected, table))
    {history : List WAL.Write} (decoded : WAL.decodeOrdinals bytes = .ok history)
    (covered : checkpoint.covered = history.take checkpoint.table.committed.toNat)
    (checkpointHistory : RepresentsWalHistory checkpoint.covered checkpoint.model)
    (fits : selected.size < UInt64.size) (reports : LegacyOpenReports)
    (success : reports.Succeeds bytes.size selected.size) :
    ∃ next : MarkedDatabaseState,
      runLegacyMarkedOpen checkpointReads.result walReads.marker walReads.wal reports before =
        .ok (next.writer.table, next.generation, next.writer.walBytes) next.writer.image ∧
      next.checkpoint = { checkpoint with
        image := { checkpoint.image with manifest := next.writer.image.directory.project .manifest } } ∧
      next.writer.table = table ∧ next.generation = (loaded.getD (.empty, 0)).2 ∧
      next.writer.history = history ∧ next.writer.walBytes = selected.size ∧
      MarkedWriterState.observeReopen next.writer.table next.writer.image = some next.writer ∧
      next.Valid ∧ next.writer.table.pins.active = [] := by
  obtain ⟨after, ran, active, durableDirectory, walActive, walDurable⟩ :=
    runLegacyMarkedOpen_success reports recovered (walReads.walVisible _ readWal) fits success
  obtain ⟨actual, abstract, model, readHistory, encoded, count, _, replayed, refined, data, clock, floor, pins⟩ :=
    checkpoint.written.recoverLegacy_refines checkpoint.accepted checkpointReads loadedResult
      checkpoint.represents recovered
  have actualHistory := Except.ok.inj (readHistory.symm.trans decoded)
  subst actual
  obtain ⟨_, _, _, _, _, replay⟩ := recoverLegacy_exact recovered
  have loader := checkpoint.written.loaded_observation checkpoint.accepted checkpointReads loadedResult
  have loadedTable : checkpoint.manifest.elim (.ok PackedTable.empty)
      (fun bytes => Manifest.decode bytes >>= fun header => loadRunSet header checkpoint.files) =
        .ok (loaded.getD (.empty, 0)).1 := by
    cases visible : checkpoint.manifest <;> rw [visible] at loader <;> exact loader
  have bounded := checkpoint.written.recoverSelected_rowBounds (by rw [loadedTable]; exact replay)
  let fixed : FixedMarkedCheckpoint := { checkpoint with
    image := { checkpoint.image with manifest := after.directory.project .manifest } }
  let writer : MarkedWriterState := ⟨table, selected.size, after, history⟩
  have ordered := WAL.decodeOrdinals_sound decoded
  have settled : after.SettledFor fixed.manifest history := by
    refine ⟨?_, durableDirectory, walActive.trans (congrArg some encoded), walDurable⟩
    rw [active, ← encoded]
    simp only [fixed, DirectoryPublication.Bindings.replace, manifest]
  have represented : RepresentsWalHistory history abstract := by
    rw [← List.take_append_drop checkpoint.table.committed.toNat history, ← covered]
    exact checkpointHistory.append replayed
  have representedModel := represented.preserve clock (UInt64.le_of_eq floor.symm)
    (refined.rowsBounded bounded) (fun _ _ _ => by rw [data])
  refine ⟨⟨writer, fixed, (loaded.getD (.empty, 0)).2⟩, ?_, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · rw [loadedResult, unmarked, readWal]
    exact ran
  · simp [writer, MarkedWriterState.observeReopen, walActive, encoded,
      WAL.decodeOrdinals_encode _ ordered, Except.toOption]
  · exact ⟨⟨settled, ordered, count.symm, congrArg ByteArray.size encoded, fits, bounded⟩,
      ⟨_, by rw [covered]; exact (List.take_append_drop ..).symm⟩,
      ⟨model, refined, representedModel⟩, checkpointHistory,
      checkpoint.written.loaded_generation checkpoint.accepted checkpointReads loadedResult⟩
  · rw [refined.pins, pins]

end Alvoki.WAL.Boundary
