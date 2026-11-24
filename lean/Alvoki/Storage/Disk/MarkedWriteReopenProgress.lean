import Alvoki.Storage.Disk.MarkedOpenControl

namespace Alvoki.WAL.Boundary

open Storage

/-- The shared native open completes after an ambiguous write and admitted
retries when the selected file reads and the required durability steps
succeed. The installed bytes and table cover the old WAL or that WAL with
the one prepared frame. The checkpoint remains the fixed durable checkpoint. -/
theorem reopenAfterWriteError_completes {writer : MarkedWriterState}
    (checkpoint : FixedMarkedCheckpoint) {pending : List WAL.Write}
    (ready : writer.ReadyFor checkpoint.manifest)
    (history : writer.history = checkpoint.covered ++ pending)
    {key : UInt64} {value : Option UInt64} {event : WAL.Write} {next : PackedTable}
    (prepared : prepareWrite writer.table key value = some (event, next))
    (fits : writer.walBytes + WAL.frameSize < UInt64.size)
    {effects : WriteEffects} {cut before : ReopenImage}
    (failed : runWriteEffectsFrom writer.history event effects writer.image = .error () cut)
    (attempts : MarkedReopenAttempts cut before)
    (checkpointReads : CheckpointReadObservations checkpoint.image before.directory.active.manifest)
    (walReads : MarkedWalReads before)
    (manifestRead : checkpointReads.readManifest = .ok before.directory.active.manifest)
    (runReads : ∀ bytes header, before.directory.active.manifest = some bytes →
      Manifest.decode bytes = .ok header → ∀ index, index < header.runCount.toNat →
        ∃ payload, checkpointReads.readRun header.generation index = .ok payload)
    (markerRead : walReads.marker = .ok before.directory.active.walBoundary)
    (walRead : walReads.wal = .ok before.wal.active)
    (report : Publication.Step → RepairReport) (aligned : AlignedSyncReport)
    (durability : ∀ marker contents length, walReads.marker = .ok (some marker) →
      walReads.wal = .ok (some contents) → decode marker = .ok length →
      if length.toNat < contents.size then (∀ step, report step = .success) else aligned = .success) :
    ∃ events table generation after,
      runSharedMarkedOpen checkpointReads.result walReads.marker walReads.wal report aligned before =
        .ok (table, generation, (WAL.encode events).size) after ∧
      ((checkpoint.manifest.mapM fun bytes => (Manifest.decode bytes).map (·.generation)).map
        (·.getD 0) : Except String UInt64) = .ok generation ∧
      after.SettledFor checkpoint.manifest events ∧
      (events = writer.history ∨ events = writer.history ++ [event]) ∧
      table.committed.toNat = events.length ∧ before.directory.active.walBoundary ≠ none := by
  let old := checkpoint.covered ++ pending
  let stagedMarker := writer.image.directory.staged .walBoundary
  let stagedManifest := writer.image.directory.staged .manifest
  let stagedWal := writer.image.wal.staged
  let physical := writeFilesAfter (runWriteEffects old event effects stagedMarker)
  have cutImage : physical.reopenImage old checkpoint.manifest stagedManifest stagedWal = cut := by
    simpa only [physical, old, ← history] using runWriteEffectsFrom_failed_image ready.settled failed
  have retry : MarkedReopenAttempts (physical.reopenImage old checkpoint.manifest stagedManifest stagedWal) before :=
    cutImage.symm ▸ attempts
  have ordered : WAL.OrdinalsFrom 1 old := by simpa only [old, ← history] using ready.ordered
  have clock : old.length = writer.table.committed.toNat := by simpa only [old, ← history] using ready.count
  have size : writer.walBytes = (WAL.encode old).size := by simpa only [old, ← history] using ready.length
  obtain ⟨_, _, _, _, nextSize⟩ := prepareWrite_extends_history ordered clock prepared
  have extendedFits : (WAL.encode (old ++ [event])).size < UInt64.size := by
    rwa [nextSize, ← size]
  have path := retry.toRetry (writeEffects_reopenMarkerBound old event effects checkpoint.manifest extendedFits)
  have visibleManifest := physical.reopenImage_manifest_eq old checkpoint.manifest
    (path.chosen_pair_from_initial (List.mem_cons_self ..))
  obtain ⟨marker, contents, events, base, table, _, markerAt, markerEncoding, walAt,
    loadedBase, selected, recovered, selectedHistory, _, count, _⟩ :=
    recoverPreparedWriteAfterReopenAttempts prepared ordered clock size fits effects retry
      (pair := before.directory.active) (walBinding := before.wal.active)
      (List.mem_cons_self ..) (List.mem_cons_self ..) checkpoint.written checkpoint.represents checkpoint.watermark
  have durable := checkpoint.written.ordered_durable_runs checkpoint.accepted
  obtain ⟨loaded, checkpointLoaded, sameBase⟩ :=
    checkpointReads.completes manifestRead runReads (visibleManifest.symm ▸ durable) loadedBase
  let reads := MarkedReopenReads.mk walReads
    (checkpointReads.result.map fun loaded => (loaded.getD (.empty, 0)).1)
  have checkpointRead : reads.checkpoint = .ok base := by
    change checkpointReads.result.map (fun result => (result.getD (.empty, 0)).1) = .ok base
    rw [checkpointLoaded]
    exact congrArg Except.ok sameBase
  have markerObserved := markerRead.trans (congrArg Except.ok markerAt)
  have walObserved := walRead.trans (congrArg Except.ok walAt)
  let length := (WAL.encode events).size.toUInt64
  have decoded : decode marker = .ok length := by rw [markerEncoding, decode_encode]
  have selection : select length contents = .ok (WAL.encode events) := by rwa [decoded] at selected
  let validated : MarkedPreflight := ⟨contents, WAL.encode events, table⟩
  have preflight : reads.preflight = .ok validated :=
    reads.preflight_succeeds checkpointRead markerObserved walObserved decoded selection recovered
  have bytes := select_size selection
  have reports := durability marker contents length markerObserved walObserved decoded
  have repaired (shorter : validated.selected.size < validated.contents.size) :
      ∀ step, report step = .success := by
    change (WAL.encode events).size < contents.size at shorter
    rw [bytes] at shorter
    simpa only [ite_eq_left shorter] using reports
  have synced (full : ¬ validated.selected.size < validated.contents.size) : aligned = .success := by
    change ¬ (WAL.encode events).size < contents.size at full
    rw [bytes] at full
    simpa only [ite_eq_right full] using reports
  let after := if validated.selected.size < validated.contents.size then
      (⟨before.directory.syncDirectory, .settled (some validated.selected)⟩ : ReopenImage)
    else before.syncDirectory
  have opened : runMarkedReopen reads.preflight report false aligned before = .ok table after := by
    rw [preflight]
    exact runMarkedReopen_durability_success validated report aligned before repaired synced
  have directory : after.directory = before.directory.syncDirectory := by
    unfold after
    split <;> rfl
  obtain ⟨walActive, walChoices⟩ := reads.success_selectedWal preflight opened
  have isMarked : before.directory.active.walBoundary ≠ none := by rw [markerAt]; simp
  have nativeOpened : runSharedMarkedOpen checkpointReads.result walReads.marker walReads.wal report aligned before =
      .ok (table, (loaded.getD (.empty, 0)).2, (WAL.encode events).size) after := by
    rw [walReads.runSharedMarkedOpen_eq isMarked checkpointReads report aligned]
    change (match runMarkedReopen reads.preflight report false aligned before with
      | .error message cut => EStateM.Result.error message cut
      | .ok table cut => EStateM.Result.ok (table, ((checkpointReads.result.toOption.getD none).getD (.empty, 0)).2,
        (reads.preflight.toOption.map (fun result : MarkedPreflight => result.selected.size)).getD 0) cut) = _
    rw [opened, checkpointLoaded, preflight]
    rfl
  have installedGeneration := CheckpointForRecovery.loaded_generation
    (visibleManifest.symm ▸ checkpoint.written) (visibleManifest.symm ▸ checkpoint.accepted)
    checkpointReads checkpointLoaded
  rw [visibleManifest] at installedGeneration
  have metadata : after.directory.active =
      ⟨checkpoint.manifest, some (encode (WAL.encode events).size.toUInt64)⟩ := by
    rw [directory]
    change (⟨before.directory.active.manifest, before.directory.active.walBoundary⟩ :
      DirectoryPublication.Bindings) = ⟨_, _⟩
    rw [visibleManifest, markerAt, markerEncoding]
  have onlyMetadata : after.directory.crashImages = [after.directory.active] := by rw [directory]; rfl
  refine ⟨events, table, _, after, nativeOpened, installedGeneration,
    ⟨metadata, onlyMetadata, walActive, walActive.symm ▸ walChoices⟩, ?_, count, isMarked⟩
  simpa only [history] using selectedHistory

end Alvoki.WAL.Boundary
