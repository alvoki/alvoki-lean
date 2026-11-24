import Alvoki.Storage.Disk.VersionedReadyWriter

namespace Alvoki.WAL.Boundary
open Storage CheckpointPublication Manifest

/-- A failed WAL submission leaves the same raw manifest selected, and the
admitted retries select either the acknowledged history or its extension by
the one submitted frame. These facts do not use a checkpoint decoder. -/
private theorem MarkedWriterState.selectAfterWriteError {writer : MarkedWriterState}
    {manifest : Option ByteArray} (ready : writer.ReadyFor manifest)
    {key : UInt64} {value : Option UInt64} {event : WAL.Write} {preparedTable : PackedTable}
    (prepared : prepareWrite writer.table key value = some (event, preparedTable))
    (fits : writer.walBytes + WAL.frameSize < UInt64.size)
    {effects : WriteEffects} {cut before : ReopenImage}
    (failed : runWriteEffectsFrom writer.history event effects writer.image = .error () cut)
    (attempts : MarkedReopenAttempts cut before) :
    ∃ contents events,
      before.directory.active.manifest = manifest ∧
      before.directory.active.walBoundary = some (encode (WAL.encode events).size.toUInt64) ∧
      before.wal.active = some contents ∧
      select (WAL.encode events).size.toUInt64 contents = .ok (WAL.encode events) ∧
      (events = writer.history ∨ events = writer.history ++ [event]) ∧
      WAL.OrdinalsFrom 1 events ∧ (WAL.encode events).size < UInt64.size := by
  let stagedMarker := writer.image.directory.staged .walBoundary
  let stagedManifest := writer.image.directory.staged .manifest
  let stagedWal := writer.image.wal.staged
  let physical := writeFilesAfter (runWriteEffects writer.history event effects stagedMarker)
  let initial := physical.reopenImage writer.history manifest stagedManifest stagedWal
  have openedCut : initial = cut := runWriteEffectsFrom_failed_image ready.settled failed
  obtain ⟨_, _, orderedNext, _, nextSize⟩ := prepareWrite_extends_history ready.ordered ready.count prepared
  have extendedFits : (WAL.encode (writer.history ++ [event])).size < UInt64.size := by
    rwa [nextSize, ← ready.length]
  have path := (openedCut.symm ▸ attempts : MarkedReopenAttempts initial before).toRetry
    (writeEffects_reopenMarkerBound writer.history event effects manifest extendedFits)
  have chosen := path.chosen_pair_from_initial (List.mem_cons_self ..)
  have visible := physical.reopenImage_manifest_eq writer.history manifest chosen
  have cuts := runWriteEffects_hasWriteCuts writer.history event effects manifest stagedMarker stagedManifest stagedWal
  obtain ⟨marker, contents, events, markerAt, encoded, walAt, selected, retained⟩ :=
    selectWriteCutAfterReopenRetry path (List.mem_cons_self ..) (List.mem_cons_self ..)
      (physical.reopenImage_crashWal_nonempty writer.history manifest stagedManifest stagedWal) extendedFits cuts
  refine ⟨contents, events, visible, markerAt.trans (congrArg some encoded), walAt, selected, retained, ?_⟩
  rcases retained with rfl | rfl
  · exact ⟨ready.ordered, ready.length ▸ ready.fits⟩
  · exact ⟨orderedNext, extendedFits⟩

/-- The actual failed write image retains a bounded active marker and bounded
crash choices, as needed to thread marked reopen failures. -/
theorem MarkedWriterState.markerBoundAfterWriteError {writer : MarkedWriterState}
    {manifest : Option ByteArray} (ready : writer.ReadyFor manifest)
    {event : WAL.Write} {effects : WriteEffects} {cut : ReopenImage}
    (fits : (WAL.encode (writer.history ++ [event])).size < UInt64.size)
    (failed : runWriteEffectsFrom writer.history event effects writer.image = .error () cut) :
    MarkerBound cut.directory := by
  rw [← runWriteEffectsFrom_failed_image ready.settled failed]
  exact writeEffects_reopenMarkerBound writer.history event effects manifest fits

/-- Write retries leave the predecessor's raw manifest selected. -/
theorem MarkedWriterState.manifestAfterWriteError {writer : MarkedWriterState}
    {manifest : Option ByteArray} (ready : writer.ReadyFor manifest)
    {key : UInt64} {value : Option UInt64} {event : WAL.Write} {preparedTable : PackedTable}
    (prepared : prepareWrite writer.table key value = some (event, preparedTable))
    (fits : writer.walBytes + WAL.frameSize < UInt64.size)
    {effects : WriteEffects} {cut before : ReopenImage}
    (failed : runWriteEffectsFrom writer.history event effects writer.image = .error () cut)
    (attempts : MarkedReopenAttempts cut before) : before.directory.active.manifest = manifest := by
  obtain ⟨_, _, selected, _⟩ := MarkedWriterState.selectAfterWriteError ready prepared fits failed attempts
  exact selected

/-- A ready v1 or v2 writer can recover after an uncertain WAL submission.
The same held lock supplies the exact versioned checkpoint bytes and WAL
observations. The required repair or aligned sync completes as reported,
leaving a ready writer for precisely the marker-selected history. -/
theorem ObservedMarkedState.VersionedReady.reopenAfterWriteErrorWithLock
    {state : ObservedMarkedState} (valid : state.VersionedReady)
    {key : UInt64} {value : Option UInt64} {event : WAL.Write} {preparedTable : PackedTable}
    (prepared : prepareWrite state.writer.table key value = some (event, preparedTable))
    (fits : state.writer.walBytes + WAL.frameSize < UInt64.size)
    {effects : WriteEffects} {cut before : ReopenImage}
    (failed : runWriteEffectsFrom state.writer.history event effects state.writer.image = .error () cut)
    (attempts : MarkedReopenAttempts cut before)
    {directory : DiskDirectory} {descriptor : Nat} {owners : DiskSession.LockOwners}
    (acquisition : DiskSession.TryLockObserves owners directory (.ok true))
    {paths : OpenPathReadReports}
    (observes : (owners.set (directory.file .lock) (some descriptor)).Owns directory descriptor →
      paths.ObservesVersioned directory before state.durable)
    (manifestRead : ∃ result, paths.readOptional (directory.file .manifest) = .ok result)
    (runReads : ∀ bytes selected, before.directory.active.manifest = some bytes →
      VersionedCheckpoint.decode bytes = .ok selected → ∀ index, index < selected.header.runCount.toNat →
        ∃ payload, paths.readBin (directory.file (.run selected.header.generation index)) = .ok payload)
    (markerRead : ∃ result, paths.readOptional (directory.file .walBoundary) = .ok result)
    (walRead : ∃ result, paths.readOptional (directory.file .wal) = .ok result)
    (report : Publication.Step → RepairReport) (aligned : AlignedSyncReport)
    (durability : ∀ marker contents length,
      (paths.readOptional (directory.file .walBoundary)).mapError toString = .ok (some marker) →
      (paths.readOptional (directory.file .wal)).mapError toString = .ok (some contents) →
      decode marker = .ok length →
      if length.toNat < contents.size then (∀ step, report step = .success) else aligned = .success)
    (unlock : DiskSession.UnlockReport) (cause : String → IO.Error) :
    let heldOwners := owners.set (directory.file .lock) (some descriptor)
    let held : heldOwners.Owns directory descriptor := by
      simp [heldOwners, DiskSession.LockOwners.Owns, DiskSession.LockOwners.set]
    let checkpointReads := VersionedCheckpointFileReads.ofLockedPaths held observes
    let walReads := (observes held).toObserves.walReads
    let reopened := runSharedMarkedOpen checkpointReads.result walReads.marker walReads.wal report aligned before
    let reopenedIntegrity := runSharedMarkedOpen
      (readIntegrityCheckpoint checkpointReads.readManifest checkpointReads.readRun id)
      walReads.marker walReads.wal report aligned before
    ∃ next : ObservedMarkedState,
      DiskSession.runLockedMarkedOpen directory descriptor (.ok true) unlock cause reopened owners =
        .ok ((next.writer.table, next.generation, next.writer.walBytes), next.writer.image) heldOwners ∧
      owners (directory.file .lock) = none ∧ heldOwners.Owns directory descriptor ∧
      MarkedWriterState.observeReopen next.writer.table next.writer.image = some next.writer ∧
      next.VersionedReady ∧ next.generation = state.generation ∧ next.durable = state.durable ∧
      next.writer.image.directory.active.manifest = state.writer.image.directory.active.manifest ∧
      (next.writer.history = state.writer.history ∨ next.writer.history = state.writer.history ++ [event]) ∧
      next.writer.table.pins.active = [] ∧
      before.directory.active.walBoundary = some (encode (WAL.encode next.writer.history).size.toUInt64) ∧
      (state.HasIntegrityManifest →
        DiskSession.runLockedMarkedOpen directory descriptor (.ok true) unlock cause reopenedIntegrity owners =
          .ok ((next.writer.table, next.generation, next.writer.walBytes), next.writer.image) heldOwners ∧
        next.HasIntegrityManifest) := by
  intro heldOwners held checkpointReads walReads reopened reopenedIntegrity
  obtain ⟨contents, events, manifest, marker, wal, selection, retained, ordered, bytesFit⟩ :=
    MarkedWriterState.selectAfterWriteError valid.ready prepared fits failed attempts
  have accepted : state.publicationInput.AcceptsVersioned events.length.toUInt64
      (CheckpointRepresentsPrefix events) before.directory.active.manifest := by
    rw [manifest]
    rcases retained with rfl | rfl
    · exact valid.selected
    · exact state.publicationInput.acceptsVersioned_extend_history valid.selected bytesFit
  have manifestObserved := VersionedCheckpointFileReads.ofLockedPaths_manifest_success held observes manifestRead
  have runsObserved bytes selected visible decoded index within :=
    (runReads bytes selected visible decoded index within).imp
      (fun _ => VersionedCheckpointFileReads.ofLockedPaths_run_success held observes)
  obtain ⟨loaded, table, model, loadedCheckpoint, decodedGeneration, replayed, bounded,
    refined, represented, freshPins⟩ :=
    checkpointReads.replays_history accepted manifestObserved runsObserved bytesFit ordered
  have actualLoaded : checkpointReads.result = .ok loaded := loadedCheckpoint
  let length := (WAL.encode events).size.toUInt64
  have markerObserved : walReads.marker = .ok (some (encode length)) :=
    (observedOptional_success markerRead (fun value read => (walReads.markerVisible value read).symm)).trans
      (congrArg Except.ok marker)
  have walObserved : walReads.wal = .ok (some contents) :=
    (observedOptional_success walRead (fun value read => (walReads.walVisible value read).symm)).trans
      (congrArg Except.ok wal)
  have marked : walReads.marker ≠ .ok none := by rw [markerObserved]; simp
  let reads := MarkedReopenReads.mk walReads
    (checkpointReads.result.map fun result => (result.getD (.empty, 0)).1)
  have baseRead : reads.checkpoint = .ok (loaded.getD (.empty, 0)).1 := by
    change checkpointReads.result.map (fun result => (result.getD (.empty, 0)).1) = _
    rw [actualLoaded]
    rfl
  let chosen : MarkedPreflight := ⟨contents, WAL.encode events, table⟩
  have preflight : reads.preflight = .ok chosen :=
    reads.preflight_succeeds baseRead markerObserved walObserved (decode_encode length) selection replayed
  have reports := durability (encode length) contents length markerObserved walObserved (decode_encode length)
  have bytes : (WAL.encode events).size = length.toNat := select_size selection
  have repairs (shorter : chosen.selected.size < chosen.contents.size) :
      ∀ step, report step = .success := by
    change (WAL.encode events).size < contents.size at shorter
    rw [bytes] at shorter
    simpa only [ite_eq_left shorter] using reports
  have syncs (full : ¬ chosen.selected.size < chosen.contents.size) : aligned = .success := by
    change ¬ (WAL.encode events).size < contents.size at full
    rw [bytes] at full
    simpa only [ite_eq_right full] using reports
  let after := if chosen.selected.size < chosen.contents.size then
    (⟨before.directory.syncDirectory, .settled (some chosen.selected)⟩ : ReopenImage)
    else before.syncDirectory
  have installed : runMarkedReopen reads.preflight report false aligned before = .ok table after := by
    rw [preflight]
    exact runMarkedReopen_durability_success chosen report aligned before repairs syncs
  have directorySettled : after.directory = before.directory.syncDirectory := by
    unfold after
    split <;> rfl
  obtain ⟨walActive, walChoices⟩ := reads.success_selectedWal preflight installed
  have nextManifest : after.directory.active.manifest = state.writer.image.directory.active.manifest := by
    rw [directorySettled]
    exact manifest
  have settled : after.SettledFor state.writer.image.directory.active.manifest events := by
    refine ⟨?_, ?_, walActive, ?_⟩
    · rw [directorySettled]
      change (⟨before.directory.active.manifest, before.directory.active.walBoundary⟩ :
        DirectoryPublication.Bindings) = ⟨_, _⟩
      rw [manifest, marker]
    · rw [directorySettled]; rfl
    · rwa [walActive]
  have native : reopened = .ok (table, (loaded.getD (.empty, 0)).2, (WAL.encode events).size) after := by
    change runSharedMarkedOpen checkpointReads.result walReads.marker walReads.wal report aligned before = _
    rw [runSharedMarkedOpen_eq _ _ _ marked]
    change (match runMarkedReopen reads.preflight report false aligned before with
      | .error message cut => EStateM.Result.error message cut
      | .ok table cut => .ok (table, ((checkpointReads.result.toOption.getD none).getD (.empty, 0)).2,
        (reads.preflight.toOption.map (fun result : MarkedPreflight => result.selected.size)).getD 0) cut) = _
    rw [installed, actualLoaded, preflight]
    rfl
  have generation : (loaded.getD (.empty, 0)).2 = state.generation := by
    rw [manifest] at decodedGeneration
    exact Except.ok.inj (decodedGeneration.symm.trans valid.generationMatches)
  let writer : MarkedWriterState := ⟨table, (WAL.encode events).size, after, events⟩
  have count : events.length = table.committed.toNat := by rw [refined.committed, represented.committed_count]
  have ready : writer.ReadyFor state.writer.image.directory.active.manifest :=
    ⟨settled, ordered, count, rfl, bytesFit, bounded⟩
  have nextReady : (state.withWriter writer).VersionedReady := by
    refine ⟨nextManifest.symm ▸ ready, ⟨model, refined, represented⟩, ?_, ?_⟩
    · change state.publicationInput.AcceptsVersioned events.length.toUInt64
        (CheckpointRepresentsPrefix events) after.directory.active.manifest
      rw [nextManifest, ← manifest]
      exact accepted
    · change ((after.directory.active.manifest.mapM fun bytes =>
        (VersionedCheckpoint.decode bytes).map (·.header.generation)).map (·.getD 0) : Except String UInt64) = _
      rw [nextManifest]
      exact valid.generationMatches
  have locked : DiskSession.runLockedMarkedOpen directory descriptor (.ok true) unlock cause reopened owners =
      .ok ((table, state.generation, (WAL.encode events).size), after) heldOwners := by
    rw [native, generation]
    rfl
  have previous := (DiskSession.runOpen_success acquisition locked).1
  refine ⟨state.withWriter writer, locked, previous, held, MarkedWriterState.observeReopen_ready ready,
    nextReady, rfl, rfl, nextManifest, retained, freshPins, marker, ?_⟩
  intro integrity
  have strictRead : readIntegrityCheckpoint checkpointReads.readManifest checkpointReads.readRun id =
      checkpointReads.result := checkpointReads.integrityResult_eq manifestObserved
        (fun bytes present => integrity bytes (manifest.symm.trans present))
  have strictReopen : reopenedIntegrity = reopened := by
    change runSharedMarkedOpen (readIntegrityCheckpoint checkpointReads.readManifest checkpointReads.readRun id)
      walReads.marker walReads.wal report aligned before =
      runSharedMarkedOpen checkpointReads.result walReads.marker walReads.wal report aligned before
    rw [strictRead]
  exact ⟨strictReopen.symm ▸ locked, integrity.ofSameManifest nextManifest⟩

/-- A failed write cannot select a different checkpoint format. Substitution
of this equality into the locked recovery result uses the deployed v2-only
reader on the genuine path reports, including for a fresh database. -/
theorem ObservedMarkedState.VersionedReady.writeError_checkpointReader_eq_integrity
    {state : ObservedMarkedState} (valid : state.VersionedReady)
    (integrity : state.HasIntegrityManifest)
    {key : UInt64} {value : Option UInt64} {event : WAL.Write} {preparedTable : PackedTable}
    (prepared : prepareWrite state.writer.table key value = some (event, preparedTable))
    (fits : state.writer.walBytes + WAL.frameSize < UInt64.size)
    {effects : WriteEffects} {cut before : ReopenImage}
    (failed : runWriteEffectsFrom state.writer.history event effects state.writer.image = .error () cut)
    (attempts : MarkedReopenAttempts cut before)
    (reads : VersionedCheckpointFileReads state.durable before.directory.active.manifest)
    (manifestRead : reads.readManifest = .ok before.directory.active.manifest) :
    readIntegrityCheckpoint reads.readManifest reads.readRun id = reads.result := by
  obtain ⟨_, _, visible, _⟩ := MarkedWriterState.selectAfterWriteError valid.ready prepared fits failed attempts
  exact reads.integrityResult_eq manifestRead (fun bytes binding => integrity bytes (visible.symm.trans binding))

end Alvoki.WAL.Boundary
