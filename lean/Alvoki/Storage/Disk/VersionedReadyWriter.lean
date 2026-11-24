import Alvoki.Storage.Disk.FirstVersionedCheckpoint

namespace Alvoki.WAL.Boundary
open Storage CheckpointPublication Manifest

/-- The ready writer's selected raw manifest binds exact ordered bytes in its
kept run map. Its live table represents the whole WAL, and the selected
checkpoint represents the prefix covered by its own watermark. -/
structure ObservedMarkedState.VersionedReady (state : ObservedMarkedState) : Prop where
  ready : state.writer.ReadyFor state.writer.image.directory.active.manifest
  live : ∃ model, state.writer.table.Refines model ∧ RepresentsWalHistory state.writer.history model
  selected : state.publicationInput.AcceptsVersioned state.writer.history.length.toUInt64
    (CheckpointRepresentsPrefix state.writer.history) state.writer.image.directory.active.manifest
  generationMatches : ((state.writer.image.directory.active.manifest.mapM fun bytes =>
    (VersionedCheckpoint.decode bytes).map (·.header.generation)).map (·.getD 0) : Except String UInt64) =
      .ok state.generation

private theorem ObservedMarkedState.VersionedReady.crashChoice {state : ObservedMarkedState}
    (valid : state.VersionedReady) :
    state.publicationInput.manifest.crashImages = [state.publicationInput.manifest.active] := by
  simp [ObservedMarkedState.publicationInput, DirectoryPublication.Image.project, valid.ready.settled.2.1]

/-- A ready writer has settled the selected raw manifest. All possible crash
bindings therefore use the same accepted run map. -/
theorem ObservedMarkedState.VersionedReady.validPublicationInput {state : ObservedMarkedState}
    (valid : state.VersionedReady) :
    state.publicationInput.ValidVersioned state.writer.history.length.toUInt64
      (CheckpointRepresentsPrefix state.writer.history) := by
  refine ⟨by simp [valid.crashChoice], valid.selected, ?_⟩
  intro candidate survives
  rw [valid.crashChoice] at survives
  exact (List.mem_singleton.mp survives).symm ▸ valid.selected

/-- The actual ready output of a versioned reopen uses the kept run map from
the reported checkpoint and the raw manifest selected by the reopen. -/
theorem ObservedMarkedState.VersionedReady.ofCheckpointReopen
    {initial published : Image} {before reopen : ReopenImage} {manifest : Option ByteArray}
    {history : List WAL.Write} {table : PackedTable} {generation : UInt64} {model : Sequential.SnapshotTable UInt64}
    (checkpoints : VersionedRetry history.length.toUInt64 (CheckpointRepresentsPrefix history) initial published)
    (valid : initial.ValidVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history))
    (settled : before.SettledFor manifest history) (fits : (WAL.encode history).size < UInt64.size)
    (attempts : MarkedReopenAttempts (published.markedReopenImage before) reopen)
    (ready : (⟨table, (WAL.encode history).size, reopen.syncDirectory, history⟩ :
      MarkedWriterState).ReadyFor reopen.directory.active.manifest)
    (generationMatches : ((reopen.directory.active.manifest.mapM fun bytes =>
      (VersionedCheckpoint.decode bytes).map (·.header.generation)).map (·.getD 0) : Except String UInt64) =
        .ok generation)
    (refines : table.Refines model) (represented : RepresentsWalHistory history model) :
    (⟨⟨table, (WAL.encode history).size, reopen.syncDirectory, history⟩, generation, published.durable⟩ :
      ObservedMarkedState).VersionedReady := by
  let writer : MarkedWriterState := ⟨table, (WAL.encode history).size, reopen.syncDirectory, history⟩
  let state : ObservedMarkedState := ⟨writer, generation, published.durable⟩
  have selected := (checkpoints.markedReadInputs valid settled fits attempts).1
  have same : state.writer.image.directory.active.manifest = reopen.directory.active.manifest := by
    have active := congrArg DirectoryPublication.Bindings.manifest ready.settled.1
    exact active
  refine ⟨same.symm ▸ ready, ⟨model, refines, represented⟩, ?_, same.symm ▸ generationMatches⟩
  rw [same]
  exact selected

/-- Extending the WAL cannot change the prefix covered by a selected
checkpoint. Its recorded clock is the length of that prefix. -/
private theorem CheckpointRepresentsPrefix.append {history : List WAL.Write} {header : Checkpoint}
    {files : List ByteArray} (known : CheckpointRepresentsPrefix history header files) (suffix : List WAL.Write) :
    CheckpointRepresentsPrefix (history ++ suffix) header files := by
  obtain ⟨checkpoint, model, written, refined, represented⟩ := known
  have within : checkpoint.committed.toNat ≤ history.length := by
    have size := represented.committed_count
    rw [← refined.committed, List.length_take] at size
    omega
  refine ⟨checkpoint, model, written, refined, ?_⟩
  rwa [List.take_append_of_le_length within]

/-- Acknowledged writes extend the live WAL and its table without changing
the selected manifest, its run bytes, or its covered prefix. -/
theorem ObservedMarkedState.VersionedReady.acknowledgedWrites {state : ObservedMarkedState}
    {submitted : List WAL.Write} {writer : MarkedWriterState} (valid : state.VersionedReady)
    (path : AcknowledgedWrites state.writer submitted writer) :
    (state.withWriter writer).VersionedReady ∧ writer.history = state.writer.history ++ submitted := by
  obtain ⟨model, refined, represented⟩ := valid.live
  obtain ⟨ready, extended, next, _, nextRefined, nextHistory⟩ :=
    path.refinesHistory valid.ready refined represented
  let after := state.withWriter writer
  have sameManifest : writer.image.directory.active.manifest = state.writer.image.directory.active.manifest := by
    have active := congrArg DirectoryPublication.Bindings.manifest ready.settled.1
    exact active
  refine ⟨⟨sameManifest.symm ▸ ready, ⟨next, nextRefined, nextHistory⟩, ?_, ?_⟩, extended⟩
  · change after.publicationInput.AcceptsVersioned writer.history.length.toUInt64
      (CheckpointRepresentsPrefix writer.history) writer.image.directory.active.manifest
    rw [sameManifest, extended]
    have monotone : state.writer.history.length.toUInt64 ≤ (state.writer.history ++ submitted).length.toUInt64 := by
      rw [← extended]
      have beforeCount : state.writer.history.length.toUInt64 = state.writer.table.committed := by
        rw [valid.ready.count]; simp
      have afterCount : writer.history.length.toUInt64 = writer.table.committed := by rw [ready.count]; simp
      rw [beforeCount, afterCount, UInt64.le_iff_toNat_le, ← valid.ready.count, ← ready.count, extended]
      simp
    have accepted := valid.selected
    cases binding : state.writer.image.directory.active.manifest with
    | none => trivial
    | some bytes =>
      rw [binding] at accepted
      obtain ⟨selected, decoded, header, files, canonical, ⟨witness, checked⟩, covered, count, durable⟩ := accepted
      exact ⟨selected, decoded, header, files, canonical, ⟨witness.append submitted, checked⟩,
        UInt64.le_trans covered monotone, count, durable⟩
  · change ((writer.image.directory.active.manifest.mapM fun bytes =>
      (VersionedCheckpoint.decode bytes).map (·.header.generation)).map (·.getD 0) : Except String UInt64) =
        .ok state.generation
    rw [sameManifest]
    exact valid.generationMatches

/-- The nonwrapping successor differs from the installed generation in
every selectable binding, even after a v2 reopen. -/
theorem ObservedMarkedState.VersionedReady.successorUnreachable {state : ObservedMarkedState}
    (valid : state.VersionedReady) (fits : state.generation.toNat + 1 < UInt64.size) :
    state.publicationInput.UnreachableVersioned (UInt64.ofNat (state.generation.toNat + 1)) := by
  intro bytes selectable selected decoded same
  have active : state.publicationInput.manifest.active = some bytes := by
    rcases selectable with visible | survives
    · exact visible
    · rw [valid.crashChoice] at survives
      exact (List.mem_singleton.mp survives).symm
  have visible : state.writer.image.directory.active.manifest = some bytes := active
  have loaded := valid.generationMatches
  rw [visible] at loaded
  have generation : selected.header.generation = state.generation := by
    simpa [Option.mapM, decoded, Functor.map, Except.map] using loaded
  have sequence := congrArg UInt64.toNat same
  rw [generation, UInt64.toNat_ofNat_of_lt' fits] at sequence
  omega

/-- The next publication report enters the same retry model whether the
ready predecessor selected a v1 or a v2 manifest. -/
theorem CheckpointPreparation.reportedFromVersionedReady {state : ObservedMarkedState}
    (prepared : CheckpointPreparation state) (valid : state.VersionedReady)
    (byteLengthsFit : ∀ bytes ∈ prepared.runs.files, bytes.size < UInt64.size)
    {report : Step → StepReport} {result : EStateM.Result Unit Image Unit}
    (reported : state.publicationInput.runVersionedWithReports (.integrity prepared.runs) report = some result) :
    match result with
    | .ok _ after | .error _ after => VersionedRetry state.writer.history.length.toUInt64
        (CheckpointRepresentsPrefix state.writer.history) state.publicationInput after := by
  obtain ⟨model, refined, represented⟩ := valid.live
  have attempt := prepared.versionedAttempt valid.ready refined represented
    (valid.successorUnreachable prepared.generationFits) byteLengthsFit reported
  cases result <;> exact attempt

/-- The shared schedule's successful result installs the real prepared
table, raw v2 manifest, successor generation, and exact run map. The
acknowledged WAL remains ready for further writes. -/
theorem CheckpointPreparation.succeededFromVersionedReady {state : ObservedMarkedState}
    (prepared : CheckpointPreparation state) (valid : state.VersionedReady)
    (byteLengthsFit : ∀ bytes ∈ prepared.runs.files, bytes.size < UInt64.size)
    {report : Step → StepReport} {published : Image}
    (reported : state.publicationInput.runVersionedWithReports (.integrity prepared.runs) report =
      some (.ok () published)) :
    (prepared.installed published).VersionedReady := by
  let plan := VersionedRunSet.integrity prepared.runs
  have trace := prepared.reportedFromVersionedReady valid byteLengthsFit reported
  have final := checkpointVersioned_retry_valid valid.validPublicationInput trace
  have actual := state.publicationInput.runVersionedWithReports_outcome plan report reported
  obtain ⟨after, complete, manifest, _, _⟩ := checkpointVersioned_complete state.publicationInput plan
  have same := Option.some.inj (complete.symm.trans actual)
  subst after
  obtain ⟨model, refined, represented⟩ := valid.live
  obtain ⟨written, committed, _⟩ := CheckpointForRecovery.of_flushForCheckpoint prepared.flushed
    refined prepared.runCountFits valid.ready.rowBounds.runs valid.ready.rowBounds.memory prepared.runs.header.generation
  obtain ⟨next, _, nextRefined, nextHistory⟩ := CheckpointForRecovery.of_flushForCheckpoint_history
    prepared.flushed refined represented valid.ready.rowBounds prepared.runCountFits prepared.runs.header.generation
  have clock : state.writer.history.length = prepared.table.committed.toNat := by
    rw [committed]
    exact valid.ready.count
  have live : RepresentsWalHistory state.writer.history next := by
    rwa [← clock, List.take_length] at nextHistory
  have visible : (published.markedReopenImage state.writer.image).directory.active.manifest =
      some plan.manifest.encode := by
    change published.manifest.active = _
    rw [manifest]
    rfl
  have settled : (published.markedReopenImage state.writer.image).SettledFor
      (some plan.manifest.encode) state.writer.history := by
    obtain ⟨active, _, wal, crashes⟩ := valid.ready.settled
    refine ⟨?_, ?_, wal, crashes⟩
    · have marker := congrArg DirectoryPublication.Bindings.walBoundary active
      change (⟨published.manifest.active, state.writer.image.directory.active.walBoundary⟩ :
        DirectoryPublication.Bindings) = ⟨some plan.manifest.encode, _⟩
      rw [manifest, marker]
      rfl
    · simp [Image.markedReopenImage, manifest, Publication.Image.settled]
  refine ⟨?_, ⟨next, nextRefined, live⟩, ?_, ?_⟩
  · exact visible.symm ▸ ⟨settled, valid.ready.ordered, clock, valid.ready.length, valid.ready.fits, written.rowBounds⟩
  · change published.AcceptsVersioned state.writer.history.length.toUInt64
      (CheckpointRepresentsPrefix state.writer.history) published.manifest.active
    exact final.activeValid
  · change (((published.markedReopenImage state.writer.image).directory.active.manifest.mapM fun bytes =>
      (VersionedCheckpoint.decode bytes).map (·.header.generation)).map (·.getD 0) : Except String UInt64) =
        .ok prepared.runs.header.generation
    have floor : prepared.runs.header.floor ≤ prepared.runs.header.committed := by
      change prepared.table.pins.floor ≤ prepared.table.committed
      rw [nextRefined.pins, nextRefined.committed]
      exact next.floor_committed
    rw [visible]
    have decoded : VersionedCheckpoint.decode plan.manifest.encode = .ok plan.manifest :=
      prepared.decodeVersionedManifest floor
    simp only [Option.mapM, decoded, Functor.map, Except.map, Option.getD]
    rfl

end Alvoki.WAL.Boundary
