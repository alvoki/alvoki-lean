import Alvoki.Storage.Disk.MarkedDatabaseCheckpoint
import Alvoki.Storage.Disk.ObservedMarkedState
import Alvoki.Storage.Disk.FreshMarkedBootstrap

namespace Alvoki.WAL.Boundary
open Storage
open Sequential (SnapshotHandle SnapshotPin)

def ObservedMarkedState.publicationInput (state : ObservedMarkedState) : CheckpointPublication.Image :=
  ⟨state.writer.image.directory.project .manifest, state.durable⟩

/-- Checkpoint preparation records the guard and flush results used before
the shared publication schedule starts. -/
structure CheckpointPreparation (state : ObservedMarkedState) where
  table : PackedTable
  flushed : (flushForCheckpoint state.writer.table id : Except String PackedTable) = .ok table
  generationFits : state.generation.toNat + 1 < UInt64.size
  runCountFits : table.runs.length < UInt64.size

def CheckpointPreparation.runs {state : ObservedMarkedState} (prepared : CheckpointPreparation state) :
    CheckpointPublication.RunSet :=
  .forTable prepared.table (UInt64.ofNat (state.generation.toNat + 1))

def CheckpointPreparation.installed {state : ObservedMarkedState} (prepared : CheckpointPreparation state)
    (published : CheckpointPublication.Image) : ObservedMarkedState :=
  ⟨{ state.writer with table := prepared.table, image := published.markedReopenImage state.writer.image },
    prepared.runs.header.generation, published.durable⟩

/-- Each step connects ready endpoints. Operations that poison the handle
record recovery attempts and the actual successful open before the next
endpoint. Checkpoint and read observations contain no refinement witness. -/
inductive MarkedDatabaseStep (state : ObservedMarkedState) : MarkedSessionWrites → ObservedMarkedState → Prop where
  | acknowledged {submitted writer} (path : AcknowledgedWrites state.writer submitted writer) :
      MarkedDatabaseStep state ⟨submitted, none⟩ (state.withWriter writer)
  | advanceFloor {floor table} (advanced : state.writer.table.advanceFloor floor = some table) :
      MarkedDatabaseStep state ⟨[], none⟩ (state.withTable table)
  | compact {index table} (compacted : state.writer.table.compact index = some table) :
      MarkedDatabaseStep state ⟨[], none⟩ (state.withTable table)
  | acquireAt {snapshot pin table} (acquired : state.writer.table.acquireAt snapshot = some (pin, table)) :
      MarkedDatabaseStep state ⟨[], none⟩ (state.withTable table)
  | release (handle : SnapshotHandle) :
      MarkedDatabaseStep state ⟨[], none⟩ (state.withTable (state.writer.table.release handle))
  | reopen {writes writer} (step : MarkedSessionStep state.durable state.writer writes writer) :
      MarkedDatabaseStep state writes (state.withWriter writer)
  | checkpoint (prepared : CheckpointPreparation state) {published report}
      (reported : state.publicationInput.runWithReports prepared.runs report = .ok () published) :
      MarkedDatabaseStep state ⟨[], none⟩ (prepared.installed published)
  | interruptedCheckpoint (prepared : CheckpointPreparation state) {published checkpointReport}
      (reported : state.publicationInput.runWithReports prepared.runs checkpointReport = .error () published)
      {reopenStart after : ReopenImage} {table : PackedTable} {writer : MarkedWriterState}
      (attempts : MarkedReopenAttempts (published.markedReopenImage state.writer.image) reopenStart)
      (checkpointReads : CheckpointReadObservations published reopenStart.directory.active.manifest)
      (walReads : MarkedWalReads reopenStart)
      {report : Publication.Step → RepairReport} {aligned : AlignedSyncReport}
      (opened : runMarkedReopen
        (MarkedReopenReads.mk walReads
          (checkpointReads.result.map fun loaded => (loaded.getD (.empty, 0)).1)).preflight
        report false aligned reopenStart = .ok table after)
      (observed : MarkedWriterState.observeReopen table after = some writer)
      {loaded : Option (PackedTable × UInt64)} (read : checkpointReads.result = .ok loaded) :
      MarkedDatabaseStep state ⟨[], none⟩ ⟨writer, (loaded.getD (.empty, 0)).2, published.durable⟩

private theorem samePublicationInput {state : ObservedMarkedState} {fixed : FixedMarkedCheckpoint}
    (durable : fixed.image.durable = state.durable) :
    fixed.publicationInput state.writer = state.publicationInput := by
  change CheckpointPublication.Image.mk _ fixed.image.durable =
    CheckpointPublication.Image.mk _ state.durable
  rw [durable]

theorem MarkedDatabaseStep.refines {state after : ObservedMarkedState} {writes : MarkedSessionWrites}
    (step : MarkedDatabaseStep state writes after) (valid : state.Valid) :
    ∃ suffix, after.Valid ∧ after.writer.history = state.writer.history ++ suffix ∧ writes.Retains suffix := by
  cases step with
  | acknowledged path =>
    obtain ⟨next, extended⟩ := valid.acknowledgedWrites path
    exact ⟨_, next, extended, .inl rfl⟩
  | advanceFloor advanced =>
    exact ⟨[], valid.advanceFloor advanced, by simp [ObservedMarkedState.withTable, ObservedMarkedState.withWriter],
      .inl rfl⟩
  | compact compacted =>
    exact ⟨[], valid.compact compacted, by simp [ObservedMarkedState.withTable, ObservedMarkedState.withWriter],
      .inl rfl⟩
  | acquireAt acquired =>
    exact ⟨[], valid.acquireAt acquired, by simp [ObservedMarkedState.withTable, ObservedMarkedState.withWriter],
      .inl rfl⟩
  | release handle =>
    exact ⟨[], valid.release handle, by simp [ObservedMarkedState.withTable, ObservedMarkedState.withWriter],
      .inl rfl⟩
  | reopen reopen =>
    obtain ⟨suffix, next, extended, retains, _⟩ := valid.sessionStep reopen
    exact ⟨suffix, next, extended, retains⟩
  | @checkpoint prepared published report reported =>
    obtain ⟨fixed, durable, represented⟩ := valid
    rw [← samePublicationInput durable] at reported
    obtain ⟨next, image, nextValid⟩ := represented.checkpointSucceeded
      prepared.generationFits prepared.flushed prepared.runCountFits reported
    exact ⟨[], ⟨next, congrArg CheckpointPublication.Image.durable image, nextValid⟩,
      by simp [CheckpointPreparation.installed], .inl rfl⟩
  | @interruptedCheckpoint prepared published checkpointReport reported _ _ _ writer
      attempts checkpointReads walReads report aligned opened observed loaded read =>
    obtain ⟨fixed, durable, represented⟩ := valid
    rw [← samePublicationInput durable] at reported
    obtain ⟨next, nextValid, history, exactDurable, nextObserved, nextLoaded, nextRead, generation⟩ :=
      represented.checkpointInterrupted prepared.generationFits prepared.flushed prepared.runCountFits
        reported attempts checkpointReads walReads opened
    have writerEq : next.writer = writer := Option.some.inj (nextObserved.symm.trans observed)
    have loadedEq : nextLoaded = loaded := Except.ok.inj (nextRead.symm.trans read)
    have generationEq : next.generation = (loaded.getD (.empty, 0)).2 := loadedEq ▸ generation
    refine ⟨[], ⟨next.checkpoint, exactDurable, ?_⟩, ?_, .inl rfl⟩
    · have stateEq : (⟨writer, next.checkpoint, (loaded.getD (.empty, 0)).2⟩ : MarkedDatabaseState) = next := by
        cases next
        simp_all
      exact stateEq.symm ▸ nextValid
    · rw [← writerEq, history, List.append_nil]

/-- A finite sequence of ready-boundary operations, with submission events
in operation order. -/
inductive MarkedDatabaseTrace (initial : ObservedMarkedState) :
    List MarkedSessionWrites → ObservedMarkedState → Prop where
  | start : MarkedDatabaseTrace initial [] initial
  | step (prior : MarkedDatabaseTrace initial sessions before)
      (operation : MarkedDatabaseStep before writes after) :
      MarkedDatabaseTrace initial (sessions ++ [writes]) after

theorem MarkedDatabaseTrace.refines {initial after : ObservedMarkedState} {sessions : List MarkedSessionWrites}
    (path : MarkedDatabaseTrace initial sessions after) (valid : initial.Valid) :
    ∃ suffix, after.Valid ∧ after.writer.history = initial.writer.history ++ suffix ∧
      MarkedSessionRetention sessions suffix := by
  induction path with
  | start => exact ⟨[], valid, by simp, .start⟩
  | step _ operation ih =>
    obtain ⟨prefixWrites, beforeValid, history, retained⟩ := ih
    obtain ⟨suffix, afterValid, extended, lastRetained⟩ := operation.refines beforeValid
    exact ⟨prefixWrites ++ suffix, afterValid, by rw [extended, history, List.append_assoc],
      .append retained lastRetained⟩

/-- Every active local pin reads the canonical durable history at its own
sequence. Session identity in the outer IO handle is a separate boundary. -/
theorem ObservedMarkedState.Valid.pinnedReads {state : ObservedMarkedState} (valid : state.Valid)
    {reference : Sequential.SnapshotTable UInt64}
    (replayed : SnapshotWalReplay .empty state.writer.history reference)
    {pin : SnapshotPin} (active : pin ∈ state.writer.table.pins.active) :
    (∀ key, state.writer.table.lookup pin.handle key = some (reference.table.lookup key pin.sequence)) ∧
    ∀ start stop, state.writer.table.range pin.handle start stop =
      some (reference.table.range start stop pin.sequence) := by
  obtain ⟨_, _, represented⟩ := valid
  obtain ⟨model, refined, history⟩ := represented.live
  have member : pin ∈ model.pins.active := refined.pins ▸ active
  obtain ⟨lookup, range⟩ := history.reads replayed (model.pins.safe pin member)
  exact ⟨fun key => by rw [PackedTable.lookup_refines refined, model.lookup_pinned member, lookup],
    fun start stop => by rw [PackedTable.range_refines refined, model.range_pinned member, range]⟩

/-- Reconstruct the initial ready boundary from the actual successful result
after any admitted empty-bootstrap attempts. The raw writer's history is
obtained by observing its installed WAL, just as at later reopen boundaries. -/
theorem ObservedMarkedState.Valid.ofEmptyBootstrap {initial before : ReopenImage}
    {state : ObservedMarkedState} (fresh : initial.Fresh) (attempts : EmptyBootstrapAttempts initial before)
    {checkpointImage : CheckpointPublication.Image}
    (checkpointReads : CheckpointReadObservations checkpointImage before.directory.active.manifest)
    (walReads : MarkedWalReads before) {manifest marker wal : Option ByteArray}
    (readManifest : checkpointReads.readManifest = .ok manifest)
    (readMarker : walReads.marker = .ok marker) (readWal : walReads.wal = .ok wal)
    (reports : FreshOpenReports) (created : wal = none → reports.createWal = .ok ())
    (synced : reports.syncWalDirectory = .ok ())
    (published : marker = none → ∀ step, reports.marker step = .ok ())
    (opened : (runFreshMarkedOpen checkpointReads.result walReads.marker walReads.wal reports).run before =
      .ok ((state.writer.table, state.generation, state.writer.walBytes), state.writer.image))
    (observed : MarkedWriterState.observeReopen state.writer.table state.writer.image = some state.writer)
    (durableRuns : state.durable = checkpointImage.durable) :
    state.Valid ∧ state.writer.history = [] := by
  obtain ⟨after, fixed, success, ready, absent, covered, _, refines, represents, durable⟩ :=
    emptyBootstrapOpen_ready (attempts.valid fresh) checkpointReads walReads readManifest readMarker readWal
      reports created synced published
  let writer : MarkedWriterState := ⟨.empty, 0, after, []⟩
  have replayed : MarkedWriterState.observeReopen writer.table writer.image = some writer := by
    have emptyWal : after.wal.active = some (WAL.encode []) := ready.settled.2.2.1
    change MarkedWriterState.observeReopen .empty after = some writer
    rw [MarkedWriterState.observeReopen, emptyWal] <;> rfl
  have installed := Except.ok.inj (success.symm.trans opened)
  have tableEq : writer.table = state.writer.table := congrArg (fun value => value.1.1) installed
  have generationEq : 0 = state.generation := congrArg (fun value => value.1.2.1) installed
  have imageEq : writer.image = state.writer.image := congrArg Prod.snd installed
  rw [tableEq, imageEq] at replayed
  have writerEq : writer = state.writer := Option.some.inj (replayed.symm.trans observed)
  have generation : ((fixed.manifest.mapM fun bytes => (Manifest.decode bytes).map (·.generation)).map
      (·.getD 0) : Except String UInt64) = .ok 0 := by
    rw [absent]
    rfl
  have valid : (⟨writer, fixed, 0⟩ : MarkedDatabaseState).Valid := by
    refine ⟨ready, ⟨[], ?_⟩, ⟨fixed.model, refines, represents⟩, ?_, generation⟩
    · change [] = fixed.covered ++ []
      simp only [covered, List.nil_append]
    · simpa only [covered] using represents
  refine ⟨⟨fixed, durable.trans durableRuns.symm, ?_⟩, ?_⟩
  · rwa [← writerEq, ← generationEq]
  · rw [← writerEq]

/-- The ready-boundary trace accounts for every acknowledged frame and every
retained ambiguous submission. Its returned table reads the unique abstract
replay of the resulting history at every active local pin. -/
theorem MarkedDatabaseTrace.canonicalReads {initial after : ObservedMarkedState}
    {sessions : List MarkedSessionWrites} (path : MarkedDatabaseTrace initial sessions after)
    (valid : initial.Valid) :
    ∃ suffix, after.writer.history = initial.writer.history ++ suffix ∧
      MarkedSessionRetention sessions suffix ∧ after.Valid ∧
      ∃ reference, SnapshotWalReplay .empty after.writer.history reference ∧
        ∀ pin ∈ after.writer.table.pins.active,
          (∀ key, after.writer.table.lookup pin.handle key = some (reference.table.lookup key pin.sequence)) ∧
          ∀ start stop, after.writer.table.range pin.handle start stop =
            some (reference.table.range start stop pin.sequence) := by
  obtain ⟨suffix, ready, history, retained⟩ := path.refines valid
  have ordered : WAL.OrdinalsFrom 1 after.writer.history := by
    obtain ⟨_, _, witness⟩ := ready
    exact witness.ready.ordered
  obtain ⟨reference, replayed⟩ := SnapshotWalReplay.fromEmpty after.writer.history ordered
  exact ⟨suffix, history, retained, ready, reference, replayed,
    fun _ active => ready.pinnedReads replayed active⟩

end Alvoki.WAL.Boundary
