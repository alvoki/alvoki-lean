import Alvoki.Storage.Disk.IntegrityBootstrap
import Alvoki.Storage.Disk.StrictCheckpointReopen
import Alvoki.Storage.Disk.VersionedUncertainWrite
import Alvoki.Storage.Disk.VersionedReadyRunCollection

namespace Alvoki.WAL.Boundary
open System Storage CheckpointPublication Manifest
open Sequential (SnapshotHandle SnapshotPin SnapshotTable)

/-- Optional and ordered run lookups refer to the same acquired directory.
The bootstrap and marked recovery supply their own effect reports. -/
structure IntegrityOpenPaths (before : ReopenImage) (durable : RunFiles) where
  directory : DiskDirectory
  descriptor : Nat
  owners : DiskSession.LockOwners
  acquisition : DiskSession.TryLockObserves owners directory (.ok true)
  paths : OpenPathReadReports
  observes : (owners.set (directory.file .lock) (some descriptor)).Owns directory descriptor →
    paths.ObservesVersioned directory before durable
  manifestRead : ∃ value, paths.readOptional (directory.file .manifest) = .ok value
  markerRead : ∃ value, paths.readOptional (directory.file .walBoundary) = .ok value
  walRead : ∃ value, paths.readOptional (directory.file .wal) = .ok value
  unlock : DiskSession.UnlockReport
  cause : String → IO.Error

def IntegrityOpenPaths.heldOwners {before : ReopenImage} {durable : RunFiles}
    (reports : IntegrityOpenPaths before durable) : DiskSession.LockOwners :=
  reports.owners.set (reports.directory.file .lock) (some reports.descriptor)

theorem IntegrityOpenPaths.held {before : ReopenImage} {durable : RunFiles}
    (reports : IntegrityOpenPaths before durable) :
    reports.heldOwners.Owns reports.directory reports.descriptor := by
  simp [heldOwners, DiskSession.LockOwners.Owns, DiskSession.LockOwners.set]

/-- Run read success is needed only for the selection made by the strict
decoder. The WAL chooses either the repair or the aligned sync report. -/
structure IntegrityLockedOpenReports (before : ReopenImage) (durable : RunFiles)
    extends IntegrityOpenPaths before durable where
  runReads : ∀ bytes selected, before.directory.active.manifest = some bytes →
    IntegrityCheckpoint.decode bytes = .ok selected → ∀ index, index < selected.header.runCount.toNat →
      ∃ payload, paths.readBin (directory.file (.run selected.header.generation index)) = .ok payload
  repair : Publication.Step → RepairReport
  aligned : AlignedSyncReport

/-- Only the branch selected by the reported WAL and marker must succeed. -/
def IntegrityLockedOpenReports.Healthy {before : ReopenImage} {durable : RunFiles}
    (reports : IntegrityLockedOpenReports before durable) : Prop :=
  ∀ marker contents length,
    (reports.paths.readOptional (reports.directory.file .walBoundary)).mapError toString = .ok (some marker) →
    (reports.paths.readOptional (reports.directory.file .wal)).mapError toString = .ok (some contents) →
    decode marker = .ok length →
    if length.toNat < contents.size then (∀ step, reports.repair step = .success) else reports.aligned = .success

def IntegrityLockedOpenReports.run {before : ReopenImage} {durable : RunFiles}
    (reports : IntegrityLockedOpenReports before durable) :
    EStateM.Result IO.Error DiskSession.LockOwners ((PackedTable × UInt64 × Nat) × ReopenImage) :=
  let reads := VersionedCheckpointFileReads.ofLockedPaths reports.toIntegrityOpenPaths.held reports.observes
  let walReads := (reports.observes reports.toIntegrityOpenPaths.held).toObserves.walReads
  let reopened := runSharedMarkedOpen (readIntegrityCheckpoint reads.readManifest reads.readRun id)
    walReads.marker walReads.wal reports.repair reports.aligned before
  DiskSession.runLockedMarkedOpen reports.directory reports.descriptor (.ok true) reports.unlock reports.cause
    reopened reports.owners

/-- A returned state records the actual installed table, generation and
files. The writer history comes from observing the returned WAL. -/
structure IntegrityLockedOpenReports.Returned {before : ReopenImage} {durable : RunFiles}
    (reports : IntegrityLockedOpenReports before durable) (next : ObservedMarkedState) : Prop where
  installed : reports.run = .ok ((next.writer.table, next.generation, next.writer.walBytes), next.writer.image)
    reports.toIntegrityOpenPaths.heldOwners
  observed : MarkedWriterState.observeReopen next.writer.table next.writer.image = some next.writer
  runMap : next.durable = durable

private theorem ObservedMarkedState.eq_of_installation {left right : ObservedMarkedState}
    (installed : ((left.writer.table, left.generation, left.writer.walBytes), left.writer.image) =
      ((right.writer.table, right.generation, right.writer.walBytes), right.writer.image))
    (observedLeft : MarkedWriterState.observeReopen left.writer.table left.writer.image = some left.writer)
    (observedRight : MarkedWriterState.observeReopen right.writer.table right.writer.image = some right.writer)
    (runsEq : left.durable = right.durable) : left = right := by
  have tableEq : left.writer.table = right.writer.table := congrArg (fun result => result.1.1) installed
  have generationEq : left.generation = right.generation := congrArg (fun result => result.1.2.1) installed
  have imageEq : left.writer.image = right.writer.image := congrArg Prod.snd installed
  rw [tableEq, imageEq] at observedLeft
  have writerEq := Option.some.inj (observedLeft.symm.trans observedRight)
  cases left
  cases right
  cases writerEq
  cases generationEq
  cases runsEq
  rfl

theorem IntegrityLockedOpenReports.Returned.unique {before : ReopenImage} {durable : RunFiles}
    {reports : IntegrityLockedOpenReports before durable} {left right : ObservedMarkedState}
    (first : reports.Returned left) (second : reports.Returned right) : left = right :=
  ObservedMarkedState.eq_of_installation (EStateM.Result.ok.inj (first.installed.symm.trans second.installed)).1
    first.observed second.observed (first.runMap.trans second.runMap.symm)

private theorem IntegrityLockedOpenReports.versionedRunReads {before : ReopenImage} {durable : RunFiles}
    (reports : IntegrityLockedOpenReports before durable)
    (integrity : ∀ bytes, before.directory.active.manifest = some bytes →
      ∃ selected, IntegrityCheckpoint.decode bytes = .ok selected)
    (bytes : ByteArray) (selected : VersionedCheckpoint)
    (visible : before.directory.active.manifest = some bytes) (decoded : VersionedCheckpoint.decode bytes = .ok selected)
    (index : Nat) (within : index < selected.header.runCount.toNat) :
    ∃ payload, reports.paths.readBin (reports.directory.file (.run selected.header.generation index)) = .ok payload := by
  obtain ⟨strict, parsed⟩ := integrity bytes visible
  have same := Except.ok.inj (decoded.symm.trans (VersionedCheckpoint.decode_integrity parsed))
  subst selected
  exact reports.runReads bytes strict visible parsed index within

/-- A healthy strict reopen recovers the one marker-selected write history
and leaves the checkpoint binding and generation unchanged. -/
theorem IntegrityLockedOpenReports.recoversUncertainWrite {state : ObservedMarkedState}
    (valid : state.VersionedReady) (integrity : state.HasIntegrityManifest)
    {key : UInt64} {value : Option UInt64} {event : WAL.Write} {preparedTable : PackedTable}
    (prepared : prepareWrite state.writer.table key value = some (event, preparedTable))
    (fits : state.writer.walBytes + WAL.frameSize < UInt64.size)
    {effects : WriteEffects} {cut before : ReopenImage}
    (failed : runWriteEffectsFrom state.writer.history event effects state.writer.image = .error () cut)
    (attempts : MarkedReopenAttempts cut before)
    (reports : IntegrityLockedOpenReports before state.durable) (healthy : reports.Healthy) :
    ∃ next : ObservedMarkedState,
      reports.Returned next ∧ reports.owners (reports.directory.file .lock) = none ∧
      next.VersionedReady ∧ next.HasIntegrityManifest ∧ next.generation = state.generation ∧
      next.writer.image.directory.active.manifest = state.writer.image.directory.active.manifest ∧
      (next.writer.history = state.writer.history ∨ next.writer.history = state.writer.history ++ [event]) ∧
      before.directory.active.walBoundary = some (encode (WAL.encode next.writer.history).size.toUInt64) ∧
      next.writer.table.pins.active = [] := by
  have manifest := MarkedWriterState.manifestAfterWriteError valid.ready prepared fits failed attempts
  have runReads := reports.versionedRunReads (fun bytes visible => integrity bytes (manifest.symm.trans visible))
  obtain ⟨next, _, available, _, observed, ready, generation, files, sameManifest, retained, pins, marker, strict⟩ :=
    valid.reopenAfterWriteErrorWithLock prepared fits failed attempts
      reports.acquisition reports.observes reports.manifestRead runReads reports.markerRead reports.walRead
      reports.repair reports.aligned healthy reports.unlock reports.cause
  obtain ⟨installed, format⟩ := strict integrity
  exact ⟨next, ⟨installed, observed, files⟩, available, ready, format, generation, sameManifest, retained, marker, pins⟩

/-- A single run collection pass in the same open session. The writer holds
the directory lock throughout the manifest read, inventory and same-path
unlink and sync callbacks. The reports carry their actual filesystem
effects. A recovery after losing the handle uses a separate open step. -/
structure IntegrityRunCollectionReports (directory : DiskDirectory) (state : ObservedMarkedState)
    (before : RunUnlinkImage) where
  owners : DiskSession.LockOwners
  descriptor : Nat
  heldLock : owners.Owns directory descriptor
  manifest : OptionalPathRead state.writer.image.directory.active.manifest
  observed : Option ByteArray
  manifestRead : manifest.result (directory.file .manifest) = .ok observed
  regularAt : FilePath → Prop
  inventory : LockedRunInventory directory regularAt
  known : ∀ generation index bytes, state.durable generation index = some bytes →
    before.guaranteed generation index = some bytes
  held : List UInt64
  removeFile : FilePath → EStateM IO.Error RunUnlinkImage (Except IO.Error Unit)
  syncDirectory : FilePath → EStateM IO.Error RunUnlinkImage Unit
  effects : RunUnlinkEffectContract (RunCollection.performPaths removeFile syncDirectory throw
    (fun address : RunAddress => directory.file (.run address.1 address.2)) directory.path)

def IntegrityRunCollectionReports.perform {directory : DiskDirectory} {state : ObservedMarkedState}
    {before : RunUnlinkImage} (reports : IntegrityRunCollectionReports directory state before) :
    RunCollection.Step RunAddress → EStateM IO.Error RunUnlinkImage Unit :=
  RunCollection.performPaths reports.removeFile reports.syncDirectory throw
    (fun address => directory.file (.run address.1 address.2)) directory.path

def IntegrityRunCollectionReports.run {directory : DiskDirectory} {state : ObservedMarkedState}
    {before : RunUnlinkImage} (reports : IntegrityRunCollectionReports directory state before) :
    EStateM.Result IO.Error RunUnlinkImage Unit :=
  reports.inventory.runIntegrityCollection state.generation reports.observed reports.held reports.perform before

def IntegrityRunCollectionReports.after {directory : DiskDirectory} {state : ObservedMarkedState}
    {before : RunUnlinkImage} (reports : IntegrityRunCollectionReports directory state before) : ObservedMarkedState :=
  match reports.run with
  | .ok _ after | .error _ after => state.withDurableRuns after.guaranteed

theorem IntegrityRunCollectionReports.refines {directory : DiskDirectory} {state : ObservedMarkedState}
    {before : RunUnlinkImage} (reports : IntegrityRunCollectionReports directory state before)
    (valid : state.VersionedReady) (integrity : state.HasIntegrityManifest) :
    reports.after.VersionedReady ∧ reports.after.HasIntegrityManifest ∧ reports.after.writer = state.writer := by
  have kept := valid.collectReported integrity reports.inventory reports.known reports.manifest reports.manifestRead
    reports.held reports.perform reports.effects
  change (match reports.run with
    | .ok _ after | .error _ after => (state.withDurableRuns after.guaranteed).VersionedReady ∧
        (state.withDurableRuns after.guaranteed).HasIntegrityManifest) at kept
  unfold IntegrityRunCollectionReports.after
  split at kept <;> exact ⟨kept.1, kept.2, rfl⟩

/-- A strict ready-boundary step records native or shared operation
outcomes. Collection can return to the same handle. Errors that require
reopening carry the actual locked open's returned state. -/
inductive IntegrityDatabaseStep (directory : DiskDirectory) (state : ObservedMarkedState) : MarkedSessionWrites → ObservedMarkedState → Prop where
  | acknowledged {submitted writer} (path : AcknowledgedWrites state.writer submitted writer) :
      IntegrityDatabaseStep directory state ⟨submitted, none⟩ (state.withWriter writer)
  | advanceFloor {floor table} (advanced : state.writer.table.advanceFloor floor = some table) :
      IntegrityDatabaseStep directory state ⟨[], none⟩ (state.withTable table)
  | compact {index table} (compacted : state.writer.table.compact index = some table) :
      IntegrityDatabaseStep directory state ⟨[], none⟩ (state.withTable table)
  | acquireAt {snapshot pin table} (acquired : state.writer.table.acquireAt snapshot = some (pin, table)) :
      IntegrityDatabaseStep directory state ⟨[], none⟩ (state.withTable table)
  | release (handle : SnapshotHandle) :
      IntegrityDatabaseStep directory state ⟨[], none⟩ (state.withTable (state.writer.table.release handle))
  | collectRuns {before : RunUnlinkImage} (reports : IntegrityRunCollectionReports directory state before) :
      IntegrityDatabaseStep directory state ⟨[], none⟩ reports.after
  | checkpoint (prepared : CheckpointPreparation state) (fits : ∀ bytes ∈ prepared.runs.files, bytes.size < UInt64.size)
      {report published} (reported : state.publicationInput.runVersionedWithReports (.integrity prepared.runs) report =
        some (.ok () published)) :
      IntegrityDatabaseStep directory state ⟨[], none⟩ (prepared.installed published)
  | interruptedCheckpoint (prepared : CheckpointPreparation state)
      (fits : ∀ bytes ∈ prepared.runs.files, bytes.size < UInt64.size) {checkpointReport published}
      (failed : state.publicationInput.runVersionedWithReports (.integrity prepared.runs) checkpointReport =
        some (.error () published)) {before next}
      (attempts : MarkedReopenAttempts (published.markedReopenImage state.writer.image) before)
      {reports : IntegrityLockedOpenReports before published.durable}
      (path : reports.directory = directory) (aligned : reports.aligned = .success)
      (returned : reports.Returned next) :
      IntegrityDatabaseStep directory state ⟨[], none⟩ next
  | reopen {before next} (attempts : MarkedReopenAttempts state.writer.image before)
      {reports : IntegrityLockedOpenReports before state.durable}
      (path : reports.directory = directory) (aligned : reports.aligned = .success)
      (returned : reports.Returned next) :
      IntegrityDatabaseStep directory state ⟨[], none⟩ next
  | uncertainWrite {key value event preparedTable} (prepared : prepareWrite state.writer.table key value =
      some (event, preparedTable)) (fits : state.writer.walBytes + WAL.frameSize < UInt64.size)
      {effects cut before next} (failed : runWriteEffectsFrom state.writer.history event effects state.writer.image =
        .error () cut) (attempts : MarkedReopenAttempts cut before)
      {reports : IntegrityLockedOpenReports before state.durable}
      (path : reports.directory = directory) (healthy : reports.Healthy) (returned : reports.Returned next) :
      IntegrityDatabaseStep directory state ⟨[], some event⟩ next

theorem IntegrityDatabaseStep.refines {directory : DiskDirectory} {state after : ObservedMarkedState} {writes : MarkedSessionWrites}
    (step : IntegrityDatabaseStep directory state writes after) (valid : state.VersionedReady)
    (integrity : state.HasIntegrityManifest) :
    ∃ suffix, after.VersionedReady ∧ after.HasIntegrityManifest ∧
      after.writer.history = state.writer.history ++ suffix ∧ writes.Retains suffix := by
  cases step with
  | acknowledged path =>
    obtain ⟨afterReady, extended⟩ := valid.acknowledgedWrites path
    have visible := congrArg DirectoryPublication.Bindings.manifest (path.refines valid.ready).1.settled.1
    exact ⟨_, afterReady, integrity.ofSameManifest visible, extended, .inl rfl⟩
  | advanceFloor advanced => exact ⟨[], valid.advanceFloor advanced, integrity, by simp [ObservedMarkedState.withTable, ObservedMarkedState.withWriter], .inl rfl⟩
  | compact compacted => exact ⟨[], valid.compact compacted, integrity, by simp [ObservedMarkedState.withTable, ObservedMarkedState.withWriter], .inl rfl⟩
  | acquireAt acquired => exact ⟨[], valid.acquireAt acquired, integrity, by simp [ObservedMarkedState.withTable, ObservedMarkedState.withWriter], .inl rfl⟩
  | release handle => exact ⟨[], valid.release handle, integrity, by simp [ObservedMarkedState.withTable, ObservedMarkedState.withWriter], .inl rfl⟩
  | collectRuns reports =>
    obtain ⟨ready, strict, sameWriter⟩ := reports.refines valid integrity
    exact ⟨[], ready, strict, by rw [sameWriter, List.append_nil], .inl rfl⟩
  | checkpoint prepared fits reported =>
    exact ⟨[], prepared.succeededFromVersionedReady valid fits reported,
      prepared.succeededIntegrityManifest valid reported, by simp [CheckpointPreparation.installed], .inl rfl⟩
  | @interruptedCheckpoint prepared fits checkpointReport published failed before next attempts reports _ aligned returned =>
    obtain ⟨ready, installed, _, _, observed, nextValid, strict, history, exactMap, _⟩ :=
      prepared.reopenAfterIntegrityCheckpointErrorWithLock valid integrity fits failed attempts
        reports.acquisition reports.observes reports.manifestRead reports.runReads reports.markerRead reports.walRead
        reports.repair reports.unlock reports.cause
    have result : reports.Returned ready := by
      refine ⟨?_, observed, exactMap⟩
      unfold IntegrityLockedOpenReports.run
      rw [aligned]
      exact installed
    have same := returned.unique result
    rw [same]
    exact ⟨[], nextValid, strict, by simpa using history, .inl rfl⟩
  | @reopen before next attempts reports _ aligned returned =>
    obtain ⟨ready, installed, _, _, observed, nextValid, strict, history, exactMap, _⟩ :=
      valid.reopenWithLock integrity attempts reports.acquisition reports.observes
        reports.manifestRead reports.runReads reports.markerRead reports.walRead reports.repair reports.unlock reports.cause
    have result : reports.Returned ready := by
      refine ⟨?_, observed, exactMap⟩
      unfold IntegrityLockedOpenReports.run
      rw [aligned]
      exact installed
    rw [returned.unique result]
    exact ⟨[], nextValid, strict, by simpa using history, .inl rfl⟩
  | @uncertainWrite key value event preparedTable prepared fits effects cut before next failed attempts reports _ healthy returned =>
    obtain ⟨ready, result, _, nextValid, format, _, _, retained, _⟩ :=
      reports.recoversUncertainWrite valid integrity prepared fits failed attempts healthy
    rw [returned.unique result]
    rcases retained with old | extended
    · exact ⟨[], nextValid, format, by simpa using old, .inl rfl⟩
    · exact ⟨[event], nextValid, format, extended, .inr ⟨event, rfl, rfl⟩⟩

/-- Each returned state supplies the next operation in the same resolved
directory. Opening edges report lock acquisition and file effects.
Retention accounts for whole submissions in operation order. -/
inductive IntegrityDatabaseTrace (directory : DiskDirectory) (initial : ObservedMarkedState) :
    List MarkedSessionWrites → ObservedMarkedState → Prop where
  | start : IntegrityDatabaseTrace directory initial [] initial
  | step (prior : IntegrityDatabaseTrace directory initial sessions before)
      (operation : IntegrityDatabaseStep directory before writes after) :
      IntegrityDatabaseTrace directory initial (sessions ++ [writes]) after

theorem IntegrityDatabaseTrace.refines {directory : DiskDirectory} {initial after : ObservedMarkedState} {sessions : List MarkedSessionWrites}
    (trace : IntegrityDatabaseTrace directory initial sessions after) (valid : initial.VersionedReady)
    (integrity : initial.HasIntegrityManifest) :
    ∃ suffix, after.VersionedReady ∧ after.HasIntegrityManifest ∧
      after.writer.history = initial.writer.history ++ suffix ∧ MarkedSessionRetention sessions suffix := by
  induction trace with
  | start => exact ⟨[], valid, integrity, by simp, .start⟩
  | step _ operation ih =>
    obtain ⟨previous, beforeReady, beforeIntegrity, history, retained⟩ := ih
    obtain ⟨suffix, nextReady, nextIntegrity, extended, one⟩ := operation.refines beforeReady beforeIntegrity
    exact ⟨previous ++ suffix, nextReady, nextIntegrity, by rw [extended, history, List.append_assoc],
      .append retained one⟩

/-- Every still-active local pin has canonical point and range results. The
durable suffix includes all acknowledgements and admits each uncertain
submission once at most, in operation order. -/
theorem IntegrityDatabaseTrace.canonicalReads {directory : DiskDirectory} {initial after : ObservedMarkedState}
    {sessions : List MarkedSessionWrites} (trace : IntegrityDatabaseTrace directory initial sessions after)
    (valid : initial.VersionedReady) (integrity : initial.HasIntegrityManifest) :
    ∃ suffix, after.writer.history = initial.writer.history ++ suffix ∧ MarkedSessionRetention sessions suffix ∧
      after.VersionedReady ∧ after.HasIntegrityManifest ∧
      ∃ reference, SnapshotWalReplay .empty after.writer.history reference ∧
        ∀ pin : SnapshotPin, pin ∈ after.writer.table.pins.active →
          (∀ key, after.writer.table.lookup pin.handle key = some (reference.table.lookup key pin.sequence)) ∧
          ∀ start stop, after.writer.table.range pin.handle start stop =
            some (reference.table.range start stop pin.sequence) := by
  obtain ⟨suffix, ready, strict, history, retained⟩ := trace.refines valid integrity
  obtain ⟨reference, replayed⟩ := SnapshotWalReplay.fromEmpty after.writer.history ready.ready.ordered
  exact ⟨suffix, history, retained, ready, strict, reference, replayed,
    fun _ active => ready.pinnedReads replayed active⟩

/-- A protected sequence has identical point and range results in two
ready sessions reached through the same database trace. -/
theorem IntegrityDatabaseTrace.pinnedReadsStable {directory : DiskDirectory} {initial after : ObservedMarkedState}
    {sessions : List MarkedSessionWrites} (trace : IntegrityDatabaseTrace directory initial sessions after)
    (valid : initial.VersionedReady) (integrity : initial.HasIntegrityManifest) {oldPin newPin : SnapshotPin}
    (oldActive : oldPin ∈ initial.writer.table.pins.active)
    (newActive : newPin ∈ after.writer.table.pins.active) (sameSequence : newPin.sequence = oldPin.sequence) :
    (∀ key, after.writer.table.lookup newPin.handle key = initial.writer.table.lookup oldPin.handle key) ∧
    ∀ start stop, after.writer.table.range newPin.handle start stop = initial.writer.table.range oldPin.handle start stop := by
  obtain ⟨_, history, _, ready, _, _, replayed, _⟩ := trace.canonicalReads valid integrity
  obtain ⟨_, oldRefines, oldHistory⟩ := valid.live
  obtain ⟨_, newRefines, newHistory⟩ := ready.live
  rw [history] at replayed newHistory
  exact oldHistory.packedPinnedReadsAfterAppend newHistory oldRefines newRefines replayed oldActive newActive
    sameSequence

/-- An earlier pin can be acquired again after reopen if its sequence has
not fallen below the final retention floor. The new pin reads the same snapshot. -/
theorem IntegrityDatabaseTrace.reacquireReadsStable {directory : DiskDirectory} {initial after : ObservedMarkedState}
    {sessions : List MarkedSessionWrites} (trace : IntegrityDatabaseTrace directory initial sessions after)
    (valid : initial.VersionedReady) (integrity : initial.HasIntegrityManifest)
    {oldPin : SnapshotPin} (oldActive : oldPin ∈ initial.writer.table.pins.active)
    (retained : after.writer.table.pins.floor ≤ oldPin.sequence) :
    ∃ newPin table, after.writer.table.acquireAt oldPin.sequence = some (newPin, table) ∧
      newPin.sequence = oldPin.sequence ∧
      (∀ key, table.lookup newPin.handle key = initial.writer.table.lookup oldPin.handle key) ∧
      ∀ start stop, table.range newPin.handle start stop = initial.writer.table.range oldPin.handle start stop := by
  obtain ⟨_, ready, _, history, _⟩ := trace.refines valid integrity
  have committed : oldPin.sequence ≤ after.writer.table.committed := by
    obtain ⟨model, refined, _⟩ := valid.live
    have earlier := model.pins_committed oldPin (refined.pins ▸ oldActive)
    rw [← refined.committed, UInt64.le_iff_toNat_le, ← valid.ready.count] at earlier
    rw [UInt64.le_iff_toNat_le, ← ready.ready.count, history, List.length_append]
    omega
  have canAcquire := (Sequential.SnapshotPins.acquire_iff after.writer.table.pins _ _).mpr ⟨retained, committed⟩
  have available : (after.writer.table.acquireAt oldPin.sequence).isSome = true := by
    simpa only [PackedTable.acquireAt, Option.isSome_map] using canAcquire
  obtain ⟨⟨newPin, table⟩, acquired⟩ := Option.isSome_iff_exists.mp available
  obtain ⟨⟨found, pins⟩, recorded, same⟩ := Option.map_eq_some_iff.mp acquired
  have sequence := (Sequential.SnapshotPins.acquire_spec recorded).2.2.1
  have samePin : found = newPin := congrArg Prod.fst same
  have newSequence : newPin.sequence = oldPin.sequence := samePin ▸ sequence
  have active := PackedTable.acquireAt_active acquired
  let extended := trace.step (.acquireAt acquired)
  exact ⟨newPin, table, acquired, newSequence, extended.pinnedReadsStable valid integrity oldActive active newSequence⟩

/-- The fresh branch uses the same owned paths. It may create the WAL and
publish its first marker after any admitted empty bootstrap cuts. -/
structure IntegrityBootstrapOpenReports (initial before : ReopenImage) (durable : RunFiles)
    extends IntegrityOpenPaths before durable where
  fresh : initial.Fresh
  attempts : EmptyBootstrapAttempts initial before
  effects : FreshOpenReports
  created : paths.readOptional (directory.file .wal) = .ok none → effects.createWal = .ok ()
  synced : effects.syncWalDirectory = .ok ()
  published : paths.readOptional (directory.file .walBoundary) = .ok none →
    ∀ step, effects.marker step = .ok ()

def IntegrityBootstrapOpenReports.run {initial before : ReopenImage} {durable : RunFiles}
    (reports : IntegrityBootstrapOpenReports initial before durable) :
    EStateM.Result IO.Error DiskSession.LockOwners ((PackedTable × UInt64 × Nat) × ReopenImage) :=
  let held := reports.toIntegrityOpenPaths.held
  let reads := VersionedCheckpointFileReads.ofLockedPaths held reports.observes
  let walReads := (reports.observes held).toObserves.walReads
  let opened := (runFreshMarkedOpen (readIntegrityCheckpoint reads.readManifest reads.readRun id)
    walReads.marker walReads.wal reports.effects).run before
  DiskSession.runOpen reports.directory reports.descriptor (.ok true) (opened.mapError reports.cause)
    reports.unlock reports.owners

/-- Starting at the actual strict fresh-open result, a finite trace accounts
for every durable frame and the returned table's local snapshot reads. -/
theorem IntegrityDatabaseTrace.canonicalReadsFromFresh {initial before : ReopenImage} {durable : RunFiles}
    (reports : IntegrityBootstrapOpenReports initial before durable) {start after : ObservedMarkedState}
    (installed : reports.run = .ok ((start.writer.table, start.generation, start.writer.walBytes), start.writer.image)
      reports.toIntegrityOpenPaths.heldOwners)
    (observed : MarkedWriterState.observeReopen start.writer.table start.writer.image = some start.writer)
    (kept : start.durable = durable) {sessions : List MarkedSessionWrites}
    (trace : IntegrityDatabaseTrace reports.directory start sessions after) :
    MarkedSessionRetention sessions after.writer.history ∧ after.VersionedReady ∧ after.HasIntegrityManifest ∧
      ∃ reference, SnapshotWalReplay .empty after.writer.history reference ∧
        ∀ pin : SnapshotPin, pin ∈ after.writer.table.pins.active →
          (∀ key, after.writer.table.lookup pin.handle key = some (reference.table.lookup key pin.sequence)) ∧
          ∀ start stop, after.writer.table.range pin.handle start stop =
            some (reference.table.range start stop pin.sequence) := by
  obtain ⟨marker, markerRead⟩ := reports.markerRead
  obtain ⟨wal, walRead⟩ := reports.walRead
  obtain ⟨state, opened, _, _, recovered, valid, strict, emptyHistory, _, _, sameMap⟩ :=
    ObservedMarkedState.VersionedReady.bootstrapWithLock reports.fresh reports.attempts reports.acquisition
      reports.observes reports.manifestRead markerRead walRead reports.effects
      (fun absent => reports.created (absent ▸ walRead)) reports.synced
      (fun absent => reports.published (absent ▸ markerRead)) reports.unlock reports.cause
  have exactRun : reports.run = .ok ((state.writer.table, state.generation, state.writer.walBytes), state.writer.image)
      reports.toIntegrityOpenPaths.heldOwners := opened
  have same := ObservedMarkedState.eq_of_installation (EStateM.Result.ok.inj (exactRun.symm.trans installed)).1
    recovered observed (sameMap.trans kept.symm)
  subst start
  obtain ⟨suffix, history, retained, ready, format, reference, replayed, reads⟩ := trace.canonicalReads valid strict
  rw [emptyHistory, List.nil_append] at history
  exact ⟨history.symm ▸ retained, ready, format, reference, replayed, reads⟩

end Alvoki.WAL.Boundary
