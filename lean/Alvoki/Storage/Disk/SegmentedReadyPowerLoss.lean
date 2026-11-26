import Alvoki.Storage.Disk.RotationAuthorityRetry
import Alvoki.Storage.Disk.SegmentedCleanReopen
import Alvoki.Storage.Disk.RetainedWriterReopen

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- A power loss selects the durable bindings and ends the observed local
lock lifetime. The settled writer determines the unique selected pair and
keeper bytes. Staged scratch files are forgotten. -/
def SegmentedWriterState.powerLossFiles (state : SegmentedWriterState) (directory : DiskDirectory) :
    LockedFileState FileImage :=
  ⟨state.files.crash state.target.pair (some state.target.trimmed) [],
    state.owners.set (directory.file .lock) none⟩

theorem SegmentedWriterState.RetainedReady.powerLossTrace {directory : DiskDirectory} {descriptor : Nat}
    {state : SegmentedWriterState} (ready : state.RetainedReady directory descriptor) (admits : Target → Prop) :
    BoundedReopenTrace directory admits ⟨state.files, state.owners⟩ (state.powerLossFiles directory) :=
  .powerLoss .empty
    (ready.resumed.ready.settled ▸ List.mem_singleton_self _)
    (ready.resumed.ready.keeperDurable ▸ List.mem_singleton_self _)
    (ready.resumed.ready.pruned.2 ▸ List.mem_singleton_self _)

theorem SegmentedWriterState.Ready.powerLossTrace {directory : DiskDirectory} {descriptor : Nat}
    {state : SegmentedWriterState} (ready : state.Ready directory descriptor) (admits : Target → Prop) :
    BoundedReopenTrace directory admits ⟨state.files, state.owners⟩ (state.powerLossFiles directory) :=
  ready.toRetained.powerLossTrace admits

theorem Target.eq_of_fields {left right : Target} (pair : left.pair = right.pair)
    (range : left.range = right.range) (first : left.first = right.first) (trimmed : left.trimmed = right.trimmed) :
    left = right := by
  cases left
  cases right
  cases pair
  cases range
  cases first
  cases trimmed
  rfl

/-- Recover the canonical keeper and sealed read plan at a settled writer's
power-loss image, before admitting any reopen effects. -/
theorem SegmentedWriterState.RetainedReady.powerLossLayout {directory : DiskDirectory} {descriptor : Nat}
    {state : SegmentedWriterState} (ready : state.RetainedReady directory descriptor) :
    let files := (state.powerLossFiles directory).image
    ∃ selected : CanonicalKeeperLayout files state.history,
      selected.target = state.target ∧ selected.keeper = state.wal.active ∧
      selected.sealed ++ [selected.keeper] = state.wal.readDescriptors selected.range.watermark ∧
      selectWalSegmentReads (state.wal.segments.map WalSegment.first) selected.range.watermark =
        some (selected.first, (state.wal.readDescriptors selected.range.watermark).map WalSegment.first) ∧
      Prepared files selected.target selected.plan := by
  intro files
  have durable : state.target.pair ∈ state.wal.directory.crashImages := by
    rw [← ready.directoryFiles, ready.resumed.ready.settled]
    exact List.mem_singleton_self _
  have bytes : state.target.trimmed = state.wal.active.bytes := by
    rw [ready.resumed.contents, ready.active, ready.layout.activeBytes]
  have exactFiles : state.wal.checkpointReopenFiles (.settled state.target.pair) none = files := by
    simp [files, SegmentedWriterState.powerLossFiles, WalSegmentImage.checkpointReopenFiles,
      FileImage.crash, Publication.Image.settled, bytes, ready.sealedFiles]
  have decoded : (DirectoryPublication.Image.settled state.target.pair).active.walRange =
      some state.target.range := state.target.decoded
  obtain ⟨selected, range, keeper, _, descriptors, offsets, _, choices, prefixes, names⟩ :=
    ready.layout.checkpointReopenLayout ready.valid (.crash durable) decoded ready.resumed.through none
  have target : selected.target = state.target := Target.eq_of_fields rfl range
    ((congrArg WalSegment.first keeper).trans ready.active.symm)
    ((congrArg WalSegment.bytes keeper).trans bytes.symm)
  have prepared := selected.prepared choices prefixes (range.symm ▸ names)
  rw [← exactFiles]
  exact ⟨selected, target, keeper, range.symm ▸ descriptors, range.symm ▸ offsets, prepared⟩

/-- A retry can sync the keeper or replace it with its selected bytes.
When all original outcomes have those bytes, every retry still does. -/
private theorem EffectTrace.exactKeeper {initial after : FileImage} {target : Target}
    (trace : EffectTrace target initial after)
    (exact : initial.keeper.Valid (· = some target.trimmed)) : after.keeper.Valid (· = some target.trimmed) := by
  induction trace with
  | authorized => exact exact
  | unlink _ _ prior | syncPruned _ prior => exact prior
  | scratch _ prior => exact ⟨prior.hasCrashImage, prior.activeValid, prior.crashValid⟩
  | replace _ _ ran prior =>
    unfold FileImage.replacementCut at ran
    obtain ⟨keeper, applied, rfl⟩ := Option.map_eq_some_iff.mp ran
    have replaced := Publication.Image.execute_cut_valid prior rfl _ applied
    split <;> exact replaced
  | aligned _ _ _ prior =>
    refine ⟨by simp [FileImage.syncKeeper], prior.activeValid, ?_⟩
    intro candidate survives
    exact (List.mem_singleton.mp survives).trans prior.activeValid
  | crash _ _ keeper _ prior => exact Publication.Image.settled_valid (prior.crashValid _ keeper)

/-- A loss of power from a settled writer, followed by the exact bounded
attempts and read reports for its next healthy reopen. -/
structure SegmentedReadyPowerLossReport (directory : DiskDirectory) (before : SegmentedWriterState)
    (oldDescriptor nextDescriptor : Nat) where
  retry : LockedFileState FileImage
  failures : BoundedReopenTrace directory (fun target => target = before.target) (before.powerLossFiles directory) retry
  nextRef : Nat
  liveRefs : List Nat
  unlock : UnlockReport
  raw : HealthyCheckpointCutReports directory (retry.owners.set (directory.file .lock) (some nextDescriptor))
    nextDescriptor before.wal retry.image.directory.active before.target.range.watermark before.published.durable
  removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit)
  write : FilePath → ByteArray → EStateM IO.Error FileImage Unit
  sync : Array FilePath → EStateM IO.Error FileImage Unit
  renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit

namespace SegmentedReadyPowerLossReport

variable {directory : DiskDirectory} {before : SegmentedWriterState} {oldDescriptor nextDescriptor : Nat}

def attempt (report : SegmentedReadyPowerLossReport directory before oldDescriptor nextDescriptor) : BoundedReopenAttempt :=
  report.raw.openAttempt report.nextRef report.unlock report.removeFile report.write report.sync report.renameFile

structure Valid (report : SegmentedReadyPowerLossReport directory before oldDescriptor nextDescriptor) : Prop where
  fresh : ∀ ref ∈ report.liveRefs, ref < report.nextRef
  acquisition : TryLockObserves report.retry.owners directory (.ok true)
  syncDirectory : report.sync #[directory.path] report.retry.image = .ok () report.retry.image.syncDirectory
  syncKeeper : report.sync #[directory.file (.walSegment before.wal.active.first)] report.retry.image.syncDirectory =
    .ok () report.retry.image.syncDirectory.syncKeeper

private def reopenedWriter (before : SegmentedWriterState) (table : PackedTable) (final : LockedFileState FileImage) :
    SegmentedWriterState :=
  SegmentedWriterState.ofReopen { before.installed with table } before.wal before.history
    before.published before.target before.checkpoint final

structure Installs (report : SegmentedReadyPowerLossReport directory before oldDescriptor nextDescriptor)
    (after : SegmentedWriterState) : Prop where
  initialLoss : BoundedReopenTrace directory (fun target => target = before.target) ⟨before.files, before.owners⟩
    (before.powerLossFiles directory)
  openEffect : ∃ session final table,
    report.attempt.run directory report.retry = .ok session final ∧
    session.phase = .ready (reopenedWriter before table final).installed ∧ after = reopenedWriter before table final

private theorem installsRetained_exact (report : SegmentedReadyPowerLossReport directory before oldDescriptor nextDescriptor)
    (observed : report.Valid) (ready : before.RetainedReady directory oldDescriptor) :
    report.retry.image.directory.active = before.target.pair ∧
      ∃ after, report.Installs after ∧ after.RetainedReady directory nextDescriptor := by
  obtain ⟨source, sourceTarget, sourceKeeper, sourceDescriptors, sourceOffsets, sourcePrepared⟩ :=
    ready.powerLossLayout
  have trace := report.failures.effectsAfterFixedAuthority (by rfl)
  have recovery : EffectTrace source.target (before.powerLossFiles directory).image report.retry.image :=
    sourceTarget.symm ▸ trace
  obtain ⟨selected, target, range, first, sealed, keeper, _, prepared⟩ :=
    recovery.canonicalRetryLayout source sourcePrepared
  have exactTarget : selected.target = before.target := target.trans sourceTarget
  have rangeExact : selected.range = before.target.range := congrArg Target.range exactTarget
  have keeperExact : selected.keeper = before.wal.active := keeper.trans sourceKeeper
  have selectedPair : report.retry.image.directory.active = before.target.pair :=
    prepared.pair.trans (congrArg Target.pair sourceTarget)
  have bytes : before.target.trimmed = before.wal.active.bytes := by
    rw [ready.resumed.contents, ready.active, ready.layout.activeBytes]
  have visible := (EffectTrace.exactKeeper trace (Publication.Image.settled_valid rfl)).activeValid
  have tailExact : selected.tail = ByteArray.empty := by
    have same := Option.some.inj (selected.visible.symm.trans visible)
    rw [keeperExact, bytes] at same
    apply (ByteArray.append_right_inj before.wal.active.bytes).mp
    simpa only [ByteArray.append_empty] using same
  have empty := trace.emptyLater (by rfl)
  have descriptors : selected.sealed ++ [selected.keeper] = before.wal.readDescriptors selected.range.watermark := by
    rw [sealed, keeper, range]
    exact sourceDescriptors
  have offsets : selectWalSegmentReads (before.wal.segments.map WalSegment.first) selected.range.watermark =
      some (selected.first, (before.wal.readDescriptors selected.range.watermark).map WalSegment.first) := by
    rw [range, first]
    exact sourceOffsets
  have currentPrepared : Prepared report.retry.image selected.target selected.plan := target.symm ▸ prepared
  have exactSize : selected.plan.keeperBytes.size = selected.plan.keeperSize := by
    change (selected.keeper.bytes ++ selected.tail).size = _
    rw [tailExact, ByteArray.append_empty]
    exact selected.target.trimmedSize
  have aligned : selected.plan.alignedWithoutPrune = true := by
    have noNames : selected.plan.newer = [] := empty
    simp only [Plan.alignedWithoutPrune, currentPrepared.valid, noNames, List.isEmpty_nil, exactSize,
      beq_self_eq_true, Bool.and_self]
  have healthy := finishActions_aligned_success (target := selected.target)
    (directory := directory) (sync := report.sync) (initial := report.retry.image.syncDirectory) aligned report.removeFile
    report.write report.renameFile
    (by simpa only [show selected.plan.keeper = before.wal.active.first from congrArg WalSegment.first keeperExact]
      using observed.syncKeeper)
  let raw : HealthyBoundedWalReports directory (report.retry.owners.set (directory.file .lock) (some nextDescriptor))
      nextDescriptor before.wal report.retry.image.directory.active selected.range.watermark before.published.durable
      selected.tail :=
    { report.raw with
      sealed := by simpa only [rangeExact] using report.raw.sealed
      keeper := by simpa only [tailExact] using report.raw.keeper }
  have installed := runOpenWithInstallation_appendLayout (owners := report.retry.owners)
    ready.layout ready.resumed.ordered selected keeperExact descriptors offsets currentPrepared empty
    (by rw [selectedPair]; exact ready.resumed.accepted) (by rw [selectedPair]; exact ready.resumed.generationRead)
    raw report.liveRefs observed.fresh observed.acquisition report.unlock report.removeFile report.write report.sync
    report.renameFile observed.syncDirectory healthy
  have availableSeals := trace.keepsSealed.trans ready.sealedFiles
  rw [exactTarget] at installed
  obtain ⟨session, final, writer, ran, _, _, phase, files, owners, wal, target, history, generation, durable, nextReady⟩ :=
    installed.writerRetained ready.layout ready.valid ready.spans ready.walPair ready.active availableSeals
  have loadedNow : SelectedIntegrityCheckpoint before.published.durable report.retry.image.directory.active.manifest
      writer.checkpoint := by
    rw [selectedPair, ← target, ← durable]
    exact nextReady.resumed.selected
  have loadedOld : SelectedIntegrityCheckpoint before.published.durable report.retry.image.directory.active.manifest
      before.checkpoint := by
    rw [selectedPair]
    exact ready.resumed.selected
  have sameCheckpoint : writer.checkpoint = before.checkpoint :=
    Except.ok.inj ((report.raw.readCheckpoint loadedNow).symm.trans (report.raw.readCheckpoint loadedOld))
  let next := reopenedWriter before writer.installed.table final
  have count : writer.installed.walBytes = before.installed.walBytes := by
    rw [nextReady.resumed.bytes, history, ready.resumed.bytes]
  have active : writer.installed.activeFirst = before.installed.activeFirst := by
    rw [nextReady.resumed.keeper, target, ← ready.resumed.keeper]
  have installedExact : writer.installed = next.installed := by
    change Installed.mk writer.installed.table writer.installed.generation writer.installed.walBytes
        writer.installed.activeFirst = Installed.mk writer.installed.table before.installed.generation
        before.installed.walBytes before.installed.activeFirst
    rw [Installed.mk.injEq]
    exact ⟨rfl, generation, count, active⟩
  have published : writer.published = next.published := by
    change CheckpointPublication.Image.mk writer.published.manifest writer.published.durable =
      CheckpointPublication.Image.mk (final.image.directory.project .manifest) before.published.durable
    rw [CheckpointPublication.Image.mk.injEq]
    exact ⟨nextReady.manifestFiles.trans (congrArg (fun files : FileImage => files.directory.project .manifest) files),
      durable⟩
  have exactWriter : writer = next := by
    change SegmentedWriterState.mk writer.installed writer.wal writer.history writer.files writer.published
        writer.target writer.checkpoint writer.owners =
      SegmentedWriterState.mk next.installed next.wal next.history next.files next.published
        next.target next.checkpoint next.owners
    rw [SegmentedWriterState.mk.injEq]
    exact ⟨installedExact, wal, history, files, published, target, sameCheckpoint, owners⟩
  exact ⟨selectedPair, next, ⟨ready.powerLossTrace _, session, final, writer.installed.table, ran, installedExact ▸ phase, rfl⟩,
    exactWriter ▸ nextReady⟩

theorem installsRetained (report : SegmentedReadyPowerLossReport directory before oldDescriptor nextDescriptor)
    (observed : report.Valid) (ready : before.RetainedReady directory oldDescriptor) :
    ∃ after, report.Installs after ∧ after.RetainedReady directory nextDescriptor :=
  (report.installsRetained_exact observed ready).2

/-- A settled writer survives power loss and bounded retries with the same
checkpoint and WAL. The following cached open installs their exact table. -/
theorem installsRetainedCached (report : SegmentedReadyPowerLossReport directory before oldDescriptor nextDescriptor)
    (observed : report.Valid) (ready : before.RetainedReady directory oldDescriptor)
    (sizes : SizedCheckpointRunReports directory report.raw.reports report.retry.image.directory.active.manifest
      before.published.durable)
    (cached : CachedWalFileReports directory report.raw.reports before.wal before.target.range.watermark ByteArray.empty) :
    ∃ after session final,
      report.Installs after ∧
      runOpenWithInstallation directory nextDescriptor report.nextRef (.ok true) report.unlock
        (report.raw.reopenCached sizes cached report.removeFile report.write report.sync report.renameFile)
        report.retry = .ok session final ∧
      session.phase = .ready after.installed ∧ final.image = after.files ∧ final.owners = after.owners := by
  obtain ⟨pair, after, endpoint, _⟩ := report.installsRetained_exact observed ready
  have decoded : report.retry.image.directory.active.walRange = some before.target.range :=
    pair.symm ▸ before.target.decoded
  have chosen : before.wal.Selects report.retry.image.directory.active := by
    rw [pair, ← ready.walPair]
    exact List.mem_cons_self ..
  have checkpoint : SelectedIntegrityCheckpoint before.published.durable report.retry.image.directory.active.manifest
      before.checkpoint := pair.symm ▸ ready.resumed.selected
  have same := report.raw.reopenCached_eq sizes cached ready.layout ready.valid chosen decoded rfl
    ready.resumed.through checkpoint report.removeFile report.write report.sync report.renameFile
  obtain ⟨session, final, _, ran, phase, exactWriter⟩ := endpoint.openEffect
  refine ⟨after, session, final, endpoint, ?_, exactWriter.symm ▸ phase, ?_, ?_⟩
  · rw [same]
    exact ran
  · rw [exactWriter]
    rfl
  · rw [exactWriter]
    rfl

theorem installs (report : SegmentedReadyPowerLossReport directory before oldDescriptor nextDescriptor)
    (observed : report.Valid) (ready : before.Ready directory oldDescriptor) :
    ∃ after, report.Installs after ∧ after.Ready directory nextDescriptor := by
  obtain ⟨after, endpoint, next⟩ := report.installsRetained observed ready.toRetained
  have chain : WalSegment.Chain after.history 0 after.wal.segments := by
    obtain ⟨_, _, _, _, _, rfl⟩ := endpoint.openEffect
    exact ready.chain
  exact ⟨after, endpoint, ⟨next.resumed, next.layout, chain, next.directoryFiles, next.sealedFiles,
    next.active, next.manifestFiles, next.held⟩⟩

theorem Installs.unique {report : SegmentedReadyPowerLossReport directory before oldDescriptor nextDescriptor}
    {left right : SegmentedWriterState} (a : report.Installs left) (b : report.Installs right) : left = right := by
  obtain ⟨_, _, leftTable, leftOpen, leftPhase, rfl⟩ := a.openEffect
  obtain ⟨_, _, rightTable, rightOpen, rightPhase, rfl⟩ := b.openEffect
  obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj (leftOpen.symm.trans rightOpen)
  have same : leftTable = rightTable := congrArg Installed.table (Phase.ready.inj (leftPhase.symm.trans rightPhase))
  rw [same]

theorem Installs.preservesReady {report : SegmentedReadyPowerLossReport directory before oldDescriptor nextDescriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after) (observed : report.Valid)
    (ready : before.Ready directory oldDescriptor) : after.Ready directory nextDescriptor := by
  obtain ⟨_, exactEndpoint, next⟩ := report.installs observed ready
  exact exactEndpoint.unique endpoint ▸ next

theorem Installs.preservesRetained {report : SegmentedReadyPowerLossReport directory before oldDescriptor nextDescriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after) (observed : report.Valid)
    (ready : before.RetainedReady directory oldDescriptor) : after.RetainedReady directory nextDescriptor := by
  obtain ⟨_, exactEndpoint, next⟩ := report.installsRetained observed ready
  exact exactEndpoint.unique endpoint ▸ next

theorem Installs.preservesChain {report : SegmentedReadyPowerLossReport directory before oldDescriptor nextDescriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after)
    (chain : WalSegment.Chain before.history 0 before.wal.segments) :
    WalSegment.Chain after.history 0 after.wal.segments := by
  obtain ⟨_, _, _, _, _, rfl⟩ := endpoint.openEffect
  exact chain

theorem Installs.history {report : SegmentedReadyPowerLossReport directory before oldDescriptor nextDescriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after) : after.history = before.history := by
  obtain ⟨_, _, _, _, _, rfl⟩ := endpoint.openEffect
  rfl

theorem Installs.generation {report : SegmentedReadyPowerLossReport directory before oldDescriptor nextDescriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after) :
    after.installed.generation = before.installed.generation := by
  obtain ⟨_, _, _, _, _, rfl⟩ := endpoint.openEffect
  rfl

end SegmentedReadyPowerLossReport

end Alvoki.Storage.DiskSession
