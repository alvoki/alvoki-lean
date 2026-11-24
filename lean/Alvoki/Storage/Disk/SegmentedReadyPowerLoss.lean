import Alvoki.Storage.Disk.RotationAuthorityRetry
import Alvoki.Storage.Disk.SegmentedCleanReopen

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- A power loss selects the durable bindings and ends the observed local
lock lifetime. The settled writer determines the unique selected pair and
keeper bytes. Staged scratch files are forgotten. -/
def SegmentedWriterState.powerLossFiles (state : SegmentedWriterState) (directory : DiskDirectory) :
    LockedFileState FileImage :=
  ⟨state.files.crash state.target.pair (some state.target.trimmed) [],
    state.owners.set (directory.file .lock) none⟩

theorem SegmentedWriterState.Ready.powerLossTrace {directory : DiskDirectory} {descriptor : Nat}
    {state : SegmentedWriterState} (ready : state.Ready directory descriptor) (admits : Target → Prop) :
    BoundedReopenTrace directory admits ⟨state.files, state.owners⟩ (state.powerLossFiles directory) :=
  .powerLoss .empty
    (ready.resumed.ready.settled ▸ List.mem_singleton_self _)
    (ready.resumed.ready.keeperDurable ▸ List.mem_singleton_self _)
    (ready.resumed.ready.pruned.2 ▸ List.mem_singleton_self _)

private theorem Target.eq_of_fields {left right : Target} (pair : left.pair = right.pair)
    (range : left.range = right.range) (first : left.first = right.first) (trimmed : left.trimmed = right.trimmed) :
    left = right := by
  cases left
  cases right
  cases pair
  cases range
  cases first
  cases trimmed
  rfl

private theorem SegmentedWriterState.Ready.powerLossLayout {directory : DiskDirectory} {descriptor : Nat}
    {state : SegmentedWriterState} (ready : state.Ready directory descriptor) :
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
    ready.layout.checkpointReopenLayout ready.walValid (.crash durable) decoded ready.resumed.through none
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

theorem installs (report : SegmentedReadyPowerLossReport directory before oldDescriptor nextDescriptor)
    (observed : report.Valid) (ready : before.Ready directory oldDescriptor) :
    ∃ after, report.Installs after ∧ after.Ready directory nextDescriptor := by
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
  have healthy : ∀ action prior next,
      ReachesAction selected.target report.retry.image.syncDirectory selected.plan.finishActions action prior →
      prior.effect selected.target action = some next →
      performPaths directory selected.plan report.removeFile throw report.write report.sync report.renameFile action prior =
        .ok () next := by
    intro action prior next reached applied
    obtain ⟨priorActions, suffix, schedule, ran⟩ := reached
    rw [Plan.finishActions, ite_eq_left aligned] at schedule
    have sizes := congrArg List.length schedule
    simp only [List.length_append, List.length_cons, List.length_nil] at sizes
    have beforeHead : priorActions = [] := List.length_eq_zero_iff.mp (by omega)
    subst priorActions
    have atHead : action = .syncKeeper := (List.cons.inj schedule).1.symm
    subst action
    have firstImage : prior = report.retry.image.syncDirectory := (Option.some.inj ran).symm
    subst prior
    have lastImage : next = report.retry.image.syncDirectory.syncKeeper := (Option.some.inj applied).symm
    subst next
    change report.sync #[directory.file (.walSegment selected.plan.keeper)] report.retry.image.syncDirectory = _
    rw [show selected.plan.keeper = before.wal.active.first from congrArg WalSegment.first keeperExact]
    exact observed.syncKeeper
  let raw : HealthyBoundedWalReports directory (report.retry.owners.set (directory.file .lock) (some nextDescriptor))
      nextDescriptor before.wal report.retry.image.directory.active selected.range.watermark before.published.durable
      selected.tail :=
    { report.raw with
      sealed := by simpa only [rangeExact] using report.raw.sealed
      keeper := by simpa only [tailExact] using report.raw.keeper }
  have installed := runOpenWithInstallation_appendLayout (owners := report.retry.owners)
    ready.layout ready.resumed.ordered selected keeperExact descriptors offsets currentPrepared empty
    (by rw [selectedPair]; exact ready.resumed.accepted) (by rw [selectedPair]; exact ready.generationRead)
    raw report.liveRefs observed.fresh observed.acquisition report.unlock report.removeFile report.write report.sync
    report.renameFile observed.syncDirectory healthy
  obtain ⟨_, _, _, _, checkpoint, table, model, session, final, ran, loaded, _, _, _, _, phase,
    durable, kept, owned, _, bounds, refines, represents, _, _, _, _⟩ := installed
  have loadedNow : SelectedIntegrityCheckpoint before.published.durable report.retry.image.directory.active.manifest
      checkpoint := by
    rw [selectedPair]
    exact exactTarget ▸ loaded
  have loadedOld : SelectedIntegrityCheckpoint before.published.durable report.retry.image.directory.active.manifest
      before.checkpoint := by
    rw [selectedPair]
    exact ready.resumed.selected
  have sameCheckpoint : checkpoint = before.checkpoint :=
    Except.ok.inj ((report.raw.readCheckpoint loadedNow).symm.trans (report.raw.readCheckpoint loadedOld))
  let next := reopenedWriter before table final
  have phaseExact : session.phase = .ready next.installed := by
    simpa only [next, reopenedWriter, SegmentedWriterState.ofReopen, exactTarget,
      ← ready.resumed.bytes, ← ready.resumed.keeper] using phase
  have reopened : report.attempt.run directory report.retry = .ok session final := ran
  have keptExact : final.image.kept = before.files.kept := kept.trans trace.keepsSealed
  have nextReady : next.Ready directory nextDescriptor := by
    refine ⟨⟨exactTarget ▸ durable, ready.resumed.through, ready.resumed.keeper, ready.resumed.bytes,
      ready.resumed.contents, ready.resumed.generation, ?_, ready.resumed.accepted, ready.resumed.ordered,
      bounds, ⟨model, refines, represents⟩⟩, ?_, ready.chain, rfl, keptExact.trans ready.sealedFiles,
      ready.active, rfl, owned⟩
    · change SelectedIntegrityCheckpoint before.published.durable before.target.pair.manifest before.checkpoint
      rw [← sameCheckpoint, ← exactTarget]
      exact loaded
    · exact ⟨ready.layout.ordered, ready.layout.forward, ready.layout.activeEnd, ready.layout.activeBytes⟩
  exact ⟨next, ⟨ready.powerLossTrace _, session, final, table, reopened, phaseExact, rfl⟩, nextReady⟩

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
