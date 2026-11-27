import Alvoki.Storage.Disk.Proofs.Append.RetainedAppendRecovery
import Alvoki.Storage.Disk.Proofs.Keeper.SegmentedKeeperReachedReplacement
import Alvoki.Storage.Disk.WalSegmentCachedExtentReports

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WalSegmentCommit WAL.Boundary

/-- The selected keeper bytes come from an accepted bounded read. Power
loss chooses survivors after the old descriptor's reported sync, while
the repair still holds its lock and its last directory callback is pending. -/
structure DelayedKeeperReplacementPowerLoss (directory : DiskDirectory) (source : LockedFileState FileImage)
    (admits : Target → Prop) where
  report : DelayedKeeperSync
  attempt : BoundedReopenAttempt
  previous : WalInodeImage
  replacement : Nat
  bounded : Plan
  opened : Reopened
  physicalSize : Nat
  settled : FileImage
  reached : FileImage
  acquired : attempt.acquired = .ok true
  acquisition : TryLockObserves source.owners directory attempt.acquired
  reports : attempt.Reports directory source.image admits
  reading : attempt.prepare directory = .ok (bounded, opened, physicalSize)
  noLater : bounded.newer = []
  longer : bounded.keeperSize < physicalSize
  barrier : attempt.sync #[directory.path] source.image = .ok () settled
  renamed : (((steps [] true).take 4).forM
    (performPaths directory bounded attempt.removeFile throw attempt.write attempt.sync attempt.renameFile))
    settled = .ok () reached
  projected : source.image.withKeeperInodes previous = source.image
  oldTarget : report.captured.inode = previous.active
  distinct : previous.active ≠ replacement
  freshInode : replacement ∉ previous.crashBindings
  allowed : ∀ bytes ∈ report.outcomes, bytes = previous.visible previous.active ∨
    bytes ∈ previous.crashBytes previous.active
  pair : DirectoryPublication.Bindings
  keeper : Option ByteArray
  later : List Nat
  survived : let files := reached.withKeeperInodes (report.effect (previous.renameSynced replacement bounded.keeperBytes))
    pair ∈ files.directory.crashImages ∧ keeper ∈ files.keeper.crashImages ∧ later ∈ files.later.crashImages

namespace DelayedKeeperReplacementPowerLoss

variable {directory source admits}

def during (cut : DelayedKeeperReplacementPowerLoss directory source admits) : LockedFileState FileImage :=
  ⟨cut.reached.withKeeperInodes (cut.report.effect (cut.previous.renameSynced cut.replacement cut.bounded.keeperBytes)),
    source.owners.set (directory.file .lock) (some cut.attempt.descriptor)⟩

def crashed (cut : DelayedKeeperReplacementPowerLoss directory source admits) : LockedFileState FileImage :=
  ⟨cut.during.image.crash cut.pair cut.keeper cut.later, cut.during.owners.set (directory.file .lock) none⟩

private theorem reachesSurvivors (cut : DelayedKeeperReplacementPowerLoss directory source admits) :
    source.owners (directory.file .lock) = none ∧ cut.during.owners.Owns directory cut.attempt.descriptor ∧
    BoundedReopenTrace directory admits cut.during cut.crashed ∧
    ∃ target full, admits target ∧ Prepared source.image.allowVisibleKeeper target full ∧
      EffectTrace target source.image.allowVisibleKeeper cut.crashed.image := by
  obtain ⟨target, full, cover, _, admitted, selected, _, _, _, prepared, trace, covers, _⟩ :=
    cut.report.atBoundedReplacementBarrier cut.attempt directory source.image cut.previous cut.replacement
      cut.acquired cut.reports cut.reading cut.noLater cut.longer cut.barrier cut.renamed cut.projected
      cut.oldTarget cut.distinct cut.freshInode cut.allowed
  have physicalCover : cut.during.image.KeeperCrashCover cover := by
    simpa only [during, selected] using covers
  obtain ⟨pair, keeper, later⟩ := cut.survived
  have held : cut.during.owners.Owns directory cut.attempt.descriptor := by
    simp [LockOwners.Owns, during, LockOwners.set]
  exact ⟨cut.acquisition cut.acquired, held,
    .powerLoss .empty pair keeper later, target, full, admitted, prepared,
    physicalCover.crash trace pair keeper later⟩

private theorem continuesAuthorized {initial final : LockedFileState FileImage} {source : FileImage}
    {target : Target} {plan : Plan}
    (attempts : BoundedReopenTrace directory admits initial final)
    (admitted : admits target) (prepared : Prepared source target plan)
    (trace : EffectTrace target source initial.image)
    (unique : ∀ {left right}, admits left → admits right → left.pair = right.pair → left = right) :
    EffectTrace target source final.image := by
  have continueEffects {before after : FileImage} (earlier : EffectTrace target source before)
      (effects : after = before ∨ ∃ next plan, admits next ∧ Prepared before next plan ∧ EffectTrace next before after) :
      EffectTrace target source after := by
    obtain unchanged | ⟨next, _, admittedNext, preparedNext, applied⟩ := effects
    · simpa only [unchanged] using earlier
    have valid := earlier.valid prepared.pair prepared.keeperPrefix prepared.newer
    have same := unique admitted admittedNext (valid.selected.symm.trans preparedNext.pair)
    subst next
    exact earlier.trans applied
  induction attempts with
  | empty => exact trace
  | failed _ attempt acquisition _ reports ran ih =>
    exact continueEffects ih (attempt.errorFiles acquisition reports ran)
  | cachedPrefixFailed _ failure unchanged ih =>
    change EffectTrace target source failure.reached
    rw [unchanged]
    exact ih
  | cachedRejected _ _ ih => exact ih
  | cachedAuthorizationFailed _ failure admitted ih => exact continueEffects ih (failure.errorFiles admitted)
  | cachedRepairFailed _ attempt admitted prepared effects _ ih =>
    exact continueEffects ih (.inr ⟨_, _, admitted, prepared, by
      simpa only [CachedOpenAttempt.cleanupError_keepsFiles] using effects⟩)
  | repairInterrupted _ _ _ admitted prepared effects ih =>
    exact continueEffects ih (.inr ⟨_, _, admitted, prepared, effects⟩)
  | referenceDrops _ _ _ ih => exact ih
  | powerLoss _ metadata keeper later ih => exact .crash ih metadata keeper later

/-- A selected keeper layout supplies the raw read and effect reports for
the cached installation from the last observed retry image. -/
abbrev CachedInstallation {before : SegmentedWriterState} (failure : SegmentedAppendFailure directory before)
    (retry : LockedFileState FileImage) (nextDescriptor nextRef : Nat) (unlock : UnlockReport)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit) : Prop :=
    ∃ history, (history = before.history ∨ history = before.history ++ [failure.event]) ∧
      ∃ selected : CanonicalKeeperLayout retry.image history,
        let wal := before.wal.appendSelectedView retry.image.directory.active history
        ∀ raw : HealthyBoundedWalReports directory (retry.owners.set (directory.file .lock) (some nextDescriptor))
            nextDescriptor wal retry.image.directory.active selected.range.watermark before.published.durable selected.tail,
          ∀ sizes : SizedCheckpointRunReports directory raw.reports retry.image.directory.active.manifest before.published.durable,
            ∀ cached : CachedWalFileReports directory raw.reports wal selected.range.watermark selected.tail,
              sync #[directory.path] retry.image = .ok () retry.image.syncDirectory →
              (∀ action prior next,
                ReachesAction selected.target retry.image.syncDirectory selected.plan.finishActions action prior →
                prior.effect selected.target action = some next →
                performPaths directory selected.plan removeFile throw write sync renameFile action prior = .ok () next) →
              ∃ after, AppendRetryEndpoint directory before failure.event retry nextDescriptor
                (runOpenWithInstallation directory nextDescriptor nextRef (.ok true) unlock
                  (raw.reopenCached sizes cached removeFile write sync renameFile) retry) after ∧
                after.history = history ∧ after.RetainedReady directory nextDescriptor ∧
                after.checkpoint = before.checkpoint ∧ after.installed.generation = before.installed.generation

/-- Failed bounded opens, lock reference drops and further power losses
preserve the history authorized before the replacement-name barrier.
Healthy cached recovery uses the file image and lock ownership reached
by the entire retry prefix. -/
theorem reopensRetainedCachedAfter {before : SegmentedWriterState} {writer nextDescriptor nextRef : Nat}
    (ready : before.RetainedReady directory writer) (failure : SegmentedAppendFailure directory before)
    (cut : DelayedKeeperReplacementPowerLoss directory failure.released
      (AppendRetryTarget before.history failure.event before.wal.active.first))
    {retry : LockedFileState FileImage}
    (attempts : BoundedReopenTrace directory (AppendRetryTarget before.history failure.event before.wal.active.first)
      cut.crashed retry)
    (acquisition : TryLockObserves retry.owners directory (.ok true))
    (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < nextRef) (unlock : UnlockReport)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit) :
    BoundedReopenTrace directory (AppendRetryTarget before.history failure.event before.wal.active.first)
      cut.during retry ∧
    retry.image.directory.active = cut.pair ∧
    CachedInstallation failure retry nextDescriptor nextRef unlock removeFile write sync renameFile := by
  obtain ⟨_, _, poweredOff, target, _, admitted, prepared, firstCrash⟩ := cut.reachesSurvivors
  have trace := continuesAuthorized attempts admitted prepared firstCrash (fun a b pair => AppendRetryTarget.unique a b pair)
  have exactPair : retry.image.directory.active = cut.pair :=
    (trace.valid prepared.pair prepared.keeperPrefix prepared.newer).selected.trans
      (firstCrash.valid prepared.pair prepared.keeperPrefix prepared.newer).selected.symm
  obtain ⟨extended, fits, exactCut⟩ := failure.retainedCut ready
  let observed := (writeFilesAfter (runWriteEffects before.history failure.event failure.effects
    (before.wal.directory.staged .walBoundary))).reopenSegment before.wal.active.first before.history
    before.wal.directory.active.manifest
  have physical : before.wal.appendReopenFiles observed before.files.keeper.staged = failure.released.image := exactCut
  have observedPair : observed.directory.active = failure.released.image.directory.active :=
    congrArg (fun files : FileImage => files.directory.active) physical
  have initialRange : before.wal.directory.active.walRange = some ⟨before.target.range.watermark, before.history.length⟩ := by
    rw [ready.walPair, ← ready.resumed.through]
    exact before.target.decoded
  have canonical := ready.layout.afterRetainedAppendCut ready.valid initialRange failure.event fits failure.effects
    (before.wal.directory.staged .walBoundary) observed before.files.keeper.staged .live
  dsimp only at canonical
  rw [physical, observedPair] at canonical
  obtain ⟨history, allowed, manifest, _, readLayout, valid, layout, range, keeper, descriptors, offsets, _,
    choices, prefixValid, later⟩ := canonical
  have canonicalPrepared := layout.prepared choices prefixValid later
  have start : layout.target.first = before.wal.active.first := by
    change layout.keeper.first = before.wal.active.first
    rw [keeper]
    rfl
  have canonicalTarget : AppendRetryTarget before.history failure.event before.wal.active.first layout.target :=
    ⟨start, history, allowed, layout.through, start ▸ layout.chain.keeperBytes⟩
  have targetEq := AppendRetryTarget.unique admitted canonicalTarget (prepared.pair.symm.trans canonicalPrepared.pair)
  let widened : CanonicalKeeperLayout failure.released.image.allowVisibleKeeper history :=
    ⟨layout.range, layout.decoded, layout.through, layout.first, layout.sealed, layout.keeper,
      layout.chain, layout.covers, layout.tail, layout.visible⟩
  rw [targetEq] at trace
  have widenedTrace : EffectTrace widened.target failure.released.image.allowVisibleKeeper retry.image := trace
  obtain ⟨selected, same, sameRange, sameFirst, sameSeals, sameKeeper, retainedSeals, retryPrepared⟩ :=
    widenedTrace.canonicalRetryLayout widened canonicalPrepared.allowVisibleKeeper
  have retryPair : retry.image.directory.active = failure.released.image.directory.active := congrArg Target.pair same
  rw [← retryPair] at readLayout valid keeper descriptors offsets
  have stableManifest : retry.image.directory.active.manifest = before.target.pair.manifest :=
    (congrArg DirectoryPublication.Bindings.manifest retryPair).trans
      (manifest.trans (congrArg DirectoryPublication.Bindings.manifest ready.walPair))
  have chosen : SelectedIntegrityCheckpoint before.published.durable retry.image.directory.active.manifest before.checkpoint := by
    rw [stableManifest]
    exact ready.resumed.selected
  have generation : ((retry.image.directory.active.manifest.mapM fun bytes =>
      (Manifest.IntegrityCheckpoint.decode bytes).map (·.header.generation)).map (·.getD 0) : Except String UInt64) =
      .ok before.installed.generation := by
    rw [stableManifest]
    exact ready.resumed.generationRead
  have accepted : before.published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest := by
    rw [stableManifest]
    rcases allowed with rfl | rfl
    · exact ready.resumed.accepted
    · exact before.published.acceptsVersioned_extend_history ready.resumed.accepted fits
  have ordered : WAL.OrdinalsFrom 1 history := by
    rcases allowed with rfl | rfl
    · exact ready.resumed.ordered
    · exact extended
  have laterEmpty : retry.image.later.visible = [] := widenedTrace.emptyLater rfl
  have water : selected.range.watermark = before.target.range.watermark := by
    have exactRange : selected.range = ⟨before.target.range.watermark, history.length⟩ := sameRange.trans range
    have sameWatermark := congrArg MarkedWalRange.watermark exactRange
    exact sameWatermark
  let wal := before.wal.appendSelectedView retry.image.directory.active history
  have keeperEq : selected.keeper = wal.active := sameKeeper.trans keeper
  have selectedDescriptors : selected.sealed ++ [selected.keeper] = wal.readDescriptors selected.range.watermark := by
    rw [sameSeals, sameKeeper, water]
    exact descriptors
  have selectedOffsets : selectWalSegmentReads (wal.segments.map WalSegment.first) selected.range.watermark =
      some (selected.first, (wal.readDescriptors selected.range.watermark).map WalSegment.first) := by
    rw [sameFirst, water]
    exact offsets
  have retained : retry.image.kept = (wal.checkpointReopenFiles wal.directory none).kept := retainedSeals
  have active : wal.directory.active = selected.target.pair := rfl
  refine ⟨poweredOff.trans attempts, exactPair, history, allowed, selected, ?_⟩
  intro reportedWal raw sizes cached settles healthy
  have opened := runOpenWithInstallation_appendLayout readLayout ordered selected keeperEq selectedDescriptors
    selectedOffsets (same.symm ▸ retryPrepared) laterEmpty accepted generation raw liveRefs fresh acquisition unlock
    removeFile write sync renameFile settles healthy
  have bounded := raw.reopenCached_eq sizes cached readLayout valid (List.mem_cons_self ..) selected.decoded rfl
    selected.through chosen removeFile write sync renameFile
  obtain ⟨session, final, after, ran, path, lock, phase, files, owners, afterWal, target, exactHistory, gen, durable, next⟩ :=
    opened.writerRetained readLayout valid ready.spans active (congrArg WalSegment.first keeperEq) retained
  have exactCheckpoint : after.checkpoint = before.checkpoint := by
    have loaded := next.resumed.selected
    rw [durable, target] at loaded
    exact Except.ok.inj ((raw.readCheckpoint loaded).symm.trans (raw.readCheckpoint chosen))
  have installedWal : after.wal = { before.wal.appendSelectedView retry.image.directory.active after.history with
      directory := after.files.directory } := by rw [afterWal, files, exactHistory]
  rw [bounded]
  refine ⟨after, ⟨⟨session, final, ran, path, lock, phase, files, owners⟩, exactHistory ▸ allowed, installedWal,
    target ▸ rfl, ?_, next.resumed.through, next.resumed.contents, durable, next.manifestFiles, next.resumed.selected⟩,
    exactHistory, next, exactCheckpoint, gen⟩
  rw [target, same]
  exact start

/-- A healthy cached open immediately after the reached old-keeper sync
and survivor selection installs the strict checkpoint and the history
authorized by the append's marker. -/
theorem reopensRetainedCached {before : SegmentedWriterState} {writer nextDescriptor nextRef : Nat}
    (ready : before.RetainedReady directory writer) (failure : SegmentedAppendFailure directory before)
    (cut : DelayedKeeperReplacementPowerLoss directory failure.released
      (AppendRetryTarget before.history failure.event before.wal.active.first))
    (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < nextRef) (unlock : UnlockReport)
    (removeFile : FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array FilePath → EStateM IO.Error FileImage Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error FileImage Unit) :
    let retry := cut.crashed
    BoundedReopenTrace directory (AppendRetryTarget before.history failure.event before.wal.active.first)
      cut.during retry ∧
    CachedInstallation failure retry nextDescriptor nextRef unlock removeFile write sync renameFile := by
  have acquisition : TryLockObserves cut.crashed.owners directory (.ok true) := by
    simp [TryLockObserves, crashed, LockOwners.set]
  obtain ⟨crash, _, installed⟩ :=
    reopensRetainedCachedAfter ready failure cut .empty acquisition liveRefs fresh unlock removeFile write sync renameFile
  exact ⟨crash, installed⟩

end DelayedKeeperReplacementPowerLoss

end Alvoki.Storage.DiskSession
