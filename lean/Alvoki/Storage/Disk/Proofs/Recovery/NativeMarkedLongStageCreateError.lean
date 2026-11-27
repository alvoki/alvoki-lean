import Alvoki.Storage.Disk.Proofs.Recovery.NativeMarkedFirstBarrierWork
import Alvoki.Storage.Disk.Proofs.Filesystem.StagedHandleCustody

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair WAL.Boundary

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {reads : CapturedMarkedReadReports admission layout published}

private abbrev Handle := DescriptorInventory × DescriptorSlot × Nat
private abbrev RepairState := CensusDirectoryCache × CensusOpenState

private def settledFiles (admission : CensusOpenAdmissionReports input directory inventory retry) :
    LockedFileState FileImage := { admission.held with image := retry.image.syncDirectory }

/-- A long keeper with no later names reaches the fresh WAL.next
create after the temporary old handle closes and both directory
barriers return. A reported error before effect leaves the staging
namespace and census unchanged and returns no handle to the cache. -/
structure NativeMarkedLongStageCreateError (reads : CapturedMarkedReadReports admission layout published)
    (keeper : CapturedKeeperOpenReports reads) where
  longer : layout.keeper.bytes.size < reads.wal.keeper.calls.metadata.byteSize.toNat
  noLater : retry.image.later.visible = []
  finalizeKeeper : Handle → EStateM IO.Error CensusOpenState Unit
  finalized : dataErrorDropState finalizeKeeper
      (reads.wal.keeper.calls.inventory, reads.wal.keeper.calls.slot, 0) (keeper.afterRead, admission.held) =
    (keeper.afterRead.afterDrops [reads.wal.keeper.calls.slot.closeEvent], admission.held)
  openRead : FilePath → EStateM IO.Error CensusOpenState Handle
  fsync : Handle → EStateM IO.Error CensusOpenState Unit
  afterAuthorize : List LockReferenceDrop
  afterSuffix : List LockReferenceDrop
  authorized : fsync (admission.reached, admission.cached, 0)
      (keeper.afterRead.afterDrops [reads.wal.keeper.calls.slot.closeEvent], admission.held) =
    .ok () ((keeper.afterRead.afterDrops [reads.wal.keeper.calls.slot.closeEvent]).afterDrops afterAuthorize,
      settledFiles admission)
  suffix : fsync (admission.reached, admission.cached, 0)
      ((keeper.afterRead.afterDrops [reads.wal.keeper.calls.slot.closeEvent]).afterDrops afterAuthorize,
        settledFiles admission) =
    .ok () (((keeper.afterRead.afterDrops [reads.wal.keeper.calls.slot.closeEvent]).afterDrops afterAuthorize).afterDrops
      afterSuffix, settledFiles admission)
  ownerLive : admission.owner ∈ (((keeper.afterRead.afterDrops [reads.wal.keeper.calls.slot.closeEvent]).afterDrops
    afterAuthorize).afterDrops afterSuffix).slots
  directoryLive : admission.cached ∈ (((keeper.afterRead.afterDrops [reads.wal.keeper.calls.slot.closeEvent]).afterDrops
    afterAuthorize).afterDrops afterSuffix).slots
  scope : DirectoryReadNamespace
  names : ∀ name, scope.child admission.root name = admission.view.child admission.root name
  scratchAbsent : scope.child admission.root "WAL.next" = none
  tryCreate : FilePath → EStateM IO.Error (CensusOpenState × DirectoryReadNamespace) (Except IO.Error Handle)
  detach : FilePath → EStateM IO.Error CensusOpenState Unit
  create : FilePath → EStateM IO.Error CensusOpenState Handle
  write : Handle → ByteArray → EStateM IO.Error CensusOpenState Unit
  flush : Handle → EStateM IO.Error CensusOpenState Unit
  remove : FilePath → EStateM IO.Error RepairState (Except IO.Error Unit)
  rename : FilePath → FilePath → EStateM IO.Error RepairState Unit
  cause : IO.Error
  notConflict : ∀ path message, cause ≠ .alreadyExists path 17 message
  failed : let atIssue :=
      (((keeper.afterRead.afterDrops [reads.wal.keeper.calls.slot.closeEvent]).afterDrops afterAuthorize).afterDrops
        afterSuffix, settledFiles admission)
    tryCreate (directory.file .stagedWal) (atIssue, scope) = .ok (.error cause) (atIssue, scope)

namespace NativeMarkedLongStageCreateError

variable {keeper : CapturedKeeperOpenReports reads} (seen : NativeMarkedLongStageCreateError reads keeper)

def afterRead : DescriptorInventory :=
  keeper.afterRead.afterDrops [reads.wal.keeper.calls.slot.closeEvent]

def atSuffix : CensusOpenState := ((afterRead (keeper := keeper)).afterDrops seen.afterAuthorize, settledFiles admission)

def atStage : CensusOpenState := (seen.atSuffix.1.afterDrops seen.afterSuffix, settledFiles admission)

def readKeeper (path : FilePath) (count physical : Nat) : EStateM IO.Error RepairState ByteArray :=
  fun initial => match keeper.readKeeperAt path count physical initial with
  | .error cause reached => .error cause reached
  | .ok bytes (cache, census, files) =>
    let reached := (census, files)
    let handle := (reads.wal.keeper.calls.inventory, reads.wal.keeper.calls.slot, 0)
    .ok bytes (cache, if count < physical then dataErrorDropState seen.finalizeKeeper handle reached else reached)

/-- The reported close consumes the exact description just read by the
long keeper path. Its returned file state enters the authorization sync. -/
theorem readsAndCloses :
    seen.readKeeper (directory.file (.walSegment layout.keeper.first)) layout.keeper.bytes.size
      reads.wal.keeper.calls.metadata.byteSize.toNat (admission.cache, keeper.atOpen, admission.held) =
    .ok layout.keeper.bytes (admission.cache, afterRead (keeper := keeper), admission.held) := by
  have read := keeper.readsLong seen.longer
  unfold CapturedKeeperOpenReports.readKeeper at read
  simp only [readKeeper, read, seen.longer, ite_true, seen.finalized, afterRead]

def sync : Array FilePath → EStateM IO.Error RepairState Unit :=
  SyncPathGroup.run (SyncHandleRouting.sync directory.path seen.openRead seen.fsync)

theorem groups :
    seen.sync #[directory.path] (admission.cache, afterRead (keeper := keeper), admission.held) =
      .ok () (admission.cache, seen.atSuffix) ∧
    seen.sync #[directory.path] (admission.cache, seen.atSuffix) = .ok () (admission.cache, seen.atStage) := by
  constructor
  · unfold sync
    rw [SyncPathGroup.run_single]
    simp [SyncHandleRouting.sync, Cache.resolve, CensusOpenAdmissionReports.cache, withCache, seen.authorized, atSuffix, afterRead]
  · unfold sync
    rw [SyncPathGroup.run_single]
    simp [SyncHandleRouting.sync, Cache.resolve, CensusOpenAdmissionReports.cache, withCache, seen.suffix, atStage, atSuffix, afterRead]

def projectCreate (path : FilePath) : EStateM IO.Error CensusOpenState (Except IO.Error Handle) :=
  fun before => match seen.tryCreate path (before, seen.scope) with
  | .ok opened (reached, _) => .ok opened reached
  | .error error (reached, _) => .error error reached

noncomputable def stage (path : FilePath) (bytes : ByteArray) : EStateM IO.Error RepairState Unit :=
  stageFreshWithCache path bytes
    (writeFreshStagedWith seen.projectCreate seen.detach seen.create seen.write seen.flush)

theorem createReturns :
    seen.projectCreate (directory.file .stagedWal) seen.atStage = .ok (.error seen.cause) seen.atStage := by
  simp only [projectCreate, atStage, atSuffix, afterRead, seen.failed]

/-- The production staging body reaches this exact raw request. A
non-conflict error bypasses stale-stage cleanup and the data callbacks. -/
theorem stageFails (bytes : ByteArray) :
    seen.stage (directory.file .stagedWal) bytes (admission.cache, seen.atStage) =
      .error seen.cause (admission.cache, seen.atStage) := by
  refine stageFreshWithCache_error _ _ _ _ ?_
  simp only [writeFreshStagedWith, withFreshStaging, Bind.bind, EStateM.bind, seen.createReturns]
  generalize cause : seen.cause = error
  cases error <;> try rfl
  case alreadyExists filename osCode details =>
    have different : osCode ≠ 17 := by
      intro code
      exact seen.notConflict filename details (code ▸ cause)
    simp [different, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- Both cached directory syncs and the first replacement step use the
same reached state. Subsequent scratch sync, rename and installation
cannot run after the observed exclusive-create error. -/
theorem finishes (prepared : Prepared retry.image layout.target layout.plan) :
    finishBoundedMarkedOpen directory layout.boundedPlan layout.plan.keeperBytes.size seen.remove seen.stage
      seen.sync seen.rename (admission.cache, afterRead (keeper := keeper), admission.held) =
        .error seen.cause (admission.cache, seen.atStage) := by
  rw [layout.boundedPlan_eq_extract, finishBoundedMarkedOpen_eq_full _ _ prepared.valid]
  have newer : layout.plan.newer = [] := prepared.names.trans seen.noLater
  have long : layout.plan.keeperSize < layout.plan.keeperBytes.size := by
    have measured : reads.wal.keeper.calls.metadata.byteSize.toNat = layout.plan.keeperBytes.size :=
      reads.wal.keeper.observesFile.extent
    have size : layout.keeper.bytes.size = layout.plan.keeperSize := layout.target.trimmedSize
    exact size ▸ measured ▸ seen.longer
  have unequal : layout.plan.keeperBytes.size ≠ layout.plan.keeperSize := (Nat.ne_of_lt long).symm
  simp [finishMarkedOpen, Plan.alignedWithoutPrune, prepared.valid, newer, unequal, runAt, runRepairPlan,
    steps, long, Publication.steps, List.forM_eq_forM, List.forM_cons, Bind.bind, EStateM.bind,
    Pure.pure, EStateM.pure, seen.groups.1, seen.groups.2, performPaths, Publication.performReplacement, seen.stageFails]

/-- The actual chronological prepare returns the validated plan after
closing the temporary keeper. The reached failure then belongs to that
same bounded worker and no table has been installed. -/
theorem recoveryFails
    (chronology : CapturedMarkedReadCensus reads keeper)
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint)
    (prepared : Prepared retry.image layout.target layout.plan)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history) :
    let prepare := reads.prepareFromCensus chronology.metadataRelease chronology.runs.released
      chronology.sealRelease seen.readKeeper
    finishPreparedWithCensus prepare (fun plan measure =>
      finishBoundedMarkedOpen directory plan measure seen.remove seen.stage seen.sync seen.rename)
      admission.cache (admission.reached, admission.held) = .error seen.cause seen.atStage := by
  dsimp only
  obtain ⟨_, reached, _⟩ := reads.preparesFromCensus chronology.manifest chronology.runs selected
    chronology.marker chronology.beforeListing keeper chronology.seals chronology.offsets chronology.retained
    following prepared.newer accepted ordered seen.readKeeper seen.readsAndCloses
  rw [finishPreparedWithCensus, reached]
  dsimp only
  rw [seen.finishes prepared]

def afterUnlock (unlock : Except IO.Error Unit) : LockedFileState FileImage :=
  match unlock with
  | .ok () => { seen.atStage.2 with owners := seen.atStage.2.owners.set (directory.file .lock) none }
  | .error _ => seen.atStage.2

def diagnostic (unlock : Except IO.Error Unit) : IO.Error :=
  match unlock with
  | .ok () => seen.cause
  | .error cause => cause

noncomputable def run (chronology : CapturedMarkedReadCensus reads keeper)
    (bootstrap : DiskDirectory → CensusDirectoryCache → EStateM IO.Error CensusOpenState Reopened)
    (install : DiskDirectory → DescriptorSlot → CensusDirectoryCache → Reopened →
      EStateM IO.Error CensusOpenState SegmentedSession) :
    EStateM.Result IO.Error CensusOpenState SegmentedSession :=
  admission.run fun path owner cache =>
    admission.recoverWithMarked path
      (finishPreparedWithCensus (reads.prepareFromCensus chronology.metadataRelease chronology.runs.released
        chronology.sealRelease seen.readKeeper) (fun plan measure =>
          finishBoundedMarkedOpen path plan measure seen.remove seen.stage seen.sync seen.rename) cache)
      (bootstrap path cache) >>= install path owner cache

/-- The returned stage error cleans up the original lock at the census
left by the two directory syncs. It retains the earlier selected WAL
and manifest, with neither a scratch allocation nor replacement. -/
theorem returns
    (chronology : CapturedMarkedReadCensus reads keeper)
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint)
    (prepared : Prepared retry.image layout.target layout.plan)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : published.AcceptsVersioned history.length.toUInt64 (CheckpointRepresentsPrefix history)
      retry.image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (flat : optionalMetadataWith (admission.lookup (directory.file .wal)) (admission.reached, admission.held) =
      .ok none (admission.reached, admission.held))
    {marker : IO.FS.Metadata}
    (found : optionalMetadataWith (admission.lookup (directory.file .walBoundary))
      (admission.reached, admission.held) = .ok (some marker) (admission.reached, admission.held))
    (unlock : Except IO.Error Unit)
    (unlocked : admission.unlock admission.owner () seen.atStage = match unlock with
      | .ok () => .ok () (seen.atStage.1, seen.afterUnlock unlock)
      | .error cause => .error cause (seen.atStage.1, seen.afterUnlock unlock))
    (bootstrap : DiskDirectory → CensusDirectoryCache → EStateM IO.Error CensusOpenState Reopened)
    (install : DiskDirectory → DescriptorSlot → CensusDirectoryCache → Reopened →
      EStateM IO.Error CensusOpenState SegmentedSession) :
    seen.run chronology bootstrap install = .error (seen.diagnostic unlock) (seen.atStage.1, seen.afterUnlock unlock) ∧
    (seen.afterUnlock unlock).image = retry.image.syncDirectory ∧
    admission.owner ∈ seen.atStage.1.slots ∧ admission.cached ∈ seen.atStage.1.slots ∧
    (TryLockObserves (seen.afterUnlock unlock).owners directory (.ok true) ↔ unlock = .ok ()) ∧
    SelectedIntegrityCheckpoint published.durable (seen.afterUnlock unlock).image.directory.active.manifest checkpoint := by
  have stopped := seen.recoveryFails chronology selected prepared following accepted ordered
  have returned : seen.run chronology bootstrap install =
      .error (seen.diagnostic unlock) (seen.atStage.1, seen.afterUnlock unlock) := by
    unfold run
    rw [admission.run_reachesRecovery]
    simp only [Bind.bind, EStateM.bind, admission.recoverWithMarked_selects flat found, Option.isSome_some,
      ↓reduceIte, stopped, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, EStateM.Backtrackable.restore,
      EStateM.dummyRestore, unlocked]
    cases unlock with
    | ok result => cases result; rfl
    | error cause => rfl
  have files : (seen.afterUnlock unlock).image = retry.image.syncDirectory := by cases unlock <;> rfl
  refine ⟨returned, files, seen.ownerLive, seen.directoryLive, ?_, ?_⟩
  · cases unlock <;> simp [afterUnlock, atStage, settledFiles, TryLockObserves, LockOwners.set, CensusOpenAdmissionReports.held]
  · rw [files]
    exact selected


end NativeMarkedLongStageCreateError
end Alvoki.Storage.DiskSession
