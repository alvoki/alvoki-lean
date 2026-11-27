import Alvoki.Storage.Disk.Proofs.Bootstrap.BootstrapKeeperMarkerHandoff
import Alvoki.Storage.Disk.Proofs.Bootstrap.ObservedBootstrapRetry

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

private abbrev Handle := DescriptorInventory × DescriptorSlot × Nat
private abbrev Files := WalSegmentRotation.State × WalInodeImage
private abbrev keeperName := renderWalSegmentName 0
private abbrev stageName := "WAL.commit.next"
private abbrev markerName := "WAL.commit"

variable {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {calls : BootstrapOpenCalls (Cache Handle) directory before}
  {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls}
  {listed : BootstrapCheckedListing captured}
  {keeper : BootstrapZeroKeeperRoute listed} {marker : BootstrapMarkerStaging listed}

/-- The failed file barrier targets the exact staged descriptor returned
by write and flush. An effect-time report supplies its outcome.
The file barrier changes only the staged inode's crash-byte choices,
and the worker stops before rename or directory sync. -/
structure BootstrapMarkerSyncError (handoff : BootstrapKeeperMarkerStaging keeper marker) where
  cause : IO.Error
  effective : Bool
  retainedLock : calls.slot ∈ (marker.inventory.afterDrops marker.beforeFile).slots
  retainedDirectory : captured.cached ∈ (marker.inventory.afterDrops marker.beforeFile).slots
  canonicalAbsent : keeper.keeperView.child captured.root markerName = none
  fileReturned : marker.fsync marker.handle (marker.writtenState, marker.inodeState) =
    .error cause (if effective then (marker.syncedState, marker.inodeState.completeFileSync marker.inodeState.active)
      else (marker.writtenState, marker.inodeState))

namespace BootstrapMarkerSyncError

variable {handoff : BootstrapKeeperMarkerStaging keeper marker}

def reached (observed : BootstrapMarkerSyncError handoff) : Files :=
  if observed.effective then (marker.syncedState, marker.inodeState.completeFileSync marker.inodeState.active)
  else (marker.writtenState, marker.inodeState)

def barrierError (observed : BootstrapMarkerSyncError handoff) : IO.Error :=
  IO.userError s!"sync failed for '{directory.file .stagedWalBoundary}': {observed.cause}"

/-- The grouped file barrier consumes the existing pending entry and
returns the exact failed filesystem image. No pathname reopen is needed. -/
theorem fileBarrier (observed : BootstrapMarkerSyncError handoff) :
    let path := directory.file .stagedWalBoundary
    marker.grouped #[path]
      (captured.cache.remember path marker.handle, marker.writtenState, marker.inodeState) =
      .error observed.barrierError (captured.cache.consume path, observed.reached) := by
  simpa only [observed.fileReturned, barrierError, reached] using marker.syncPending

/-- The failed grouped barrier starts from the stage reached by the
same keeper barrier, cache, and staged write. -/
theorem physicalPrefix (observed : BootstrapMarkerSyncError handoff) :
    let input := keeper.keeperImage.completeFileSync keeper.keeperImage.active
    let path := directory.file .stagedWalBoundary
    ((keeper.groupedSync #[directory.path] *> stageFreshWithCache path (WAL.Boundary.encode 0) marker.stage) *>
      marker.grouped #[path]) (captured.cache, keeper.fileSyncedState, input) =
      .error observed.barrierError (captured.cache.consume path, observed.reached) := by
  have staged := handoff.stageAfterKeeper
  simp only [SeqRight.seqRight, EStateM.seqRight] at staged
  simp only [SeqRight.seqRight, EStateM.seqRight, staged, observed.fileBarrier]

private theorem syncProjected (observed : BootstrapMarkerSyncError handoff) :
    calls.sync captured.cache #[directory.file .stagedWalBoundary] marker.writtenState =
      .error observed.barrierError observed.reached.1 :=
  marker.projectFile.trans (congrArg bootstrapMarkerProjection observed.fileBarrier)

/-- Staging and the file barrier leave the canonical marker absent. The
same keeper and staged inodes remain visible in their own names, and the
keeper's already durable empty contents survive either file sync effect. -/
theorem preservesKeeper (observed : BootstrapMarkerSyncError handoff) :
    marker.slot ∈ (marker.inventory.afterDrops marker.beforeFile).slots ∧
    calls.slot ∈ (marker.inventory.afterDrops marker.beforeFile).slots ∧
    captured.cached ∈ (marker.inventory.afterDrops marker.beforeFile).slots ∧
    marker.inodeState.active = marker.inventory.inode marker.slot.description ∧
    marker.stageChild.child ≠ keeper.keeperChild ∧
    marker.stageView.child captured.root markerName = none ∧
    handoff.afterStageNames markerName = [none] ∧
    marker.stageView.child captured.root stageName = some marker.stageChild.child ∧
    marker.stageView.child captured.root keeperName = some keeper.keeperChild ∧
    handoff.afterStageNames keeperName = [some keeper.keeperChild] ∧
    observed.reached.2.visible keeper.settledImage.active = ByteArray.empty ∧
    observed.reached.2.crashBytes keeper.settledImage.active = [ByteArray.empty] ∧
    observed.reached.2.visible marker.inodeState.active = WAL.Boundary.encode 0 ∧
    observed.reached.2.crashBytes marker.inodeState.active =
      if observed.effective then [WAL.Boundary.encode 0] else marker.inodeState.crashBytes marker.inodeState.active := by
  obtain ⟨separate, distinct, keeperBound, _, keeperNames, keeperVisible, keeperBytes⟩ := handoff.stagedKeeper
  have different : markerName ≠ stageName := by decide
  have absent := (handoff.stageNames markerName different).trans observed.canonicalAbsent
  have absentCrash := (handoff.stageChoices markerName different).trans
    ((handoff.keeperSettlement markerName).trans (congrArg (fun child => [child]) observed.canonicalAbsent))
  have staged := marker.stageChild.binds
  rw [marker.stageChild.atRoot, marker.stageChild.atName] at staged
  refine ⟨marker.fileLive, observed.retainedLock, observed.retainedDirectory, marker.stageInode.trans marker.stageObject,
    distinct, absent, absentCrash, staged, keeperBound, keeperNames, ?_⟩
  cases effect : observed.effective <;>
    simp [reached, effect, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, separate,
      keeperVisible, keeperBytes, marker.stageBytes]

private theorem modelReached (observed : BootstrapMarkerSyncError handoff) :
    observed.reached.1.metadata.active.walBoundary = none ∧
    observed.reached.1.metadata.crashImages = [before.image.metadata.active] ∧
    observed.reached.1.successor = .durable ∧
    observed.reached.1.metadata.staged .walBoundary = some (WAL.Boundary.encode 0, observed.effective) := by
  cases effect : observed.effective <;>
    simp only [reached, effect, Bool.false_eq_true, ite_false, ite_true] <;>
    exact ⟨calls.markerAbsent.1, rfl, rfl, rfl⟩

/-- The shared bootstrap worker returns at the failed staged file barrier.
The exact reached model leaves no completed marker and requires no
reports for an unexecuted rename or directory sync. -/
theorem worker (observed : BootstrapMarkerSyncError handoff) (valid : BootstrapValid before.image) :
    calls.bootstrapAt directory captured.cache before.image = .error observed.barrierError observed.reached.1 ∧
    BootstrapValid observed.reached.1 := by
  have effect : observed.reached.1 = marker.writtenState ∨
      bootstrapMarkerStep marker.writtenState .syncStaged = some observed.reached.1 := by
    cases returned : observed.effective
    · exact .inl (by simp [reached, returned])
    · exact .inr (by simp only [reached, returned, ite_true]; rfl)
  have result := bootstrapEmptyWith_syncStagedError directory before.image valid before.image.observeSuccessor rfl
    (calls.createEmpty captured.cache) (calls.write captured.cache) (calls.sync captured.cache) calls.renameFile
    keeper.rotationHealthy rfl marker.writeProjected observed.syncProjected effect
  exact ⟨(calls.reachesPublication captured.cache listed.entries.1 listed.entries.2).trans result.1, result.2⟩

def final (observed : BootstrapMarkerSyncError handoff) : LockedFileState WalSegmentRotation.State :=
  ⟨observed.reached.1, before.owners.set (directory.file .lock)
    (match calls.unlock with | .success => none | .failure _ _ => some calls.slot.description)⟩

def returnedError (observed : BootstrapMarkerSyncError handoff) : IO.Error :=
  match calls.unlock with | .success => observed.barrierError | .failure cleanup _ => cleanup

/-- Local cleanup returns this exact file image for both effect timings.
A lock cleanup error takes precedence and retains the acquired owner. -/
theorem returns {input : FilePath} (observed : BootstrapMarkerSyncError handoff)
    (admission : OpenAdmissionReports input directory calls.slot) (valid : BootstrapValid before.image)
    (localUnlock : calls.unlock.LocalFlock) :
    calls.run admission = .error observed.returnedError observed.final ∧
    BootstrapValid observed.final.image ∧
    observed.final.image.metadata.active.walBoundary = none ∧
    observed.final.image.metadata.crashImages = [before.image.metadata.active] ∧
    observed.final.image.successor = .durable ∧
    observed.final.image.metadata.staged .walBoundary = some (WAL.Boundary.encode 0, observed.effective) := by
  have exactRun := runOpenWithInstallation_acquiredRecoveryError directory calls.slot.description calls.nextRef
    calls.unlock (calls.bootstrapAt directory captured.cache) before (observed.worker valid).1
  refine ⟨?_, (observed.worker valid).2, observed.modelReached⟩
  rw [calls.runMarkerless admission captured.captures.1, exactRun]
  cases outcome : calls.unlock with
  | success => simp [final, returnedError, outcome]
  | failure cleanup released =>
    have retained : released = false := by simpa [outcome, UnlockReport.LocalFlock] using localUnlock
    subst released
    simp [final, returnedError, outcome]

/-- Every admitted power-loss choice from this returned file image
still has the old absent marker and the durable empty keeper. -/
theorem crashSelection (observed : BootstrapMarkerSyncError handoff) (valid : BootstrapValid before.image)
    {pair : DirectoryPublication.Bindings} (selected : pair ∈ observed.final.image.metadata.crashImages)
    {keeperSurvives : Bool} (survival : observed.final.image.successor.MaySurvive keeperSurvives) :
    let crashed := bootstrapPowerLoss directory observed.final pair keeperSurvives
    pair = before.image.metadata.active ∧ keeperSurvives = true ∧ BootstrapValid crashed.image ∧
    crashed.image.metadata.active.walBoundary = none ∧ crashed.image.successor = .durable := by
  intro crashed
  obtain ⟨_, candidates, durable, _⟩ := observed.modelReached
  change pair ∈ observed.reached.1.metadata.crashImages at selected
  change observed.reached.1.successor.MaySurvive keeperSurvives at survival
  have admissible := (observed.worker valid).2.crash selected survival
  rw [candidates] at selected
  rw [durable] at survival
  have pairExact := List.mem_singleton.mp selected
  have keeperExact : keeperSurvives = true := survival
  refine ⟨pairExact, keeperExact, admissible, ?_, ?_⟩
  · change pair.walBoundary = none
    rw [pairExact]
    exact calls.markerAbsent.1
  · simp [crashed, bootstrapPowerLoss, keeperExact]

/-- Any new admitted open on this returned image takes the markerless
branch when its canonical probe reports ENOENT. Its lock grant supplies
vacancy and its own capture supplies the cache for the next worker. -/
theorem retryMarkerless {input nextInput : FilePath} (observed : BootstrapMarkerSyncError handoff)
    (admission : OpenAdmissionReports input directory calls.slot) (valid : BootstrapValid before.image)
    (localUnlock : calls.unlock.LocalFlock)
    {retry : BootstrapAdmissionCalls (Cache Handle) directory observed.final}
    (nextCache : BootstrapCacheOpen retry) (nextAdmission : OpenAdmissionReports nextInput directory retry.slot)
    {name message : String}
    (missing : retry.lookup (directory.file .walBoundary) = .error (.noFileOrDirectory name 2 message))
    (bootstrap : DiskDirectory → Cache Handle → EStateM IO.Error WalSegmentRotation.State Reopened) :
    calls.run admission = .error observed.returnedError observed.final ∧
    observed.final.owners (directory.file .lock) = none ∧
    retry.run bootstrap nextAdmission =
      runOpenWithInstallation directory retry.slot.description retry.nextRef (.ok true) retry.unlock
        (bootstrap directory nextCache.cache) observed.final := by
  obtain ⟨returned, _, _⟩ := observed.returns admission valid localUnlock
  exact ⟨returned, retry.acquisition retry.acquired,
    retry.runSelected bootstrap nextAdmission nextCache.captures.1 (marker := none)
      (by simp [optionalMetadataWith, missing, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure])⟩

end BootstrapMarkerSyncError

end Alvoki.Storage.DiskSession
