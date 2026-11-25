import Alvoki.Storage.Disk.BootstrapKeeperMarkerHandoff
import Alvoki.Storage.Disk.ObservedBootstrapRetry

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
  {keeper : BootstrapZeroKeeperRoute listed} {marker : BootstrapMarkerSynced listed}
  {handoff : BootstrapKeeperMarkerStaging keeper marker.toBootstrapMarkerStaging}

/-- The local atomic rename returns an error before or after its effect.
The namespace report refers to the exact reached names in the captured
root. Before the directory barrier, a visible replacement can survive a
crash or leave the earlier missing binding. These are admitted model
choices. The reported rename leaves both inodes' bytes as they were. -/
structure BootstrapMarkerRenameError (handoff : BootstrapKeeperMarkerStaging keeper marker.toBootstrapMarkerStaging) where
  cause : IO.Error
  effective : Bool
  rename : FilePath → FilePath → EStateM IO.Error Files Unit
  afterFile : List LockReferenceDrop
  lockLive : calls.slot ∈ (marker.toBootstrapMarkerStaging.inventory.afterDrops (marker.beforeFile ++ afterFile)).slots
  directoryLive : captured.cached ∈ (marker.toBootstrapMarkerStaging.inventory.afterDrops (marker.beforeFile ++ afterFile)).slots
  canonicalAbsent : keeper.keeperView.child captured.root markerName = none
  returned : rename (directory.file .stagedWalBoundary) (directory.file .walBoundary)
    (marker.toBootstrapMarkerStaging.syncedState, marker.inodeSynced) =
    .error cause (if effective then marker.renamedState else marker.toBootstrapMarkerStaging.syncedState, marker.inodeSynced)
  projectRename :
    calls.renameFile (directory.file .stagedWalBoundary) (directory.file .walBoundary)
      marker.toBootstrapMarkerStaging.syncedState =
    bootstrapMarkerProjection (withCache (captured.cache.consume (directory.file .stagedWalBoundary))
      (rename (directory.file .stagedWalBoundary) (directory.file .walBoundary)
        (marker.toBootstrapMarkerStaging.syncedState, marker.inodeSynced)))
  reachedView : DirectoryReadNamespace
  sameObjects : reachedView.modelObject = captured.view.modelObject
  names : ∀ name, reachedView.child captured.root name =
    if effective ∧ name = stageName then none
    else if effective ∧ name = markerName then marker.stageView.child captured.root stageName
    else marker.stageView.child captured.root name
  crashNames : String → List (Option DeviceInode)
  retainedNames : ∀ name, name ≠ stageName → name ≠ markerName → crashNames name = handoff.afterStageNames name
  markerChoices : crashNames markerName = if effective then
    marker.stageView.child captured.root stageName :: handoff.afterStageNames markerName
    else handoff.afterStageNames markerName

namespace BootstrapMarkerRenameError

def reached (observed : BootstrapMarkerRenameError handoff) : WalSegmentRotation.State :=
  if observed.effective then marker.renamedState else marker.toBootstrapMarkerStaging.syncedState

/-- The single pending group must complete before the issued rename.
The rename receives that exact synced inode and keeps the reached cache. -/
theorem physicalPrefix (observed : BootstrapMarkerRenameError handoff) :
    let input := keeper.keeperImage.completeFileSync keeper.keeperImage.active
    let staged := directory.file .stagedWalBoundary
    let rename := fun (state : Cache Handle × Files) =>
      withCache state.1 (observed.rename staged (directory.file .walBoundary) state.2)
    let write := stageFreshWithCache staged (WAL.Boundary.encode 0) marker.toBootstrapMarkerStaging.stage
    (((keeper.groupedSync #[directory.path] *> write) *> marker.grouped #[staged]) *> rename)
      (captured.cache, keeper.fileSyncedState, input) =
      .error observed.cause (captured.cache.consume staged, observed.reached, marker.inodeSynced) := by
  intro input staged rename write
  have wrote := handoff.stageAfterKeeper
  simp only [SeqRight.seqRight, EStateM.seqRight] at wrote
  simp only [SeqRight.seqRight, EStateM.seqRight, input, staged, write, wrote, marker.fileCallback, rename, withCache,
    observed.returned, reached]

private theorem renameProjected (observed : BootstrapMarkerRenameError handoff) :
    calls.renameFile (directory.file .stagedWalBoundary) (directory.file .walBoundary)
      marker.toBootstrapMarkerStaging.syncedState = .error observed.cause observed.reached := by
  rw [observed.projectRename, observed.returned]
  rfl

/-- The physical keeper stays at its old binding with empty durable
contents. The synced marker's visible name and admitted crash choices
depend on whether this exact atomic rename took effect. -/
theorem physicalChoices (observed : BootstrapMarkerRenameError handoff) :
    calls.slot ∈ (marker.toBootstrapMarkerStaging.inventory.afterDrops (marker.beforeFile ++ observed.afterFile)).slots ∧
    captured.cached ∈ (marker.toBootstrapMarkerStaging.inventory.afterDrops (marker.beforeFile ++ observed.afterFile)).slots ∧
    marker.inodeState.active = marker.toBootstrapMarkerStaging.inventory.inode marker.slot.description ∧
    marker.stageChild.child ≠ keeper.keeperChild ∧
    observed.reachedView.modelObject marker.stageChild.child = marker.inodeState.active ∧
    observed.reachedView.child captured.root stageName = (if observed.effective then none else some marker.stageChild.child) ∧
    observed.reachedView.child captured.root markerName = (if observed.effective then some marker.stageChild.child else none) ∧
    observed.crashNames markerName = (if observed.effective then [some marker.stageChild.child, none] else [none]) ∧
    observed.reachedView.child captured.root keeperName = some keeper.keeperChild ∧
    observed.crashNames keeperName = [some keeper.keeperChild] ∧
    marker.inodeSynced.crashBytes marker.inodeState.active = [WAL.Boundary.encode 0] ∧
    marker.inodeSynced.crashBytes keeper.settledImage.active = [ByteArray.empty] := by
  obtain ⟨separate, distinct, kept, _, keeperNames, _, empty⟩ := handoff.stagedKeeper
  have keeperNotStage : keeperName ≠ stageName := by decide
  have keeperNotMarker : keeperName ≠ markerName := by decide
  have markerNotStage : markerName ≠ stageName := by decide
  have staged := marker.stageChild.binds
  rw [marker.stageChild.atRoot, marker.stageChild.atName] at staged
  have absent := (handoff.stageNames markerName markerNotStage).trans observed.canonicalAbsent
  have absentAtCrash := (handoff.stageChoices markerName markerNotStage).trans
    ((handoff.keeperSettlement markerName).trans (congrArg (fun child => [child]) observed.canonicalAbsent))
  refine ⟨observed.lockLive, observed.directoryLive, marker.stageInode.trans marker.stageObject, distinct, ?_,
    ?_, ?_, ?_, ?_, (observed.retainedNames keeperName keeperNotStage keeperNotMarker).trans keeperNames, ?_, ?_⟩
  · rw [observed.sameObjects, ← handoff.stageObjects, marker.stageInode]
  · simp [observed.names, staged]
  · simp [observed.names, markerNotStage, staged, absent]
  · simp [observed.markerChoices, staged, absentAtCrash]
  · simp [observed.names, keeperNotStage, keeperNotMarker, kept]
  · simp [BootstrapMarkerSynced.inodeSynced, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, marker.stageBytes]
  · simp [BootstrapMarkerSynced.inodeSynced, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, separate, empty]

private theorem modelReached (observed : BootstrapMarkerRenameError handoff) :
    observed.reached.metadata.active.walBoundary = (if observed.effective then some (WAL.Boundary.encode 0) else none) ∧
    observed.reached.metadata.crashImages.map DirectoryPublication.Bindings.walBoundary =
      (if observed.effective then [some (WAL.Boundary.encode 0), none] else [none]) ∧
    observed.reached.successor = .durable ∧
    observed.reached.metadata.staged .walBoundary =
      (if observed.effective then none else some (WAL.Boundary.encode 0, true)) := by
  cases effect : observed.effective
  · simp only [reached, effect, Bool.false_eq_true, ite_false]
    exact ⟨calls.markerAbsent.1, congrArg (fun value => [value]) calls.markerAbsent.1, rfl, rfl⟩
  · simp only [reached, effect, ite_true]
    exact ⟨rfl, congrArg (fun tail => some (WAL.Boundary.encode 0) :: [tail]) calls.markerAbsent.1, rfl, rfl⟩

/-- Reading the admitted raw crash names through the synced inodes
recovers exactly the model's marker choices. -/
theorem crashProjection (observed : BootstrapMarkerRenameError handoff) :
    (observed.crashNames markerName).flatMap (fun child => match child with
      | none => [none]
      | some inode => (marker.inodeSynced.crashBytes (observed.reachedView.modelObject inode)).map some) =
    observed.reached.metadata.crashImages.map DirectoryPublication.Bindings.walBoundary := by
  obtain ⟨_, _, _, _, identity, _, _, names, _, _, bytes, _⟩ := observed.physicalChoices
  rw [observed.modelReached.2.1, names]
  cases effect : observed.effective <;> simp [identity, bytes]

theorem worker (observed : BootstrapMarkerRenameError handoff) (valid : BootstrapValid before.image) :
    calls.bootstrapAt directory captured.cache before.image = .error observed.cause observed.reached ∧
    BootstrapValid observed.reached := by
  have effect : observed.reached = marker.toBootstrapMarkerStaging.syncedState ∨
      bootstrapMarkerStep marker.toBootstrapMarkerStaging.syncedState .renameStaged = some observed.reached := by
    cases returned : observed.effective
    · exact .inl (by simp [reached, returned])
    · exact .inr (by simp only [reached, returned, ite_true]; rfl)
  have outcome := bootstrapEmptyWith_renameError directory before.image valid before.image.observeSuccessor rfl
    (calls.createEmpty captured.cache) (calls.write captured.cache) (calls.sync captured.cache) calls.renameFile
    keeper.rotationHealthy rfl marker.toBootstrapMarkerStaging.writeProjected rfl marker.fileProjected
    observed.renameProjected effect
  exact ⟨(calls.reachesPublication captured.cache listed.entries.1 listed.entries.2).trans outcome.1, outcome.2⟩

def final (observed : BootstrapMarkerRenameError handoff) : LockedFileState WalSegmentRotation.State :=
  ⟨observed.reached, before.owners.set (directory.file .lock)
    (match calls.unlock with | .success => none | .failure _ _ => some calls.slot.description)⟩

def returnedError (observed : BootstrapMarkerRenameError handoff) : IO.Error :=
  match calls.unlock with | .success => observed.cause | .failure cleanup _ => cleanup

/-- The reported local unlock returns the exact reached image. Once the
rename takes effect a live retry can observe the new marker, even before
the directory barrier rules out the older crash choice. -/
theorem returns {input : FilePath} (observed : BootstrapMarkerRenameError handoff)
    (admission : OpenAdmissionReports input directory calls.slot) (valid : BootstrapValid before.image)
    (localUnlock : calls.unlock.LocalFlock) :
    calls.run admission = .error observed.returnedError observed.final ∧ BootstrapValid observed.final.image ∧
    observed.final.image.metadata.active.walBoundary =
      (if observed.effective then some (WAL.Boundary.encode 0) else none) ∧
    observed.final.image.metadata.crashImages.map DirectoryPublication.Bindings.walBoundary =
      (if observed.effective then [some (WAL.Boundary.encode 0), none] else [none]) ∧
    observed.final.image.successor = .durable ∧ observed.final.image.metadata.staged .walBoundary =
      (if observed.effective then none else some (WAL.Boundary.encode 0, true)) := by
  have recovered := (observed.worker valid).1
  have exactRun := runOpenWithInstallation_acquiredRecoveryError directory calls.slot.description calls.nextRef
    calls.unlock (calls.bootstrapAt directory captured.cache) before recovered
  refine ⟨?_, (observed.worker valid).2, observed.modelReached⟩
  rw [calls.runMarkerless admission captured.captures.1, exactRun]
  cases outcome : calls.unlock with
  | success => simp [final, returnedError, outcome]
  | failure cleanup released =>
    have retained : released = false := by simpa [outcome, UnlockReport.LocalFlock] using localUnlock
    subst released
    simp [final, returnedError, outcome]

/-- Every reported power-loss choice uses the same durable keeper.
Only an effective rename admits a surviving canonical zero marker. -/
theorem crashSelection (observed : BootstrapMarkerRenameError handoff) (valid : BootstrapValid before.image)
    {pair : DirectoryPublication.Bindings} (selected : pair ∈ observed.final.image.metadata.crashImages)
    {keeperSurvives : Bool} (survival : observed.final.image.successor.MaySurvive keeperSurvives) :
    let crashed := bootstrapPowerLoss directory observed.final pair keeperSurvives
    BootstrapValid crashed.image ∧ crashed.image.successor = .durable ∧
    (crashed.image.metadata.active.walBoundary = none ∨
      (observed.effective = true ∧ crashed.image.metadata.active.walBoundary = some (WAL.Boundary.encode 0))) := by
  intro crashed
  change pair ∈ observed.reached.metadata.crashImages at selected
  change observed.reached.successor.MaySurvive keeperSurvives at survival
  have admissible := (observed.worker valid).2.crash selected survival
  rw [observed.modelReached.2.2.1] at survival
  have keeperExact : keeperSurvives = true := survival
  refine ⟨admissible, by simp [crashed, bootstrapPowerLoss, keeperExact], ?_⟩
  change pair.walBoundary = none ∨ (observed.effective = true ∧ pair.walBoundary = some (WAL.Boundary.encode 0))
  have choice : pair.walBoundary ∈ observed.reached.metadata.crashImages.map DirectoryPublication.Bindings.walBoundary :=
    List.mem_map_of_mem selected
  rw [observed.modelReached.2.1] at choice
  cases effect : observed.effective
  · simp only [effect, Bool.false_eq_true, ite_false] at choice
    exact .inl (List.mem_singleton.mp choice)
  · simp only [effect, ite_true] at choice
    rcases List.mem_cons.mp choice with zero | absent
    · exact .inr ⟨rfl, zero⟩
    · exact .inl (List.mem_singleton.mp absent)

/-- A live admitted retry uses this reached image and selects from its
canonical marker probe under the next lock and captured cache. -/
theorem retrySelects {input nextInput : FilePath} (observed : BootstrapMarkerRenameError handoff)
    (admission : OpenAdmissionReports input directory calls.slot) (valid : BootstrapValid before.image)
    (localUnlock : calls.unlock.LocalFlock)
    {retry : BootstrapAdmissionCalls (Cache Handle) directory observed.final}
    (nextCache : BootstrapCacheOpen retry) (nextAdmission : OpenAdmissionReports nextInput directory retry.slot)
    (probe : BootstrapRetryMarker retry)
    (bootstrap : DiskDirectory → Cache Handle → EStateM IO.Error WalSegmentRotation.State Reopened) :
    calls.run admission = .error observed.returnedError observed.final ∧
    nextCache.RetrySelection nextAdmission bootstrap := by
  obtain ⟨returned, reachedValid, _⟩ := observed.returns admission valid localUnlock
  exact ⟨returned, nextCache.retrySelects nextAdmission reachedValid probe bootstrap⟩

end BootstrapMarkerRenameError

end Alvoki.Storage.DiskSession
