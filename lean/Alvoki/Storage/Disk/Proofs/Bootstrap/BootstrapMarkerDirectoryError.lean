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
  {keeper : BootstrapZeroKeeperRoute listed} {marker : BootstrapMarkerRenamed listed}
  {handoff : BootstrapKeeperMarkerRename keeper marker}

/-- The final directory fsync takes the same captured directory slot.
The returned error either retains the rename's existing crash choices
or settles its visible bindings. The observed file sync has already
made the marker inode's bytes durable. -/
structure BootstrapMarkerDirectoryError (handoff : BootstrapKeeperMarkerRename keeper marker) where
  cause : IO.Error
  effective : Bool
  canonicalAbsent : keeper.keeperView.child captured.root markerName = none
  renameMarkerChoices : handoff.afterRenameNames markerName =
    marker.renamedView.child captured.root markerName :: handoff.afterStageNames markerName
  returned : marker.fsync (captured.reached, captured.cached, 0)
    (marker.toBootstrapMarkerSynced.renamedState, marker.toBootstrapMarkerSynced.inodeSynced) =
    .error cause (if effective then (marker.publishedState, marker.toBootstrapMarkerSynced.inodeSynced.settleBinding)
      else (marker.toBootstrapMarkerSynced.renamedState, marker.toBootstrapMarkerSynced.inodeSynced))
  crashNames : String → List (Option DeviceInode)
  choices : ∀ name, crashNames name = if effective then [marker.renamedView.child captured.root name]
    else handoff.afterRenameNames name

namespace BootstrapMarkerDirectoryError

def reached (observed : BootstrapMarkerDirectoryError handoff) : Files :=
  if observed.effective then (marker.publishedState, marker.toBootstrapMarkerSynced.inodeSynced.settleBinding)
  else (marker.toBootstrapMarkerSynced.renamedState, marker.toBootstrapMarkerSynced.inodeSynced)

def barrierError (observed : BootstrapMarkerDirectoryError handoff) : IO.Error :=
  IO.userError s!"sync failed for '{directory.path}': {observed.cause}"

/-- The final singleton group calls fsync on the captured retained
directory, returning the same spent pending cache and exact file image. -/
theorem barrier (observed : BootstrapMarkerDirectoryError handoff) :
    let cache := captured.cache.consume (directory.file .stagedWalBoundary)
    marker.grouped #[directory.path] (cache, marker.toBootstrapMarkerSynced.renamedState,
      marker.toBootstrapMarkerSynced.inodeSynced) =
      .error observed.barrierError (cache, observed.reached) := by
  simpa only [observed.returned, barrierError, reached] using marker.directoryCallback

/-- The state reaching the failed barrier comes from the actual completed
rename. The same captured cache and inode state pass through the suffix. -/
theorem physicalPrefix (observed : BootstrapMarkerDirectoryError handoff) :
    let input := keeper.keeperImage.completeFileSync keeper.keeperImage.active
    let path := directory.file .stagedWalBoundary
    let write := stageFreshWithCache path (WAL.Boundary.encode 0) marker.toBootstrapMarkerStaging.stage
    let rename := fun (state : Cache Handle × Files) =>
      withCache state.1 (marker.rename path (directory.file .walBoundary) state.2)
    ((((keeper.groupedSync #[directory.path] *> write) *> marker.grouped #[path]) *> rename) *>
      marker.grouped #[directory.path]) (captured.cache, keeper.fileSyncedState, input) =
      .error observed.barrierError (captured.cache.consume path, observed.reached) := by
  have renamed := handoff.renameAfterKeeper
  simp only [SeqRight.seqRight, EStateM.seqRight] at renamed
  simp only [SeqRight.seqRight, EStateM.seqRight, renamed, observed.barrier]

private theorem barrierProjected (observed : BootstrapMarkerDirectoryError handoff) :
    calls.sync captured.cache #[directory.path] marker.toBootstrapMarkerSynced.renamedState =
      .error observed.barrierError observed.reached.1 :=
  marker.projectDirectory.trans (congrArg bootstrapMarkerProjection observed.barrier)

/-- The same directory descriptor governs the keeper and marker names.
The marker is visible under its real renamed inode at both error
timings. A before-effect report retains the previous missing choice. -/
theorem physicalChoices (observed : BootstrapMarkerDirectoryError handoff) :
    let inventory := (marker.toBootstrapMarkerStaging.inventory.afterDrops (marker.beforeFile ++ marker.afterFile))
    let inode := keeper.settledImage.active
    marker.renamedView.modelObject captured.root = captured.reached.inode captured.cached.description ∧
    calls.slot ∈ inventory.slots ∧ captured.cached ∈ inventory.slots ∧
    marker.renamedView.child captured.root stageName = none ∧
    marker.renamedView.child captured.root markerName = some marker.stageChild.child ∧
    marker.renamedView.modelObject marker.stageChild.child = marker.inodeState.active ∧
    marker.stageChild.child ≠ keeper.keeperChild ∧
    marker.renamedView.child captured.root keeperName = some keeper.keeperChild ∧
    observed.crashNames keeperName = [some keeper.keeperChild] ∧
    observed.crashNames markerName =
      (if observed.effective then [some marker.stageChild.child] else [some marker.stageChild.child, none]) ∧
    observed.reached.2.crashBytes inode = [ByteArray.empty] ∧
    observed.reached.2.crashBytes marker.inodeState.active = [WAL.Boundary.encode 0] := by
  intro inventory inode
  obtain ⟨distinct, keeperBound, _, keeperChoices, _, keeperBytes⟩ := handoff.renamedKeeper
  have markerNotStage : markerName ≠ stageName := by decide
  have markerBound := marker.liveChild.binds
  rw [marker.liveChild.atRoot, marker.liveChild.atName, marker.sameChild] at markerBound
  have absentAtCrash := (handoff.stageChoices markerName markerNotStage).trans
    ((handoff.keeperSettlement markerName).trans (congrArg (fun child => [child]) observed.canonicalAbsent))
  have markerBytes : marker.toBootstrapMarkerSynced.inodeSynced.crashBytes marker.inodeState.active =
      [WAL.Boundary.encode 0] := by
    simp [BootstrapMarkerSynced.inodeSynced, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, marker.stageBytes]
  refine ⟨?_, marker.lockLive, marker.directoryLive, marker.stageGone, markerBound, ?_, distinct, keeperBound,
    ?_, ?_, ?_, ?_⟩
  · rw [handoff.renameObjects]
    exact captured.captures.2.2.2.2
  · rw [handoff.renameObjects, ← handoff.stageObjects, marker.stageInode]
  · simp [observed.choices, keeperBound, keeperChoices]
  · simp [observed.choices, observed.renameMarkerChoices, markerBound, absentAtCrash]
  · cases effect : observed.effective <;> simpa [reached, effect, WalInodeImage.settleBinding, inode] using keeperBytes
  · cases effect : observed.effective <;> simpa [reached, effect, WalInodeImage.settleBinding] using markerBytes

private theorem modelReached (observed : BootstrapMarkerDirectoryError handoff) :
    observed.reached.1.metadata.active.walBoundary = some (WAL.Boundary.encode 0) ∧
    observed.reached.1.metadata.crashImages.map DirectoryPublication.Bindings.walBoundary =
      (if observed.effective then [some (WAL.Boundary.encode 0)] else [some (WAL.Boundary.encode 0), none]) ∧
    observed.reached.1.successor = .durable ∧ observed.reached.1.metadata.staged .walBoundary = none := by
  cases effect : observed.effective
  · simp only [reached, effect, Bool.false_eq_true, ite_false]
    exact ⟨rfl, congrArg (fun tail => some (WAL.Boundary.encode 0) :: [tail]) calls.markerAbsent.1, rfl, rfl⟩
  · simp only [reached, effect, ite_true]
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- The same raw inode choices and synced bytes project to the exact
marker choices carried by the admitted returned file image. -/
theorem crashProjection (observed : BootstrapMarkerDirectoryError handoff) :
    (observed.crashNames markerName).flatMap (fun child => match child with
      | none => [none]
      | some inode => (observed.reached.2.crashBytes (marker.renamedView.modelObject inode)).map some) =
    observed.reached.1.metadata.crashImages.map DirectoryPublication.Bindings.walBoundary := by
  obtain ⟨_, _, _, _, _, identity, _, _, _, names, _, bytes⟩ := observed.physicalChoices
  rw [observed.modelReached.2.1, names]
  cases effect : observed.effective <;> simp [identity, bytes]

theorem worker (observed : BootstrapMarkerDirectoryError handoff) (valid : BootstrapValid before.image) :
    calls.bootstrapAt directory captured.cache before.image = .error observed.barrierError observed.reached.1 ∧
    BootstrapValid observed.reached.1 := by
  have effect : observed.reached.1 = marker.toBootstrapMarkerSynced.renamedState ∨
      bootstrapMarkerStep marker.toBootstrapMarkerSynced.renamedState .syncDirectory = some observed.reached.1 := by
    cases returned : observed.effective
    · exact .inl (by simp [reached, returned])
    · exact .inr (by simp only [reached, returned, ite_true]; rfl)
  have outcome := bootstrapEmptyWith_directoryError directory before.image valid before.image.observeSuccessor rfl
    (calls.createEmpty captured.cache) (calls.write captured.cache) (calls.sync captured.cache) calls.renameFile
    keeper.rotationHealthy rfl marker.toBootstrapMarkerStaging.writeProjected rfl
    marker.toBootstrapMarkerSynced.fileProjected rfl marker.renameProjected observed.barrierProjected effect
  exact ⟨(calls.reachesPublication captured.cache listed.entries.1 listed.entries.2).trans outcome.1, outcome.2⟩

def final (observed : BootstrapMarkerDirectoryError handoff) : LockedFileState WalSegmentRotation.State :=
  ⟨observed.reached.1, before.owners.set (directory.file .lock)
    (match calls.unlock with | .success => none | .failure _ _ => some calls.slot.description)⟩

def returnedError (observed : BootstrapMarkerDirectoryError handoff) : IO.Error :=
  match calls.unlock with | .success => observed.barrierError | .failure cleanup _ => cleanup

/-- Admission returns the exact failed barrier image. The local unlock
can replace the error and retain ownership, while the files stay intact. -/
theorem returns {input : FilePath} (observed : BootstrapMarkerDirectoryError handoff)
    (admission : OpenAdmissionReports input directory calls.slot) (valid : BootstrapValid before.image)
    (localUnlock : calls.unlock.LocalFlock) :
    calls.run admission = .error observed.returnedError observed.final ∧ BootstrapValid observed.final.image ∧
    observed.final.image.metadata.active.walBoundary = some (WAL.Boundary.encode 0) ∧
    observed.final.image.metadata.crashImages.map DirectoryPublication.Bindings.walBoundary =
      (if observed.effective then [some (WAL.Boundary.encode 0)] else [some (WAL.Boundary.encode 0), none]) ∧
    observed.final.image.successor = .durable ∧ observed.final.image.metadata.staged .walBoundary = none := by
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

/-- A reported crash can remove the live marker only before the directory
effect. The settled empty keeper always survives. -/
theorem crashSelection (observed : BootstrapMarkerDirectoryError handoff) (valid : BootstrapValid before.image)
    {pair : DirectoryPublication.Bindings} (selected : pair ∈ observed.final.image.metadata.crashImages)
    {keeperSurvives : Bool} (survival : observed.final.image.successor.MaySurvive keeperSurvives) :
    let crashed := bootstrapPowerLoss directory observed.final pair keeperSurvives
    BootstrapValid crashed.image ∧ crashed.image.successor = .durable ∧
    (crashed.image.metadata.active.walBoundary = some (WAL.Boundary.encode 0) ∨
      (observed.effective = false ∧ crashed.image.metadata.active.walBoundary = none)) := by
  intro crashed
  change pair ∈ observed.reached.1.metadata.crashImages at selected
  change observed.reached.1.successor.MaySurvive keeperSurvives at survival
  have admissible := (observed.worker valid).2.crash selected survival
  rw [observed.modelReached.2.2.1] at survival
  have keeperExact : keeperSurvives = true := survival
  refine ⟨admissible, by simp [crashed, bootstrapPowerLoss, keeperExact], ?_⟩
  change pair.walBoundary = some (WAL.Boundary.encode 0) ∨ (observed.effective = false ∧ pair.walBoundary = none)
  have choice : pair.walBoundary ∈ observed.reached.1.metadata.crashImages.map DirectoryPublication.Bindings.walBoundary :=
    List.mem_map_of_mem selected
  rw [observed.modelReached.2.1] at choice
  cases effect : observed.effective
  · simp only [effect, Bool.false_eq_true, ite_false] at choice
    rcases List.mem_cons.mp choice with zero | absent
    · exact .inl zero
    · exact .inr ⟨rfl, List.mem_singleton.mp absent⟩
  · simp only [effect, ite_true] at choice
    exact .inl (List.mem_singleton.mp choice)

/-- Until a crash, the next admitted lookup sees the published marker
and enters marked recovery on its own captured directory and lock. -/
theorem retryMarked {input nextInput : FilePath} (observed : BootstrapMarkerDirectoryError handoff)
    (admission : OpenAdmissionReports input directory calls.slot) (valid : BootstrapValid before.image)
    (localUnlock : calls.unlock.LocalFlock)
    {retry : BootstrapAdmissionCalls (Cache Handle) directory observed.final}
    (nextCache : BootstrapCacheOpen retry) (nextAdmission : OpenAdmissionReports nextInput directory retry.slot)
    {metadata : IO.FS.Metadata} (probe : retry.lookup (directory.file .walBoundary) = .ok metadata)
    (bootstrap : DiskDirectory → Cache Handle → EStateM IO.Error WalSegmentRotation.State Reopened) :
    calls.run admission = .error observed.returnedError observed.final ∧
    observed.final.owners (directory.file .lock) = none ∧
    retry.run bootstrap nextAdmission =
      runOpenWithInstallation directory retry.slot.description retry.nextRef (.ok true) retry.unlock
        (retry.marked directory nextCache.cache) observed.final := by
  obtain ⟨returned, _, _⟩ := observed.returns admission valid localUnlock
  exact ⟨returned, retry.acquisition retry.acquired,
    retry.runSelected bootstrap nextAdmission nextCache.captures.1 (marker := some metadata)
      (by simp [optionalMetadataWith, probe, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure])⟩

end BootstrapMarkerDirectoryError

end Alvoki.Storage.DiskSession
