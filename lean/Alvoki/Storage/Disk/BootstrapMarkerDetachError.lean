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
private abbrev markerBytes := WAL.Boundary.encode 0

private def markerStageImage (before : WalSegmentRotation.State) (detached : Bool) : WalSegmentRotation.State :=
  let settled := before.metadata.syncDirectory
  ⟨{ settled with staged := match detached with
    | false => settled.staged
    | true => fun
      | .walBoundary => none
      | .manifest => settled.staged .manifest }, .durable⟩

private def metadataOnly (stat : FilePath → EStateM IO.Error Files (Except IO.Error (IO.FS.Metadata × DeviceInode)))
    (path : FilePath) : EStateM IO.Error Files (Except IO.Error IO.FS.Metadata) :=
  (stat path).map (Except.map Prod.fst)

/-- The stale binding is inspected without following links. A nonregular
entry and an error other than ENOENT return before unlink. An unlink error
may be reported before or after its locally observed name effect. -/
inductive MarkerStaleDetachFailure
    (stat : FilePath → EStateM IO.Error Files (Except IO.Error (IO.FS.Metadata × DeviceInode)))
    (unlink : FilePath → EStateM IO.Error Files (Except IO.Error Unit))
    (path : FilePath) (stale : DeviceInode) (initial : Files) : IO.Error → Files → Bool → Prop where
  | statError {cause : IO.Error}
      (failed : stat path initial = .ok (.error cause) initial)
      (propagated : ∀ name message, cause ≠ .noFileOrDirectory name 2 message) :
      MarkerStaleDetachFailure stat unlink path stale initial cause initial false
  | notRegular {metadata : IO.FS.Metadata}
      (found : stat path initial = .ok (.ok (metadata, stale)) initial)
      (different : (metadata.type == .file) = false) :
      MarkerStaleDetachFailure stat unlink path stale initial
        (IO.userError s!"expected a regular database staging file: '{path}'") initial false
  | unlinkError {metadata : IO.FS.Metadata} {cause : IO.Error} {reached : Files} {detached : Bool}
      (found : stat path initial = .ok (.ok (metadata, stale)) initial)
      (regular : metadata.type = .file)
      (failed : unlink path initial = .ok (.error cause) reached)
      (propagated : RunCollection.ownedUnlinkResult (.error cause) = .error cause)
      (unchanged : detached = false → reached = initial) :
      MarkerStaleDetachFailure stat unlink path stale initial cause reached detached

namespace MarkerStaleDetachFailure

private theorem returns
    {stat : FilePath → EStateM IO.Error Files (Except IO.Error (IO.FS.Metadata × DeviceInode))}
    {unlink : FilePath → EStateM IO.Error Files (Except IO.Error Unit)}
    {path : FilePath} {stale : DeviceInode} {initial reached : Files} {cause : IO.Error} {detached : Bool}
    (failure : MarkerStaleDetachFailure stat unlink path stale initial cause reached detached) :
    removeStaleStagingWith (metadataOnly stat) unlink path initial = .error cause reached := by
  cases failure with
  | statError failed propagated =>
    simp only [removeStaleStagingWith, metadataOnly, EStateM.map, Bind.bind, EStateM.bind, failed, Except.map]
    cases cause with
    | noFileOrDirectory name code message =>
      by_cases same : code = 2
      · subst code
        exact False.elim (propagated name message rfl)
      · simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw]
    | _ => rfl
  | notRegular found different =>
    simp [removeStaleStagingWith, metadataOnly, EStateM.map, Bind.bind, EStateM.bind, found,
      different, Except.map, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  | @unlinkError metadata _ _ _ found regular failed propagated _ =>
    have kind : (metadata.type == .file) = true := by rw [regular]; rfl
    simp [removeStaleStagingWith, metadataOnly, EStateM.map, Bind.bind, EStateM.bind, found,
      kind, Except.map, Pure.pure, failed, propagated, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

private theorem unchanged
    {stat : FilePath → EStateM IO.Error Files (Except IO.Error (IO.FS.Metadata × DeviceInode))}
    {unlink : FilePath → EStateM IO.Error Files (Except IO.Error Unit)}
    {path : FilePath} {stale : DeviceInode} {initial reached : Files} {cause : IO.Error} {detached : Bool}
    (failure : MarkerStaleDetachFailure stat unlink path stale initial cause reached detached)
    (beforeEffect : detached = false) : reached = initial := by
  cases failure with
  | statError => rfl
  | notRegular => rfl
  | unlinkError _ _ _ _ unchanged => exact unchanged beforeEffect

end MarkerStaleDetachFailure

variable {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {calls : BootstrapOpenCalls (Cache Handle) directory before}
  {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls}
  {listed : BootstrapCheckedListing captured}

/-- The acquired markerless opener reaches an existing staging name after
settling the keeper. A failed cleanup stops before the second exclusive
open. The local namespace report accounts for the scratch binding and
its power-loss choices without requiring it to have only one link. -/
structure BootstrapMarkerDetachError (keeper : BootstrapZeroKeeperRoute listed) where
  between : List LockReferenceDrop
  lockLive : calls.slot ∈ (keeper.settledInventory.afterDrops between).slots
  directoryLive : captured.cached ∈ (keeper.settledInventory.afterDrops between).slots
  stale : RunChildLookup captured.root stageName keeper.keeperView
  canonicalAbsent : keeper.keeperView.child captured.root markerName = none
  tryCreate : FilePath → EStateM IO.Error Files (Except IO.Error Handle)
  statStale : FilePath → EStateM IO.Error Files (Except IO.Error (IO.FS.Metadata × DeviceInode))
  unlinkStale : FilePath → EStateM IO.Error Files (Except IO.Error Unit)
  create : FilePath → EStateM IO.Error Files Handle
  write : Handle → ByteArray → EStateM IO.Error Files Unit
  flush : Handle → EStateM IO.Error Files Unit
  conflict : ∃ name message, tryCreate (directory.file .stagedWalBoundary)
      (markerStageImage before.image false, keeper.settledImage) =
    .ok (.error (.alreadyExists name 17 message)) (markerStageImage before.image false, keeper.settledImage)
  cause : IO.Error
  reached : Files
  detached : Bool
  failed : MarkerStaleDetachFailure statStale unlinkStale (directory.file .stagedWalBoundary) stale.child
    (markerStageImage before.image false, keeper.settledImage) cause reached detached
  logicalImage : reached.1 = markerStageImage before.image detached
  view : DirectoryReadNamespace
  sameObjects : view.modelObject = captured.view.modelObject
  stageNameReached : view.child captured.root stageName = if detached then none else some stale.child
  offTargetNames : ∀ name, name ≠ stageName → view.child captured.root name = keeper.keeperView.child captured.root name
  crashNames : String → List (Option DeviceInode)
  offTargetCrash : ∀ name, name ≠ stageName → crashNames name = [keeper.keeperView.child captured.root name]
  stageCrash : if detached then
      ∀ choice ∈ crashNames stageName, choice = some stale.child ∨ choice = none
    else crashNames stageName = [some stale.child]
  keeperBytes : reached.2.visible keeper.settledImage.active = keeper.settledImage.visible keeper.settledImage.active ∧
    reached.2.crashBytes keeper.settledImage.active = keeper.settledImage.crashBytes keeper.settledImage.active
  survivingScratchBytes : some stale.child ∈ crashNames stageName →
    reached.2.crashBytes (view.modelObject stale.child) =
      keeper.settledImage.crashBytes (keeper.keeperView.modelObject stale.child)
  projection :
    calls.write captured.cache (directory.file .stagedWalBoundary) markerBytes (markerStageImage before.image false) =
      bootstrapMarkerProjection (stageFreshWithCache (directory.file .stagedWalBoundary) markerBytes
        (writeFreshStagedWith tryCreate (removeStaleStagingWith (metadataOnly statStale) unlinkStale) create write flush)
        (captured.cache, markerStageImage before.image false, keeper.settledImage))

namespace BootstrapMarkerDetachError

variable {keeper : BootstrapZeroKeeperRoute listed}

noncomputable abbrev stage (observed : BootstrapMarkerDetachError keeper) :=
  writeFreshStagedWith observed.tryCreate (removeStaleStagingWith (metadataOnly observed.statStale) observed.unlinkStale)
    observed.create observed.write observed.flush

/-- The reported EEXIST enters the actual detach branch. That error skips
reopen, write and flush and leaves the pending cache unchanged. -/
theorem stageError (observed : BootstrapMarkerDetachError keeper) :
    stageFreshWithCache (directory.file .stagedWalBoundary) markerBytes observed.stage
      (captured.cache, markerStageImage before.image false, keeper.settledImage) =
      .error observed.cause (captured.cache, observed.reached) := by
  obtain ⟨name, message, conflict⟩ := observed.conflict
  have returned := observed.failed.returns
  apply stageFreshWithCache_error
  simp only [writeFreshStagedWith, withFreshStaging, Bind.bind, EStateM.bind, conflict]
  change (removeStaleStagingWith (metadataOnly observed.statStale) observed.unlinkStale
      (directory.file .stagedWalBoundary) (markerStageImage before.image false, keeper.settledImage)) = .error _ _ at returned
  simp only [returned]

/-- The keeper directory barrier supplies the same settled inode state
and cache to the reported staged-name failure. -/
theorem physicalPrefix (observed : BootstrapMarkerDetachError keeper) :
    let input := keeper.keeperImage.completeFileSync keeper.keeperImage.active
    (keeper.groupedSync #[directory.path] *>
      stageFreshWithCache (directory.file .stagedWalBoundary) markerBytes observed.stage)
      (captured.cache, keeper.fileSyncedState, input) =
        .error observed.cause (captured.cache, observed.reached) := by
  simpa only [SeqRight.seqRight, EStateM.seqRight, keeper.reachesMarker, markerStageImage,
    BootstrapZeroKeeperRoute.settledImage] using observed.stageError

/-- The local detach report keeps the keeper name, its exact empty bytes
and the absence of the canonical marker. The scratch can have other links. -/
theorem physicalKeeper (observed : BootstrapMarkerDetachError keeper) :
    calls.slot ∈ (keeper.settledInventory.afterDrops observed.between).slots ∧
    captured.cached ∈ (keeper.settledInventory.afterDrops observed.between).slots ∧
    observed.view.modelObject = captured.view.modelObject ∧
    observed.view.child captured.root markerName = none ∧
    observed.view.child captured.root keeperName = some keeper.keeperChild ∧
    observed.crashNames markerName = [none] ∧ observed.crashNames keeperName = [some keeper.keeperChild] ∧
    observed.reached.2.visible keeper.settledImage.active = ByteArray.empty ∧
    observed.reached.2.crashBytes keeper.settledImage.active = [ByteArray.empty] := by
  obtain ⟨_, _, bound, _⟩ := keeper.settledCustody
  exact ⟨observed.lockLive, observed.directoryLive, observed.sameObjects,
    (observed.offTargetNames markerName (by decide)).trans observed.canonicalAbsent,
    (observed.offTargetNames keeperName (by decide)).trans bound,
    (observed.offTargetCrash markerName (by decide)).trans (congrArg (fun name => [name]) observed.canonicalAbsent),
    (observed.offTargetCrash keeperName (by decide)).trans (congrArg (fun name => [name]) bound),
    observed.keeperBytes.1.trans keeper.settledVisible, observed.keeperBytes.2.trans keeper.settledEmpty.2⟩

/-- If detach did not take effect, the visible scratch keeps its exact
old payload. If it did, only the old name or absence can survive a
crash. A reported survivor reads the existing inode's crash bytes. -/
theorem physicalScratch (observed : BootstrapMarkerDetachError keeper) :
    observed.view.child captured.root stageName = (if observed.detached then none else some observed.stale.child) ∧
    (observed.view.child captured.root stageName).map (fun inode => observed.reached.2.visible
      (observed.view.modelObject inode)) =
        (if observed.detached then none else some (keeper.settledImage.visible (keeper.keeperView.modelObject observed.stale.child))) ∧
    (observed.detached = false → observed.crashNames stageName = [some observed.stale.child]) ∧
    ∀ choice ∈ observed.crashNames stageName,
      (choice = some observed.stale.child ∧
        observed.reached.2.crashBytes (observed.view.modelObject observed.stale.child) =
          keeper.settledImage.crashBytes (keeper.keeperView.modelObject observed.stale.child)) ∨
      (observed.detached = true ∧ choice = none) := by
  refine ⟨observed.stageNameReached, ?_, ?_, ?_⟩
  · rw [observed.stageNameReached]
    cases outcome : observed.detached with
    | false =>
      rw [observed.failed.unchanged outcome, observed.sameObjects, keeper.keeperObjects]
      rfl
    | true => rfl
  · intro beforeEffect
    simpa [beforeEffect] using observed.stageCrash
  · intro choice present
    have allowed := observed.stageCrash
    cases effect : observed.detached with
    | false =>
      simp [effect] at allowed
      rw [allowed] at present
      exact .inl ⟨List.mem_singleton.mp present, observed.survivingScratchBytes (allowed ▸ List.mem_singleton_self _)⟩
    | true =>
      simp [effect] at allowed
      rcases allowed choice present with survives | absent
      · exact .inl ⟨survives, observed.survivingScratchBytes (survives ▸ present)⟩
      · exact .inr ⟨rfl, absent⟩

theorem worker (observed : BootstrapMarkerDetachError keeper) (valid : BootstrapValid before.image) :
    calls.bootstrapAt directory captured.cache before.image = .error observed.cause observed.reached.1 ∧
    BootstrapValid observed.reached.1 := by
  have failed := observed.projection.trans (congrArg bootstrapMarkerProjection observed.stageError)
  have active : observed.reached.1.metadata.active = before.image.metadata.active := by rw [observed.logicalImage]; rfl
  have crash : observed.reached.1.metadata.crashImages = [before.image.metadata.active] := by rw [observed.logicalImage]; rfl
  have durable : observed.reached.1.successor = .durable := by rw [observed.logicalImage]; rfl
  have result := bootstrapEmptyWith_writeStagedError directory before.image valid before.image.observeSuccessor rfl
    (calls.createEmpty captured.cache) (calls.write captured.cache) (calls.sync captured.cache) calls.renameFile
    keeper.rotationHealthy failed active crash durable
  exact ⟨(calls.reachesPublication captured.cache listed.entries.1 listed.entries.2).trans result.1, result.2⟩

def final (observed : BootstrapMarkerDetachError keeper) : LockedFileState WalSegmentRotation.State :=
  ⟨observed.reached.1, before.owners.set (directory.file .lock)
    (match calls.unlock with | .success => none | .failure _ _ => some calls.slot.description)⟩

def returnedError (observed : BootstrapMarkerDetachError keeper) : IO.Error :=
  match calls.unlock with | .success => observed.cause | .failure cleanup _ => cleanup

/-- Local unlock gives the exact reached scratch to the next open. -/
theorem returns {input : FilePath} (observed : BootstrapMarkerDetachError keeper)
    (admission : OpenAdmissionReports input directory calls.slot) (valid : BootstrapValid before.image)
    (localUnlock : calls.unlock.LocalFlock) :
    calls.run admission = .error observed.returnedError observed.final ∧ BootstrapValid observed.final.image ∧
    observed.final.image.metadata.active.walBoundary = none ∧
    observed.final.image.metadata.staged .walBoundary =
      (if observed.detached then none else before.image.metadata.staged .walBoundary) := by
  obtain ⟨worker, preserved⟩ := observed.worker valid
  have returned := BootstrapOpenCalls.runWorkerError captured admission localUnlock worker
  refine ⟨?_, preserved, ?_, ?_⟩
  · exact returned.trans (by cases outcome : calls.unlock <;> simp [final, returnedError, outcome])
  · change observed.reached.1.metadata.active.walBoundary = none
    rw [observed.logicalImage]
    exact calls.markerAbsent.1
  · change observed.reached.1.metadata.staged .walBoundary = _
    rw [observed.logicalImage]
    cases observed.detached <;> rfl

/-- A later successful admission and raw marker ENOENT select markerless
recovery from the exact error state. -/
theorem retryMarkerless {input nextInput : FilePath} (observed : BootstrapMarkerDetachError keeper)
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
  exact ⟨(observed.returns admission valid localUnlock).1, retry.acquisition retry.acquired,
    retry.runSelected bootstrap nextAdmission nextCache.captures.1 (marker := none)
      (by simp [optionalMetadataWith, missing, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure])⟩

end BootstrapMarkerDetachError

end Alvoki.Storage.DiskSession
