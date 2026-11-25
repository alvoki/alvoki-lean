import Alvoki.Storage.Disk.BootstrapKeeperMarkerHandoff
import Alvoki.Storage.Disk.ObservedBootstrapRetry

namespace Alvoki.Storage.SyncHandleRouting

open System

/-- A first exclusive-open result other than EEXIST goes directly to
the worker's error return. There is no staged handle to write or drop. -/
theorem writeFreshStagedWith_openError {handle state : Type}
    {tryCreate : FilePath → EStateM IO.Error state (Except IO.Error handle)}
    (detach : FilePath → EStateM IO.Error state Unit) (create : FilePath → EStateM IO.Error state handle)
    (write : handle → ByteArray → EStateM IO.Error state Unit) (flush : handle → EStateM IO.Error state Unit)
    {path : FilePath} (bytes : ByteArray) {before reached : state} {cause : IO.Error}
    (failed : tryCreate path before = .ok (.error cause) reached)
    (direct : ∀ name message, cause ≠ .alreadyExists name 17 message) :
    writeFreshStagedWith tryCreate detach create write flush path bytes before = .error cause reached := by
  simp only [writeFreshStagedWith, withFreshStaging, Bind.bind, EStateM.bind, failed]
  rfl

end Alvoki.Storage.SyncHandleRouting

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

private abbrev Handle := DescriptorInventory × DescriptorSlot × Nat
private abbrev Files := WalSegmentRotation.State × WalInodeImage
private abbrev Native := DescriptorInventory × Files
private abbrev keeperName := renderWalSegmentName 0
private abbrev stageName := "WAL.commit.next"
private abbrev markerName := "WAL.commit"
private abbrev markerBytes := WAL.Boundary.encode 0

variable {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {calls : BootstrapOpenCalls (Cache Handle) directory before}
  {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls}
  {listed : BootstrapCheckedListing captured}

private abbrev atStage (before : WalSegmentRotation.State) : WalSegmentRotation.State :=
  ⟨before.metadata.syncDirectory, .durable⟩

private def emptyScratch (before : WalSegmentRotation.State) : WalSegmentRotation.State :=
  { metadata := { before.metadata.syncDirectory with
      staged := fun
        | .walBoundary => some (ByteArray.empty, false)
        | .manifest => before.metadata.staged .manifest }
    successor := .durable }

/-- Project the raw descriptor observation out of the first open result.
The native `toBaseIO` reports its I/O error as a returned value. -/
private def projectExclusive (native : FilePath → EStateM IO.Error Native (Except IO.Error Handle))
    (initial : DescriptorInventory) : FilePath → EStateM IO.Error Files (Except IO.Error Handle) :=
  fun path image => match native path (initial, image) with
    | .ok result (_, reached) => .ok result reached
    | .error cause (_, reached) => .error cause reached

/-- The exclusive raw create succeeded before `fdopen` failed. The
observations record the raw descriptor and the exact reached empty
scratch, using the pinned Linux primitive's reported effects. -/
structure BootstrapEmptyMarkerStage (keeper : BootstrapZeroKeeperRoute listed) (initial : DescriptorInventory) where
  raw : DescriptorSlot
  free : ∀ previous ∈ initial.slots, previous.address ≠ raw.address
  fresh : initial.references raw.description = []
  closeOnExec : raw.reference.closeOnExec = true
  view : DirectoryReadNamespace
  sameObjects : view.modelObject = captured.view.modelObject
  child : RunChildLookup captured.root stageName view
  metadata : IO.FS.Metadata
  lookup : FilePath → Except IO.Error (IO.FS.Metadata × DeviceInode)
  stat : lookup (directory.file .stagedWalBoundary) = .ok (metadata, child.child)
  regular : metadata.type = .file
  singleLink : metadata.numLinks = 1
  size : metadata.byteSize = 0
  object : view.modelObject child.child = initial.inode raw.description
  inodes : WalInodeImage
  empty : inodes.visible (initial.inode raw.description) = ByteArray.empty
  separate : captured.view.modelObject keeper.keeperChild ≠ initial.inode raw.description
  names : ∀ name, name ≠ stageName → view.child captured.root name = keeper.keeperView.child captured.root name
  crashNames : String → List (Option DeviceInode)
  offTargetCrash : ∀ name, name ≠ stageName → crashNames name = [keeper.keeperView.child captured.root name]
  offTargetBytes : ∀ inode, inode ≠ initial.inode raw.description →
    inodes.visible inode = keeper.settledImage.visible inode ∧
    inodes.crashBytes inode = keeper.settledImage.crashBytes inode

/-- Report either an exclusive raw failure without effects, or a created
empty stage with a raw slot which could not be wrapped. -/
inductive BootstrapMarkerExclusiveEffect (keeper : BootstrapZeroKeeperRoute listed) (initial : DescriptorInventory) :
    Native → DirectoryReadNamespace → (String → List (Option DeviceInode)) → Prop where
  | rawFailed : BootstrapMarkerExclusiveEffect keeper initial
      (initial, atStage before.image, keeper.settledImage) keeper.keeperView
      (fun name => [keeper.keeperView.child captured.root name])
  | wrapFailed (created : BootstrapEmptyMarkerStage keeper initial) :
      BootstrapMarkerExclusiveEffect keeper initial
        (initial.insert created.raw created.free, emptyScratch before.image, created.inodes) created.view created.crashNames

namespace BootstrapMarkerExclusiveEffect

variable {keeper : BootstrapZeroKeeperRoute listed} {initial : DescriptorInventory}
  {reached : Native} {view : DirectoryReadNamespace} {crashNames : String → List (Option DeviceInode)}

/-- Neither outcome adds a reference to an earlier description. -/
theorem keepsReferences (effect : BootstrapMarkerExclusiveEffect keeper initial reached view crashNames)
    {description : Nat} (live : initial.references description ≠ []) :
    reached.1.references description = initial.references description := by
  cases effect with
  | rawFailed => rfl
  | wrapFailed created =>
    have distinct : created.raw.description ≠ description := by
      intro same
      exact live (same ▸ created.fresh)
    exact (DescriptorInventory.references_insert initial created.raw created.free description).trans (ite_eq_right distinct)

/-- The canonical keeper and its empty bytes survive either native open
effect. The reported namespace changes only the scratch name. -/
theorem keepsKeeper (effect : BootstrapMarkerExclusiveEffect keeper initial reached view crashNames)
    (oldAbsent : keeper.keeperView.child captured.root markerName = none) :
    view.modelObject = captured.view.modelObject ∧
    view.child captured.root markerName = none ∧
    view.child captured.root keeperName = some keeper.keeperChild ∧
    crashNames markerName = [none] ∧ crashNames keeperName = [some keeper.keeperChild] ∧
    reached.2.2.visible keeper.settledImage.active = ByteArray.empty ∧
    reached.2.2.crashBytes keeper.settledImage.active = [ByteArray.empty] := by
  obtain ⟨_, _, bound, identity⟩ := keeper.settledCustody
  cases effect with
  | rawFailed => exact ⟨keeper.keeperObjects, oldAbsent, bound, congrArg (fun child => [child]) oldAbsent,
      congrArg (fun child => [child]) bound, keeper.settledVisible, keeper.settledEmpty.2⟩
  | wrapFailed created =>
    have markerNotStage : markerName ≠ stageName := by decide
    have keeperNotStage : keeperName ≠ stageName := by decide
    obtain ⟨visible, durable⟩ := created.offTargetBytes keeper.settledImage.active (identity ▸ created.separate)
    exact ⟨created.sameObjects, (created.names markerName markerNotStage).trans oldAbsent,
      (created.names keeperName keeperNotStage).trans bound,
      (created.offTargetCrash markerName markerNotStage).trans (congrArg (fun child => [child]) oldAbsent),
      (created.offTargetCrash keeperName keeperNotStage).trans (congrArg (fun child => [child]) bound),
      visible.trans keeper.settledVisible, durable.trans keeper.settledEmpty.2⟩

/-- The physical result shows a new raw close-on-exec reference only in
the wrapping failure case. It makes no later descriptor-release claim. -/
theorem rawSlot (effect : BootstrapMarkerExclusiveEffect keeper initial reached view crashNames)
    (absent : keeper.keeperView.child captured.root stageName = none) :
    (reached.1 = initial ∧ view.child captured.root stageName = none) ∨
    ∃ raw : DescriptorSlot, ∃ child : DeviceInode, ∃ metadata : IO.FS.Metadata,
    ∃ lookup : FilePath → Except IO.Error (IO.FS.Metadata × DeviceInode),
      initial.references raw.description = [] ∧ reached.1.references raw.description = [raw.reference] ∧
      raw.reference.closeOnExec = true ∧ view.child captured.root stageName = some child ∧
      view.modelObject child = reached.1.inode raw.description ∧ reached.2.2.visible (reached.1.inode raw.description) = ByteArray.empty ∧
      lookup (directory.file .stagedWalBoundary) = .ok (metadata, child) ∧
      metadata.type = .file ∧ metadata.numLinks = 1 ∧ metadata.byteSize = 0 := by
  cases effect with
  | rawFailed => exact .inl ⟨rfl, absent⟩
  | wrapFailed created =>
    have bound := created.child.binds
    rw [created.child.atRoot, created.child.atName] at bound
    exact .inr ⟨created.raw, created.child.child, created.metadata, created.lookup, created.fresh,
      by simp [DescriptorInventory.references_insert, created.fresh], created.closeOnExec, bound,
      created.object, created.empty, created.stat, created.regular, created.singleLink, created.size⟩

theorem image (effect : BootstrapMarkerExclusiveEffect keeper initial reached view crashNames) :
    reached.2.1.metadata.active = before.image.metadata.active ∧
    reached.2.1.metadata.crashImages = [before.image.metadata.active] ∧ reached.2.1.successor = .durable := by
  cases effect <;> exact ⟨rfl, rfl, rfl⟩

theorem scratch (effect : BootstrapMarkerExclusiveEffect keeper initial reached view crashNames)
    (missing : before.image.metadata.staged .walBoundary = none) :
    reached.2.1.metadata.staged .walBoundary = none ∨
      reached.2.1.metadata.staged .walBoundary = some (ByteArray.empty, false) := by
  cases effect with
  | rawFailed => exact .inl missing
  | wrapFailed _ => exact .inr rfl

end BootstrapMarkerExclusiveEffect

/-- The first exclusive stage open fails with a diagnostic other than
the EEXIST sentinel. This observation starts after the completed
keeper barrier and uses the same captured lock, directory and cache. -/
structure BootstrapMarkerOpenError (keeper : BootstrapZeroKeeperRoute listed) where
  between : List LockReferenceDrop
  lockAtOpen : calls.slot ∈ (keeper.settledInventory.afterDrops between).slots
  directoryAtOpen : captured.cached ∈ (keeper.settledInventory.afterDrops between).slots
  stageMissing : keeper.keeperView.child captured.root stageName = none
  scratchMissing : before.image.metadata.staged .walBoundary = none
  canonicalAbsent : keeper.keeperView.child captured.root markerName = none
  tryCreate : FilePath → EStateM IO.Error Native (Except IO.Error Handle)
  statStale : FilePath → EStateM IO.Error Files (Except IO.Error IO.FS.Metadata)
  unlinkStale : FilePath → EStateM IO.Error Files (Except IO.Error Unit)
  create : FilePath → EStateM IO.Error Files Handle
  write : Handle → ByteArray → EStateM IO.Error Files Unit
  flush : Handle → EStateM IO.Error Files Unit
  reached : Native
  view : DirectoryReadNamespace
  crashNames : String → List (Option DeviceInode)
  cause : IO.Error
  returned : tryCreate (directory.file .stagedWalBoundary)
    (keeper.settledInventory.afterDrops between, atStage before.image, keeper.settledImage) =
      .ok (.error cause) reached
  direct : ∀ name message, cause ≠ .alreadyExists name 17 message
  effect : BootstrapMarkerExclusiveEffect keeper (keeper.settledInventory.afterDrops between) reached view crashNames
  projection :
    calls.write captured.cache (directory.file .stagedWalBoundary) markerBytes (atStage before.image) =
      bootstrapMarkerProjection (stageFreshWithCache (directory.file .stagedWalBoundary) markerBytes
        (writeFreshStagedWith (projectExclusive tryCreate (keeper.settledInventory.afterDrops between))
          (removeStaleStagingWith statStale unlinkStale) create write flush)
        (captured.cache, atStage before.image, keeper.settledImage))

namespace BootstrapMarkerOpenError

variable {keeper : BootstrapZeroKeeperRoute listed}

noncomputable abbrev stage (observed : BootstrapMarkerOpenError keeper) :=
  writeFreshStagedWith (projectExclusive observed.tryCreate (keeper.settledInventory.afterDrops observed.between))
    (removeStaleStagingWith observed.statStale observed.unlinkStale) observed.create observed.write observed.flush

/-- The raw first-open error leaves no new pending handle. No stale
detach, write, flush or marker sync is reached. -/
theorem stageError (observed : BootstrapMarkerOpenError keeper) :
    stageFreshWithCache (directory.file .stagedWalBoundary) markerBytes observed.stage
      (captured.cache, atStage before.image, keeper.settledImage) =
      .error observed.cause (captured.cache, observed.reached.2) := by
  have returned : projectExclusive observed.tryCreate (keeper.settledInventory.afterDrops observed.between)
      (directory.file .stagedWalBoundary) (atStage before.image, keeper.settledImage) =
        .ok (.error observed.cause) observed.reached.2 := by
    simp only [projectExclusive, observed.returned]
  exact stageFreshWithCache_error captured.cache _ _ observed.stage
    (writeFreshStagedWith_openError _ _ _ _ _ returned observed.direct)

/-- The same cache and settled keeper before the failure are reached
by the actual keeper-directory barrier. -/
theorem physicalPrefix (observed : BootstrapMarkerOpenError keeper) :
    let input := keeper.keeperImage.completeFileSync keeper.keeperImage.active
    (keeper.groupedSync #[directory.path] *>
      stageFreshWithCache (directory.file .stagedWalBoundary) markerBytes observed.stage)
      (captured.cache, keeper.fileSyncedState, input) =
        .error observed.cause (captured.cache, observed.reached.2) := by
  simpa only [SeqRight.seqRight, EStateM.seqRight, keeper.reachesMarker, atStage, BootstrapZeroKeeperRoute.settledImage]
    using observed.stageError

/-- Exact physical keeper custody through the denied first stage open. -/
theorem physicalKeeper (observed : BootstrapMarkerOpenError keeper) :
    calls.slot.reference ∈ observed.reached.1.references calls.slot.description ∧
    captured.cached.reference ∈ observed.reached.1.references captured.cached.description ∧
    observed.view.modelObject = captured.view.modelObject ∧
    observed.view.child captured.root markerName = none ∧
    observed.view.child captured.root keeperName = some keeper.keeperChild ∧
    observed.crashNames markerName = [none] ∧ observed.crashNames keeperName = [some keeper.keeperChild] ∧
    observed.reached.2.2.visible keeper.settledImage.active = ByteArray.empty ∧
    observed.reached.2.2.crashBytes keeper.settledImage.active = [ByteArray.empty] := by
  let initial := keeper.settledInventory.afterDrops observed.between
  have lockPresent := initial.mem_references.mpr ⟨calls.slot, observed.lockAtOpen, rfl, rfl⟩
  have dirPresent := initial.mem_references.mpr ⟨captured.cached, observed.directoryAtOpen, rfl, rfl⟩
  exact ⟨(observed.effect.keepsReferences (List.ne_nil_of_mem lockPresent)).symm ▸ lockPresent,
    (observed.effect.keepsReferences (List.ne_nil_of_mem dirPresent)).symm ▸ dirPresent,
    observed.effect.keepsKeeper observed.canonicalAbsent⟩

theorem worker (observed : BootstrapMarkerOpenError keeper) (valid : BootstrapValid before.image) :
    calls.bootstrapAt directory captured.cache before.image = .error observed.cause observed.reached.2.1 ∧
    BootstrapValid observed.reached.2.1 := by
  have failed := observed.projection.trans (congrArg bootstrapMarkerProjection observed.stageError)
  obtain ⟨active, crash, durable⟩ := observed.effect.image
  have result := bootstrapEmptyWith_writeStagedError directory before.image valid before.image.observeSuccessor rfl
    (calls.createEmpty captured.cache) (calls.write captured.cache) (calls.sync captured.cache) calls.renameFile
    keeper.rotationHealthy failed active crash durable
  exact ⟨(calls.reachesPublication captured.cache listed.entries.1 listed.entries.2).trans result.1, result.2⟩

def final (observed : BootstrapMarkerOpenError keeper) : LockedFileState WalSegmentRotation.State :=
  ⟨observed.reached.2.1, before.owners.set (directory.file .lock)
    (match calls.unlock with | .success => none | .failure _ _ => some calls.slot.description)⟩

def returnedError (observed : BootstrapMarkerOpenError keeper) : IO.Error :=
  match calls.unlock with | .success => observed.cause | .failure cleanup _ => cleanup

/-- Native local lock cleanup propagates the exact reached file state.
The wrapper error leaves either no scratch or the empty unsynced inode. -/
theorem returns {input : FilePath} (observed : BootstrapMarkerOpenError keeper)
    (admission : OpenAdmissionReports input directory calls.slot) (valid : BootstrapValid before.image)
    (localUnlock : calls.unlock.LocalFlock) :
    calls.run admission = .error observed.returnedError observed.final ∧ BootstrapValid observed.final.image ∧
    observed.final.image.metadata.active.walBoundary = none ∧
    observed.final.image.metadata.crashImages = [before.image.metadata.active] ∧
    observed.final.image.successor = .durable ∧
    (observed.final.image.metadata.staged .walBoundary = none ∨
      observed.final.image.metadata.staged .walBoundary = some (ByteArray.empty, false)) := by
  obtain ⟨active, crash, durable⟩ := observed.effect.image
  have returned := (observed.worker valid).1
  have cleanup := runOpenWithInstallation_acquiredRecoveryError directory calls.slot.description calls.nextRef
    calls.unlock (calls.bootstrapAt directory captured.cache) before returned
  refine ⟨?_, (observed.worker valid).2, ?_, crash, durable, ?_⟩
  · rw [calls.runMarkerless admission captured.captures.1, cleanup]
    cases outcome : calls.unlock with
    | success => simp [final, returnedError, outcome]
    | failure error released =>
      have retained : released = false := by simpa [outcome, UnlockReport.LocalFlock] using localUnlock
      subst released
      simp [final, returnedError, outcome]
  · change observed.reached.2.1.metadata.active.walBoundary = none
    rw [active]
    exact calls.markerAbsent.1
  · exact observed.effect.scratch observed.scratchMissing

/-- Dispatch a later admitted open on the exact returned file image.
Acquiring that lock and initializing its cache remain reported steps. -/
theorem retryMarkerless {input nextInput : FilePath} (observed : BootstrapMarkerOpenError keeper)
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

end BootstrapMarkerOpenError

end Alvoki.Storage.DiskSession
