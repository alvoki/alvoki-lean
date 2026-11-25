import Alvoki.Storage.Disk.BootstrapZeroKeeperCustody
import Alvoki.Storage.Disk.ObservedBootstrapRetry

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

private abbrev Handle := DescriptorInventory × DescriptorSlot × Nat
private abbrev Files := WalSegmentRotation.State × WalInodeImage
private abbrev keeperName := renderWalSegmentName 0
private abbrev markerName := "WAL.commit"
private abbrev keeperPath (directory : DiskDirectory) := directory.file (.walSegment 0)

variable {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {calls : BootstrapOpenCalls (Cache Handle) directory before}
  {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls}

namespace BootstrapZeroKeeperFilePrefix

variable {listed : BootstrapCheckedListing captured}

/-- Both reported file prefixes use the captured lock and directory.
The keeper's canonical child has the same file-synced inode and empty bytes. -/
theorem syncedCustody (route : BootstrapZeroKeeperFilePrefix listed) :
    calls.slot ∈ route.inventory.slots ∧ captured.cached ∈ route.inventory.slots ∧
    route.view.modelObject captured.root = route.inventory.inode captured.cached.description ∧
    route.view.child captured.root keeperName = some route.child ∧
    route.view.modelObject route.child = route.synced.active ∧
    route.synced.active = route.inventory.inode route.keeperSlot.description ∧
    route.synced.visible route.synced.active = ByteArray.empty ∧
    route.synced.crashBytes route.synced.active = [ByteArray.empty] := by
  have directoryObject := captured.captures.2.2.2.2
  cases route with
  | fresh reported =>
    have root := reported.sameObjects.symm ▸ directoryObject
    have bound := reported.child.binds
    rw [reported.child.atRoot, reported.child.atName] at bound
    refine ⟨reported.lockLive, reported.directoryLive, ?_, bound, reported.active.symm,
      reported.active.trans reported.object, reported.empty, ?_⟩
    · change reported.namespaceView.modelObject captured.root = listed.scan.afterClose.inode captured.cached.description
      rw [listed.scan.afterClose_eq]
      exact root
    · simp [synced, inodeImage, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, reported.empty]
  | reused reported =>
    have bound := reported.statChild.binds
    rw [reported.statChild.atRoot, reported.statChild.atName] at bound
    have sameChild := reported.openedChild.child_eq bound
    have empty := reported.readEmpty.2.2
    refine ⟨reported.lockLive, reported.directoryLive, ?_, bound, reported.statObject,
      reported.statObject.symm.trans ((congrArg captured.view.modelObject sameChild).symm.trans reported.openedObject),
      empty, ?_⟩
    · change captured.view.modelObject captured.root = listed.scan.afterClose.inode captured.cached.description
      rw [listed.scan.afterClose_eq]
      exact directoryObject
    · simp [synced, inodeImage, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, empty]

theorem projectDirectory (route : BootstrapZeroKeeperFilePrefix listed) :
    calls.sync captured.cache #[directory.path] route.state =
    zeroKeeperProjection (route.grouped #[directory.path] (captured.cache, route.state, route.synced)) := by
  cases route with
  | fresh reported => exact reported.projectDirectory
  | reused reported => exact reported.projectDirectory

private theorem metadata (route : BootstrapZeroKeeperFilePrefix listed) : route.state.metadata = before.image.metadata := by
  cases route <;> rfl

private theorem binding (route : BootstrapZeroKeeperFilePrefix listed) :
    (route.state.successor = .fileSynced ∨ route.state.successor = .durable) ∧
    (before.image.successor = .durable → route.state.successor = .durable) := by
  cases route with
  | fresh reported =>
    exact ⟨.inl rfl, fun durable => by rw [reported.absentSegment] at durable; contradiction⟩
  | reused reported =>
    have present : before.image.successor ≠ .absent := by
      intro absent
      have seen := reported.readEmpty.2.1
      simp [WalSegmentRotation.State.observeSuccessor, absent] at seen
    let result : WalSegmentRotation.Binding := if before.image.successor = .created then .fileSynced else before.image.successor
    change (result = .fileSynced ∨ result = .durable) ∧ (before.image.successor = .durable → result = .durable)
    cases seen : before.image.successor <;>
      simp_all [result]

/-- The actual vector of rotation callbacks stops at the failed keeper
directory sync after the successful create and file sync, or file sync
alone when the no-follow probe found an existing empty inode. -/
theorem rotationError (route : BootstrapZeroKeeperFilePrefix listed) {cause reached}
    (failed : calls.sync captured.cache #[directory.path] route.state = .error cause reached) :
    WalSegmentRotation.runAt directory 0 (fun _ => EStateM.pure before.image.observeSuccessor)
      (calls.createEmpty captured.cache) (fun path => calls.sync captured.cache #[path]) before.image = .error cause reached := by
  cases route with
  | fresh reported =>
    obtain ⟨created, file⟩ := reported.filePrefix
    have createProjected : calls.createEmpty captured.cache (keeperPath directory) before.image =
        .ok () ⟨before.image.metadata, .created⟩ :=
      reported.projectCreate.trans (congrArg zeroKeeperProjection created)
    have fileProjected : calls.sync captured.cache #[keeperPath directory] ⟨before.image.metadata, .created⟩ =
        .ok () ⟨before.image.metadata, .fileSynced⟩ :=
      reported.projectFile.trans (congrArg zeroKeeperProjection file)
    have absent : before.image.observeSuccessor = none := by
      simp [WalSegmentRotation.State.observeSuccessor, reported.absentSegment]
    simp [WalSegmentRotation.runAt, WalSegmentRotation.observeSuccessorWith, WalSegmentRotation.run,
      WalSegmentRotation.steps, WalSegmentRotation.performPaths, List.forM_eq_forM, Bind.bind, EStateM.bind,
      Pure.pure, EStateM.pure, absent, createProjected, fileProjected, state] at failed ⊢
    rw [failed]
  | reused reported =>
    have fileProjected : calls.sync captured.cache #[keeperPath directory] before.image =
        .ok () reported.fileSyncedState :=
      reported.projectFile.trans (congrArg zeroKeeperProjection reported.filePrefix)
    have present := reported.readEmpty.2.1
    simp [WalSegmentRotation.runAt, WalSegmentRotation.observeSuccessorWith, WalSegmentRotation.run,
      WalSegmentRotation.steps, WalSegmentRotation.performPaths, List.forM_eq_forM, Bind.bind, EStateM.bind,
      Pure.pure, EStateM.pure, present, fileProjected, state] at failed ⊢
    rw [failed]

end BootstrapZeroKeeperFilePrefix

variable {listed : BootstrapCheckedListing captured} {route : BootstrapZeroKeeperFilePrefix listed}

/-- The retained directory handle reports a failure before or after
settlement. The prebarrier keeper name choices project to the same
file-synced inode image. No marker callback has been reached. -/
structure BootstrapKeeperDirectoryError (route : BootstrapZeroKeeperFilePrefix listed) where
  cause : IO.Error
  effective : Bool
  failed : route.fsync (captured.reached, captured.cached, 0) (route.state, route.synced) =
    .error cause (if effective then (⟨before.image.metadata.syncDirectory, .durable⟩, route.synced.settleBinding)
      else (route.state, route.synced))
  markerAbsent : route.view.child captured.root markerName = none
  priorNames : List (Option DeviceInode)
  priorChoices : ∀ choice ∈ priorNames, choice = none ∨ choice = some route.child
  priorProjected : priorNames.filterMap (Option.map route.view.modelObject) = route.synced.crashBindings
  priorSettled : route.state.successor = .durable → priorNames = [some route.child]

namespace BootstrapKeeperDirectoryError

def reached (observed : BootstrapKeeperDirectoryError route) : Files :=
  if observed.effective then (⟨before.image.metadata.syncDirectory, .durable⟩, route.synced.settleBinding)
  else (route.state, route.synced)

def error (observed : BootstrapKeeperDirectoryError route) : IO.Error :=
  IO.userError s!"sync failed for '{directory.path}': {observed.cause}"

def survivingNames (observed : BootstrapKeeperDirectoryError route) : List (Option DeviceInode) :=
  if observed.effective then [some route.child] else observed.priorNames

/-- The actual grouped callback reuses the original directory slot. Its
error includes that path and leaves the cache intact. -/
theorem directoryBarrier (observed : BootstrapKeeperDirectoryError route) :
    route.grouped #[directory.path] (captured.cache, route.state, route.synced) =
      .error observed.error (captured.cache, observed.reached) := by
  unfold BootstrapZeroKeeperFilePrefix.grouped
  rw [SyncPathGroup.run_single]
  simp [sync, Cache.resolve, BootstrapCacheOpen.cache, observed.failed, reached, error, withCache]
  rfl

/-- The names and inode bytes keep the same physical keeper. The effect
settles its name, while a pre-effect failure preserves prior choices. -/
theorem keeper (observed : BootstrapKeeperDirectoryError route) :
    calls.slot ∈ route.inventory.slots ∧ captured.cached ∈ route.inventory.slots ∧
    route.view.modelObject captured.root = route.inventory.inode captured.cached.description ∧
    route.view.child captured.root keeperName = some route.child ∧ route.view.child captured.root markerName = none ∧
    route.view.modelObject route.child = observed.reached.2.active ∧
    observed.reached.2.active = route.inventory.inode route.keeperSlot.description ∧
    observed.reached.2.visible observed.reached.2.active = ByteArray.empty ∧
    observed.reached.2.crashBytes observed.reached.2.active = [ByteArray.empty] ∧
    observed.survivingNames.filterMap (Option.map route.view.modelObject) = observed.reached.2.crashBindings := by
  obtain ⟨lock, dir, root, child, object, issuer, empty, bytes⟩ := route.syncedCustody
  refine ⟨lock, dir, root, child, observed.markerAbsent, ?_⟩
  cases effect : observed.effective
  · simpa only [reached, survivingNames, effect, Bool.false_eq_true, ite_false] using
      And.intro object (And.intro issuer (And.intro empty (And.intro bytes observed.priorProjected)))
  · simp only [reached, survivingNames, effect, ite_true]
    refine ⟨object, issuer, empty, bytes, ?_⟩
    simp [WalInodeImage.settleBinding, object]

private theorem validReached (observed : BootstrapKeeperDirectoryError route) (valid : BootstrapValid before.image) :
    BootstrapValid observed.reached.1 := by
  cases effect : observed.effective
  · have validPrefix : BootstrapValid route.state := by
      refine ⟨route.metadata ▸ valid.metadata, ?_⟩
      intro pair choice marked
      rw [route.metadata] at choice
      exact route.binding.2 (valid.marked pair choice marked)
    simpa [reached, effect] using validPrefix
  · simpa [reached, effect] using
      (show BootstrapValid ⟨before.image.metadata.syncDirectory, .durable⟩ from ⟨valid.metadata.syncDirectory, fun _ _ _ => rfl⟩)

/-- The reached worker returns the keeper directory error before starting
the marker stage. The selected phase follows the actual rotation prefix. -/
theorem worker (observed : BootstrapKeeperDirectoryError route) (valid : BootstrapValid before.image) :
    calls.bootstrapAt directory captured.cache before.image = .error observed.error observed.reached.1 ∧
    BootstrapValid observed.reached.1 := by
  have failed : calls.sync captured.cache #[directory.path] route.state = .error observed.error observed.reached.1 :=
    route.projectDirectory.trans (congrArg zeroKeeperProjection observed.directoryBarrier)
  have rotation := route.rotationError failed
  change WalSegmentRotation.runAt directory 0 (fun _ => pure before.image.observeSuccessor)
    (calls.createEmpty captured.cache) (fun path => calls.sync captured.cache #[path]) before.image =
    .error observed.error observed.reached.1 at rotation
  refine ⟨?_, observed.validReached valid⟩
  rw [calls.reachesPublication captured.cache listed.entries.1 listed.entries.2]
  simp only [bootstrapEmptyWith, bootstrapEmptyWithMarker, Bind.bind, EStateM.bind, rotation]

def final (observed : BootstrapKeeperDirectoryError route) : LockedFileState WalSegmentRotation.State :=
  ⟨observed.reached.1, before.owners.set (directory.file .lock)
    (match calls.unlock with | .success => none | .failure _ _ => some calls.slot.description)⟩

def returnedError (observed : BootstrapKeeperDirectoryError route) : IO.Error :=
  match calls.unlock with | .success => observed.error | .failure cleanup _ => cleanup

/-- Local unlock determines the exact returned error and owner while
framing the file state at the stopped keeper barrier. -/
theorem returns {input : FilePath} (observed : BootstrapKeeperDirectoryError route)
    (admission : OpenAdmissionReports input directory calls.slot) (valid : BootstrapValid before.image)
    (localUnlock : calls.unlock.LocalFlock) :
    calls.run admission = .error observed.returnedError observed.final ∧
    BootstrapValid observed.final.image ∧ observed.final.image.metadata.active.walBoundary = none ∧
    observed.final.image.observeSuccessor = some ByteArray.empty := by
  have outcome := runOpenWithInstallation_acquiredRecoveryError directory calls.slot.description calls.nextRef calls.unlock
    (calls.bootstrapAt directory captured.cache) before (observed.worker valid).1
  refine ⟨?_, (observed.worker valid).2, ?_, ?_⟩
  · rw [calls.runMarkerless admission captured.captures.1, outcome]
    cases unlock : calls.unlock with
    | success => simp [final, returnedError, unlock]
    | failure cleanup released =>
      have held : released = false := by simpa [UnlockReport.LocalFlock, unlock] using localUnlock
      subst released
      simp [final, returnedError, unlock]
  · cases effect : observed.effective <;>
      simp [final, reached, effect, route.metadata, calls.markerAbsent.1, DirectoryPublication.Image.syncDirectory]
  · cases effect : observed.effective
    · rcases route.binding.1 with synced | durable <;>
        simp [final, reached, WalSegmentRotation.State.observeSuccessor, *]
    · simp [final, reached, effect, WalSegmentRotation.State.observeSuccessor]

/-- A surviving binding is absent or names the original empty keeper.
Its presence agrees with the bootstrap rotation state. The metadata
choice is unchanged before the effect and settled after the effect. -/
theorem crashSelection (observed : BootstrapKeeperDirectoryError route) (valid : BootstrapValid before.image)
    {pair : DirectoryPublication.Bindings} (metadata : pair ∈ observed.final.image.metadata.crashImages)
    {binding : Option DeviceInode} (name : binding ∈ observed.survivingNames) :
    let crashed := bootstrapPowerLoss directory observed.final pair binding.isSome
    (binding = none ∨ binding = some route.child) ∧
    (observed.effective = true → binding = some route.child ∧ pair = before.image.metadata.active) ∧
    BootstrapValid crashed.image ∧
    crashed.image.observeSuccessor = binding.map (fun _ => ByteArray.empty) ∧
    (binding = some route.child → observed.reached.2.crashBytes observed.reached.2.active = [ByteArray.empty]) := by
  intro crashed
  have allowed : observed.final.image.successor.MaySurvive binding.isSome := by
    cases effect : observed.effective
    · have unchanged : observed.final.image.successor = route.state.successor := by simp [final, reached, effect]
      rw [unchanged]
      rcases route.binding.1 with synced | durable
      · rw [synced]; trivial
      · rw [durable]
        have names := observed.priorSettled durable
        simp [survivingNames, effect, names] at name
        simp [name, WalSegmentRotation.Binding.MaySurvive]
    · simp [survivingNames, effect] at name
      simp [final, reached, effect, name, WalSegmentRotation.Binding.MaySurvive]
  obtain ⟨_, _, _, _, _, _, _, _, bytes, _⟩ := observed.keeper
  refine ⟨?_, ?_, (observed.validReached valid).crash metadata allowed, ?_, fun _ => bytes⟩
  · cases effect : observed.effective
    · exact observed.priorChoices binding (by simpa [survivingNames, effect] using name)
    · exact .inr (by simpa [survivingNames, effect] using name)
  · intro effective
    exact ⟨by simpa [survivingNames, effective] using name,
      by simpa [final, reached, effective, DirectoryPublication.Image.syncDirectory] using metadata⟩
  · cases binding <;> rfl

/-- A fresh admission that reports an absent canonical marker dispatches
the same bootstrap worker from the exact failed state. -/
theorem retryMarkerless {input nextInput : FilePath} (observed : BootstrapKeeperDirectoryError route)
    (admission : OpenAdmissionReports input directory calls.slot) (valid : BootstrapValid before.image)
    (localUnlock : calls.unlock.LocalFlock)
    {retry : BootstrapAdmissionCalls (Cache Handle) directory observed.final}
    (nextCache : BootstrapCacheOpen retry) (nextAdmission : OpenAdmissionReports nextInput directory retry.slot)
    {name message : String}
    (missing : retry.lookup (directory.file .walBoundary) = .error (.noFileOrDirectory name 2 message))
    (bootstrap : DiskDirectory → Cache Handle → EStateM IO.Error WalSegmentRotation.State Reopened) :
    calls.run admission = .error observed.returnedError observed.final ∧
    retry.run bootstrap nextAdmission =
      runOpenWithInstallation directory retry.slot.description retry.nextRef (.ok true) retry.unlock
        (bootstrap directory nextCache.cache) observed.final := by
  exact ⟨(observed.returns admission valid localUnlock).1,
    retry.runSelected bootstrap nextAdmission nextCache.captures.1 (marker := none)
      (by simp [optionalMetadataWith, missing, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure])⟩

end BootstrapKeeperDirectoryError

end Alvoki.Storage.DiskSession
