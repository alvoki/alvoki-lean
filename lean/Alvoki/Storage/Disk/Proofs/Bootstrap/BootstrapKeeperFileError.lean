import Alvoki.Storage.Disk.Proofs.Bootstrap.BootstrapZeroKeeperCustody
import Alvoki.Storage.Disk.Proofs.Bootstrap.ObservedBootstrapRetry

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

private abbrev Handle := DescriptorInventory × DescriptorSlot × Nat
private abbrev Files := WalSegmentRotation.State × WalInodeImage
private abbrev keeperName := renderWalSegmentName 0
private abbrev keeperPath (directory : DiskDirectory) := directory.file (.walSegment 0)

variable {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {calls : BootstrapOpenCalls (Cache Handle) directory before}
  {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls}
  {listed : BootstrapCheckedListing captured}

/-- The first keeper barrier either consumes the descriptor from exclusive
creation or opens the already present empty child on a cache miss. -/
inductive BootstrapZeroKeeperOpened (listed : BootstrapCheckedListing captured) where
  | fresh (reported : BootstrapFreshZeroKeeperOpen listed)
  | reused (reported : BootstrapReusedZeroKeeperOpen listed)

namespace BootstrapZeroKeeperOpened

def handle : BootstrapZeroKeeperOpened listed → Handle
  | .fresh report => ((listed.scan.afterClose.afterDrops report.beforeCreate).insert report.slot report.free, report.slot, 0)
  | .reused report => ((listed.scan.afterClose.afterDrops report.beforeOpen).insert report.slot report.free, report.slot, 0)

def atFile : BootstrapZeroKeeperOpened listed → Files
  | .fresh report => (⟨before.image.metadata, .created⟩, report.opened)
  | .reused report => (before.image, report.files)

def view : BootstrapZeroKeeperOpened listed → DirectoryReadNamespace
  | .fresh report => report.namespaceView
  | .reused _ => captured.view

def child : BootstrapZeroKeeperOpened listed → DeviceInode
  | .fresh report => report.child.child
  | .reused report => report.statChild.child

def openRead : BootstrapZeroKeeperOpened listed → FilePath → EStateM IO.Error Files Handle
  | .fresh report => report.openRead
  | .reused report => report.openRead

def fsync : BootstrapZeroKeeperOpened listed → Handle → EStateM IO.Error Files Unit
  | .fresh report => report.fsync
  | .reused report => report.fsync

def cache (route : BootstrapZeroKeeperOpened listed) : Cache Handle :=
  match route with
  | .fresh _ => captured.cache.remember (keeperPath directory) route.handle
  | .reused _ => captured.cache

def grouped (route : BootstrapZeroKeeperOpened listed) : Array FilePath → EStateM IO.Error (Cache Handle × Files) Unit :=
  SyncPathGroup.run (sync directory.path route.openRead route.fsync)

def atFileInventory (route : BootstrapZeroKeeperOpened listed) : DescriptorInventory :=
  match route with
  | .fresh report => route.handle.1.afterDrops report.beforeFile
  | .reused report => route.handle.1.afterDrops report.beforeFile

def afterFileInventory (route : BootstrapZeroKeeperOpened listed) : DescriptorInventory :=
  match route with
  | .fresh report => route.handle.1.afterDrops (report.beforeFile ++ report.afterFile)
  | .reused report => route.handle.1.afterDrops (report.beforeFile ++ report.afterFile)

private theorem metadata (route : BootstrapZeroKeeperOpened listed) : route.atFile.1.metadata = before.image.metadata := by
  cases route <;> rfl

private theorem present (route : BootstrapZeroKeeperOpened listed) : route.atFile.1.successor ≠ .absent := by
  cases route with
  | fresh => simp [atFile]
  | reused report =>
    intro absent
    have seen := report.readEmpty.2.1
    simp [atFile] at absent
    simp [WalSegmentRotation.State.observeSuccessor, absent] at seen

theorem custody (route : BootstrapZeroKeeperOpened listed) :
    route.handle.2.1 ∈ route.atFileInventory.slots ∧
    calls.slot ∈ route.afterFileInventory.slots ∧ captured.cached ∈ route.afterFileInventory.slots ∧
    route.view.modelObject captured.root = route.afterFileInventory.inode captured.cached.description ∧
    route.view.child captured.root keeperName = some route.child ∧
    route.view.modelObject route.child = route.atFile.2.active ∧
    route.atFile.2.active = route.atFileInventory.inode route.handle.2.1.description ∧
    route.atFile.2.visible route.atFile.2.active = ByteArray.empty := by
  have directoryObject := captured.captures.2.2.2.2
  cases route with
  | fresh report =>
    have bound := report.child.binds
    rw [report.child.atRoot, report.child.atName] at bound
    refine ⟨report.fileLive, report.lockLive, report.directoryLive, ?_, bound, report.active.symm,
      report.active.trans report.object, report.empty⟩
    change report.namespaceView.modelObject captured.root = listed.scan.afterClose.inode captured.cached.description
    rw [listed.scan.afterClose_eq]
    exact report.sameObjects.symm ▸ directoryObject
  | reused report =>
    have bound := report.statChild.binds
    rw [report.statChild.atRoot, report.statChild.atName] at bound
    have sameChild := report.openedChild.child_eq bound
    refine ⟨report.fileLive, report.lockLive, report.directoryLive, ?_, bound, report.statObject,
      report.statObject.symm.trans ((congrArg captured.view.modelObject sameChild).symm.trans report.openedObject),
      report.readEmpty.2.2⟩
    change captured.view.modelObject captured.root = listed.scan.afterClose.inode captured.cached.description
    rw [listed.scan.afterClose_eq]
    exact directoryObject

end BootstrapZeroKeeperOpened

variable {route : BootstrapZeroKeeperOpened listed}

/-- The reported file effect changes only the targeted inode's crash
bytes. It does not settle the keeper's directory binding or publish
the marker. A surviving pre-effect binding is supplied by observation. -/
structure BootstrapKeeperFileError (route : BootstrapZeroKeeperOpened listed) where
  cause : IO.Error
  effective : Bool
  failed : route.fsync route.handle route.atFile =
    .error cause (if effective then ((route.atFile.1.step .syncFile).getD route.atFile.1,
      route.atFile.2.completeFileSync route.atFile.2.active) else route.atFile)
  markerAbsent : route.view.child captured.root "WAL.commit" = none
  names : List (Option DeviceInode)
  nameChoice : ∀ binding ∈ names, binding = none ∨ binding = some route.child
  projectedNames : names.filterMap (Option.map route.view.modelObject) = route.atFile.2.crashBindings
  durableName : route.atFile.1.successor = .durable → names = [some route.child]
  emptySurvivor : some route.child ∈ names →
    ∀ bytes ∈ route.atFile.2.crashBytes route.atFile.2.active, bytes = ByteArray.empty

namespace BootstrapKeeperFileError

def reached (observed : BootstrapKeeperFileError route) : Files :=
  if observed.effective then ((route.atFile.1.step .syncFile).getD route.atFile.1,
    route.atFile.2.completeFileSync route.atFile.2.active) else route.atFile

def error (observed : BootstrapKeeperFileError route) : IO.Error :=
  IO.userError s!"sync failed for '{keeperPath directory}': {observed.cause}"

/-- The grouped file sync keeps the reached file state and consumes
any pending keeper reference before reporting the pathname error. -/
theorem fileBarrier (observed : BootstrapKeeperFileError route) :
    route.grouped #[keeperPath directory] (route.cache, route.atFile) =
    .error observed.error (captured.cache, observed.reached) := by
  have failed : route.fsync route.handle route.atFile = .error observed.cause observed.reached :=
    observed.failed
  unfold BootstrapZeroKeeperOpened.grouped
  rw [SyncPathGroup.run_single]
  cases route with
  | fresh report =>
    rw [show (.fresh report : BootstrapZeroKeeperOpened listed).cache =
      captured.cache.remember (keeperPath directory) (.fresh report : BootstrapZeroKeeperOpened listed).handle from rfl,
      syncRemembered (zeroPath_ne_directory directory), failed]
    rfl
  | reused report =>
    have separate : (keeperPath directory == directory.path) = false := by
      simpa using zeroPath_ne_directory directory
    change report.fsync ((listed.scan.afterClose.afterDrops report.beforeOpen).insert report.slot report.free,
      report.slot, 0) (before.image, report.files) = _ at failed
    have pending : captured.cache.pending = [] := rfl
    have active : captured.cache.active = none := rfl
    simp [BootstrapZeroKeeperOpened.cache, BootstrapZeroKeeperOpened.atFile,
      BootstrapZeroKeeperOpened.openRead, BootstrapZeroKeeperOpened.fsync, sync, Cache.resolve,
      pending, active, separate, report.opened, failed, withCache, error]
    rfl

/-- The callback targets the live keeper description. Its effect preserves
the canonical child and its visible empty bytes. The captured directory
and writer slots remain in the reported post-file census. -/
theorem keeper (observed : BootstrapKeeperFileError route) :
    route.handle.2.1 ∈ route.atFileInventory.slots ∧
    calls.slot ∈ route.afterFileInventory.slots ∧ captured.cached ∈ route.afterFileInventory.slots ∧
    route.view.modelObject captured.root = route.afterFileInventory.inode captured.cached.description ∧
    route.view.child captured.root keeperName = some route.child ∧
    route.view.child captured.root "WAL.commit" = none ∧
    route.view.modelObject route.child = observed.reached.2.active ∧
    observed.reached.2.active = route.atFileInventory.inode route.handle.2.1.description ∧
    observed.reached.2.visible observed.reached.2.active = ByteArray.empty := by
  obtain ⟨live, lock, directoryLive, root, child, object, identity, empty⟩ := route.custody
  refine ⟨live, lock, directoryLive, root, child, observed.markerAbsent, ?_⟩
  cases effect : observed.effective <;>
    simpa [reached, effect, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync] using
      (show _ ∧ _ ∧ _ from ⟨object, identity, empty⟩)

private theorem reachedBinding (observed : BootstrapKeeperFileError route) :
    observed.reached.1.metadata = before.image.metadata ∧ observed.reached.1.successor ≠ .absent ∧
    (before.image.successor = .durable → observed.reached.1.successor = .durable) ∧
    (route.atFile.1.successor = .durable ↔ observed.reached.1.successor = .durable) := by
  have unchanged := route.metadata
  have present := route.present
  have durable (old : before.image.successor = .durable) : route.atFile.1.successor = .durable := by
    cases route with
    | fresh report => rw [report.absentSegment] at old; contradiction
    | reused => exact old
  cases effect : observed.effective
  · exact ⟨by simpa [reached, effect] using unchanged, by simpa [reached, effect] using present,
      by simpa [reached, effect] using durable, by simp [reached, effect]⟩
  · cases state : route.atFile.1 with
    | mk metadata binding =>
      cases binding <;>
        simp_all [reached, WalSegmentRotation.State.step]

/-- The worker stops at the selected keeper file sync. The marker and
directory barriers have no role in the returned state. -/
theorem worker (observed : BootstrapKeeperFileError route) (valid : BootstrapValid before.image) :
    calls.bootstrapAt directory captured.cache before.image = .error observed.error observed.reached.1 ∧
    BootstrapValid observed.reached.1 := by
  have binding := observed.reachedBinding
  constructor
  · rw [calls.reachesPublication captured.cache listed.entries.1 listed.entries.2]
    have rotation : WalSegmentRotation.runAt directory 0 (fun _ => pure before.image.observeSuccessor)
        (calls.createEmpty captured.cache) (fun path => calls.sync captured.cache #[path]) before.image =
        .error observed.error observed.reached.1 := by
      cases route with
      | fresh report =>
        have created : calls.createEmpty captured.cache (keeperPath directory) before.image =
            .ok () ⟨before.image.metadata, .created⟩ :=
          report.projectCreate.trans (congrArg zeroKeeperProjection report.create)
        have file : calls.sync captured.cache #[keeperPath directory] ⟨before.image.metadata, .created⟩ =
            .error observed.error observed.reached.1 :=
          report.projectFile.trans (congrArg zeroKeeperProjection observed.fileBarrier)
        have absent : before.image.observeSuccessor = none := by
          simp [WalSegmentRotation.State.observeSuccessor, report.absentSegment]
        simp [WalSegmentRotation.runAt, WalSegmentRotation.observeSuccessorWith, WalSegmentRotation.run,
          WalSegmentRotation.steps, WalSegmentRotation.performPaths, List.forM_eq_forM, Bind.bind, EStateM.bind,
          Pure.pure, EStateM.pure, absent, created, file]
      | reused report =>
        have file : calls.sync captured.cache #[keeperPath directory] before.image =
            .error observed.error observed.reached.1 :=
          report.projectFile.trans (congrArg zeroKeeperProjection observed.fileBarrier)
        simp [WalSegmentRotation.runAt, WalSegmentRotation.observeSuccessorWith, WalSegmentRotation.run,
          WalSegmentRotation.steps, WalSegmentRotation.performPaths, List.forM_eq_forM, Bind.bind, EStateM.bind,
          Pure.pure, EStateM.pure, report.readEmpty.2.1, file]
    simp only [bootstrapEmptyWith, Bind.bind, EStateM.bind, rotation]
  · refine ⟨binding.1 ▸ valid.metadata, ?_⟩
    intro pair choice marker
    rw [binding.1] at choice
    exact binding.2.2.1 (valid.marked pair choice marker)

def final (observed : BootstrapKeeperFileError route) : LockedFileState WalSegmentRotation.State :=
  ⟨observed.reached.1, before.owners.set (directory.file .lock)
    (match calls.unlock with | .success => none | .failure _ _ => some calls.slot.description)⟩

def returnedError (observed : BootstrapKeeperFileError route) : IO.Error :=
  match calls.unlock with | .success => observed.error | .failure cleanup _ => cleanup

theorem returns {input : FilePath} (observed : BootstrapKeeperFileError route)
    (admission : OpenAdmissionReports input directory calls.slot) (valid : BootstrapValid before.image)
    (localUnlock : calls.unlock.LocalFlock) :
    calls.run admission = .error observed.returnedError observed.final ∧
    BootstrapValid observed.final.image ∧ observed.final.image.metadata.active.walBoundary = none ∧
    observed.final.image.observeSuccessor = some ByteArray.empty := by
  have outcome := runOpenWithInstallation_acquiredRecoveryError directory calls.slot.description calls.nextRef calls.unlock
    (calls.bootstrapAt directory captured.cache) before (observed.worker valid).1
  have binding := observed.reachedBinding
  refine ⟨?_, (observed.worker valid).2, ?_, ?_⟩
  · rw [calls.runMarkerless admission captured.captures.1, outcome]
    cases unlock : calls.unlock with
    | success => simp [final, returnedError, unlock]
    | failure cleanup released =>
      have held : released = false := by simpa [UnlockReport.LocalFlock, unlock] using localUnlock
      subst released
      simp [final, returnedError, unlock]
  · exact binding.1 ▸ calls.markerAbsent.1
  · simp [final, WalSegmentRotation.State.observeSuccessor, binding.2.1]

/-- Syncing only the inode leaves the old directory choices in force.
A surviving keeper still has its reported empty contents. -/
theorem crashSelection (observed : BootstrapKeeperFileError route) (valid : BootstrapValid before.image)
    {pair : DirectoryPublication.Bindings} (metadata : pair ∈ observed.final.image.metadata.crashImages)
    {name : Option DeviceInode} (chosen : name ∈ observed.names) :
    let crashed := bootstrapPowerLoss directory observed.final pair name.isSome
    (name = none ∨ name = some route.child) ∧
    observed.names.filterMap (Option.map route.view.modelObject) = observed.reached.2.crashBindings ∧
    BootstrapValid crashed.image ∧ crashed.image.observeSuccessor = name.map (fun _ => ByteArray.empty) ∧
    (name = some route.child → ∀ bytes ∈ observed.reached.2.crashBytes observed.reached.2.active,
      bytes = ByteArray.empty) := by
  intro crashed
  have binding := observed.reachedBinding
  have allowed : observed.final.image.successor.MaySurvive name.isSome := by
    change observed.reached.1.successor.MaySurvive name.isSome
    cases state : observed.reached.1.successor with
    | absent => exact False.elim (binding.2.1 state)
    | created => trivial
    | fileSynced => trivial
    | durable =>
      have names := observed.durableName (binding.2.2.2.mpr state)
      simp [names] at chosen
      simp [chosen, WalSegmentRotation.Binding.MaySurvive]
  refine ⟨observed.nameChoice name chosen, ?_, (observed.worker valid).2.crash metadata allowed, ?_, ?_⟩
  · cases effect : observed.effective <;>
      simpa [reached, effect, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync] using observed.projectedNames
  · cases name <;> rfl
  · intro same bytes member
    cases effect : observed.effective
    · exact observed.emptySurvivor (same ▸ chosen) bytes (by simpa [reached, effect] using member)
    · obtain ⟨_, _, _, _, _, _, _, empty⟩ := route.custody
      simpa [reached, effect, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, empty] using member

theorem retryMarkerless {input nextInput : FilePath} (observed : BootstrapKeeperFileError route)
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

end BootstrapKeeperFileError
end Alvoki.Storage.DiskSession
