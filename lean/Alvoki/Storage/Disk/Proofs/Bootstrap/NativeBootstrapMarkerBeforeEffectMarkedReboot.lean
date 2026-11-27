import Alvoki.Storage.Disk.Proofs.Bootstrap.NativeBootstrapMarkerRebootTableOpen

namespace Alvoki.Storage.DiskSession.RawBootstrapMarkerDirectoryStop

open System SyncHandleRouting WalSegmentRepair

private abbrev keeperName := renderWalSegmentName 0
private abbrev markerName := "WAL.commit"
private abbrev scratchName := "WAL.commit.next"

variable {heap : Type} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {fileCalls : BootstrapOpenCalls (Cache CheckpointOpenHandle) directory before}
  {captured : BootstrapCacheOpen fileCalls.toBootstrapAdmissionCalls} {listed : BootstrapCheckedListing captured}
  {view : OpenCloseHeapView heap WalSegmentRotation.State} {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {seed : OpenSyncCacheAllocations captured.opened view init entry} {calls : FreshBootstrapCacheCalls heap}
  {observed : BootstrapReusedZeroKeeper listed} {guards : ReusedBootstrapKeeperGuards observed seed calls}
  {keeper : ReusedBootstrapKeeperHeap guards} {stop : RawBootstrapMarkerDirectoryStop keeper}
  {marker : BootstrapMarkerRenamed listed} {handoff : BootstrapKeeperMarkerRename (.reused observed) marker}

/-- A crash can select the renamed marker before the last directory
fsync takes effect. The selected names and inode payloads come from the
reached rename and file sync. -/
structure BeforeEffectMarkedReboot (physical : stop.Physical handoff) where
  fsync : IO.FS.Handle → EStateM (FilePath × IO.FS.Handle) heap (Except IO.Error Unit)
  stopped : fsync seed.handle stop.afterRename = .error (directory.path, seed.handle) stop.afterRename
  markerChoices : handoff.afterRenameNames markerName =
    (physical.names stop.afterRename).child captured.root markerName :: handoff.afterStageNames markerName
  rebooted : heap
  files : view.files rebooted = stop.visibleMarkerReboot
  emptyCensus : (view.descriptors rebooted).slots = []
  objectMap : (physical.names rebooted).modelObject = (physical.names stop.afterRename).modelObject
  chose : ∀ name, (physical.names rebooted).child captured.root name ∈ handoff.afterRenameNames name
  markerSelected : (physical.names rebooted).child captured.root markerName = some marker.stageChild.child
  scratchMissing : (physical.names rebooted).child captured.root scratchName = none
  payload : ∀ name ∈ [keeperName, markerName], ∀ child, (physical.names rebooted).child captured.root name = some child →
    (keeper.inodes rebooted).visible ((physical.names rebooted).modelObject child) ∈
      (keeper.inodes stop.afterRename).crashBytes ((physical.names stop.afterRename).modelObject child)

namespace BeforeEffectMarkedReboot

variable {physical : stop.Physical handoff} (report : BeforeEffectMarkedReboot physical)

structure Selected : Prop where
  issued : report.fsync seed.handle stop.afterRename = .error (directory.path, seed.handle) stop.afterRename
  pairAllowed : (view.files stop.afterRename).image.metadata.active ∈
    (view.files stop.afterRename).image.metadata.crashImages
  keeperAllowed : (view.files stop.afterRename).image.successor.MaySurvive true
  markerAllowed : some marker.stageChild.child ∈ handoff.afterRenameNames markerName
  scratchAllowed : none ∈ handoff.afterRenameNames scratchName
  marked : MarkedRebootSelection physical report.rebooted

/-- The visible zero marker and earlier durable empty keeper are both
selected from the same issue heap's allowed crash choices. -/
theorem selects (valid : BootstrapValid before.image) : report.Selected := by
  have reached := stop.reachesPhysical physical
  have pairAllowed : (view.files stop.afterRename).image.metadata.active ∈
      (view.files stop.afterRename).image.metadata.crashImages := by
    rw [reached.image]
    exact List.mem_cons_self
  have keeperAllowed : (view.files stop.afterRename).image.successor.MaySurvive true := by
    rw [reached.image]
    rfl
  have markerAllowed : some marker.stageChild.child ∈ handoff.afterRenameNames markerName := by
    rw [report.markerChoices, reached.markerBinding]
    exact List.mem_cons_self
  have sameNames (name : String) : (physical.names report.rebooted).child captured.root name =
      (physical.names stop.afterRename).child captured.root name := by
    by_cases scratch : name = scratchName
    · subst name
      exact report.scratchMissing.trans reached.scratchGone.symm
    by_cases active : name = markerName
    · subst name
      exact report.markerSelected.trans reached.markerBinding.symm
    have chosen := report.chose name
    rw [handoff.renameChoices name scratch active, handoff.stageChoices name scratch, handoff.keeperSettlement] at chosen
    rw [physical.renamedNames, handoff.renameNames name scratch active, handoff.stageNames name scratch]
    exact List.mem_singleton.mp chosen
  have keeperBinding := (sameNames keeperName).trans reached.keeperBinding
  have keeperBytes := report.payload keeperName (by simp) _ keeperBinding
  have markerBytes := report.payload markerName (by simp) _ report.markerSelected
  rw [reached.keeperBytes] at keeperBytes
  rw [reached.markerBytes] at markerBytes
  exact ⟨report.stopped, pairAllowed, keeperAllowed, markerAllowed, report.scratchMissing ▸ report.chose scratchName,
    selectsVisibleMarker physical valid report.files report.emptyCensus report.objectMap sameNames
      (List.mem_singleton.mp keeperBytes) (List.mem_singleton.mp markerBytes)⟩

variable {input : FilePath} {nextView : OpenCloseHeapView heap FileImage}
  {nextCalls : RawOpenAdmissionCallbacks heap} {nextInit : OpenSyncCacheCallbacks heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)} {stream : Type}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)} {stage : LongKeeperStageCallbacks heap}
  {rename : FilePath → FilePath → EStateM IO.Error heap Unit}

/-- The marked opener reads the selected zero marker and existing keeper
from this before-effect reboot, then returns its exact empty table. -/
theorem opensEmptyTable (valid : BootstrapValid before.image)
    (opening : MarkedRebootSelection.OpenObservation (input := input) (report.selects valid).marked)
    (same : (report.selects valid).marked.SameReboot opening)
    (raw : RawHealthyMarkedOpenEffects opening nextView nextCalls nextInit report.rebooted
      phaseIdentity tokenIdentity allocatePhase allocateToken stream remove stage rename)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
      IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (constructs : ∀ resolved lock cache, DiskTable.OpenReferenceAssembly resolved lock cache (assemble resolved lock cache))
    (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
    (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit)
    (phaseEffects : OpenPhaseCellEffects nextView.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) :
    report.Selected ∧ Nonempty ((report.selects valid).marked.Returned opening raw bootstrap assemble get set ptrEq) :=
  ⟨report.selects valid, (report.selects valid).marked.opensEmptyTable opening same raw bootstrap assemble
    constructs get set phaseEffects ptrEq⟩

end BeforeEffectMarkedReboot
end Alvoki.Storage.DiskSession.RawBootstrapMarkerDirectoryStop
