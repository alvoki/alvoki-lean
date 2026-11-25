import Alvoki.Storage.Disk.BootstrapMarkerDetachError
import Alvoki.Storage.Disk.BootstrapMarkerFlushError

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

private abbrev Handle := DescriptorInventory × DescriptorSlot × Nat
private abbrev keeperName := renderWalSegmentName 0
private abbrev stageName := "WAL.commit.next"
private abbrev markerName := "WAL.commit"

variable {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {calls : BootstrapOpenCalls (Cache Handle) directory before}
  {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls}
  {listed : BootstrapCheckedListing captured} {keeper : BootstrapZeroKeeperRoute listed}

/-- One observed restart after a failed marker flush and its finalizer.
The restart namespace and inode image select the name and byte survivors
together. This route follows the newly created scratch inode when it survives. -/
structure BootstrapMarkerFlushSurvivor (source : BootstrapMarkerFlushError keeper) where
  view : DirectoryReadNamespace
  inodes : WalInodeImage
  sameObjects : view.modelObject = source.reachedView.modelObject
  names : ∀ name, view.child captured.root name ∈ source.crashNames name
  scratch : view.child captured.root stageName = some source.child.child
  keeperObject : inodes.active = view.modelObject keeper.keeperChild
  payload : ∀ name ∈ [keeperName, stageName], ∀ child, view.child captured.root name = some child →
    inodes.visible (view.modelObject child) ∈ source.reachedInodes.crashBytes (source.reachedView.modelObject child)

namespace BootstrapMarkerFlushSurvivor

variable {source : BootstrapMarkerFlushError keeper}

def scratchBytes (observed : BootstrapMarkerFlushSurvivor source) : ByteArray :=
  observed.inodes.visible (observed.view.modelObject source.child.child)

/-- The canonical pair and keeper use the ordinary restart projection.
The surviving scratch bytes are stale and carry no staging-sync witness
for the new worker. -/
def state (observed : BootstrapMarkerFlushSurvivor source) : LockedFileState WalSegmentRotation.State :=
  let crashed := bootstrapPowerLoss directory source.final before.image.metadata.active true
  { crashed with image := { crashed.image with metadata := { crashed.image.metadata with
      staged := fun
        | .manifest => none
        | .walBoundary => some (observed.scratchBytes, false) } } }

/-- The observed joint restart keeps the same empty keeper, keeps the
canonical marker absent, and selects bytes from the issued scratch inode. -/
theorem physical (observed : BootstrapMarkerFlushSurvivor source) :
    observed.view.child captured.root markerName = none ∧
    observed.view.child captured.root keeperName = some keeper.keeperChild ∧
    observed.inodes.visible observed.inodes.active = ByteArray.empty ∧
    some source.child.child ∈ source.crashNames stageName ∧
    observed.scratchBytes ∈ source.reachedInodes.crashBytes source.reachedInodes.active ∧
    observed.view.modelObject source.child.child ≠ observed.inodes.active := by
  have marker := observed.names markerName
  have zero := observed.names keeperName
  have markerCrash : source.crashNames markerName = [none] :=
    (source.offTargetCrashNames markerName (by decide)).trans
      (congrArg (fun name => [name]) source.canonicalAbsent)
  have held := keeper.settledCustody
  have zeroCrash : source.crashNames keeperName = [some keeper.keeperChild] :=
    (source.offTargetCrashNames keeperName (by decide)).trans (congrArg (fun name => [name]) held.2.2.1)
  rw [markerCrash] at marker
  rw [zeroCrash] at zero
  have zeroBinding := List.mem_singleton.mp zero
  have empty := observed.payload keeperName (by simp) keeper.keeperChild zeroBinding
  have sameKeeper : source.reachedView.modelObject keeper.keeperChild = keeper.settledImage.active := by
    rw [source.sameObjects, held.2.2.2]
  have distinct : source.reachedView.modelObject keeper.keeperChild ≠ source.reachedInodes.active := by
    simpa only [source.sameObjects] using source.keeperSeparate
  have retained := (source.offTargetBytes _ distinct).2
  have settledBytes : keeper.settledImage.crashBytes keeper.settledImage.active = [ByteArray.empty] :=
    keeper.settledEmpty.2
  rw [sameKeeper, settledBytes] at retained
  rw [sameKeeper, retained, ← observed.keeperObject] at empty
  have scratch := observed.payload stageName (by simp) source.child.child observed.scratch
  rw [← source.reachedMarkerInode] at scratch
  have scratchName : some source.child.child ∈ source.crashNames stageName := observed.scratch ▸ observed.names stageName
  refine ⟨List.mem_singleton.mp marker, zeroBinding, List.mem_singleton.mp empty, scratchName, scratch, ?_⟩
  rw [observed.keeperObject, observed.sameObjects, ← source.reachedMarkerInode]
  exact distinct.symm

/-- The exact admitted flush error is followed by the canonical crash
choice. Keeping the reported stale file does not alter bootstrap validity. -/
theorem afterError {input : FilePath} (observed : BootstrapMarkerFlushSurvivor source)
    (admission : OpenAdmissionReports input directory calls.slot) (valid : BootstrapValid before.image)
    (localUnlock : calls.unlock.LocalFlock) :
    calls.run admission = .error source.returnedError source.final ∧
    BootstrapValid observed.state.image ∧
    observed.state.image.metadata.active.walBoundary = none ∧
    observed.state.image.successor = .durable ∧
    observed.state.image.metadata.staged .walBoundary = some (observed.scratchBytes, false) ∧
    observed.state.owners (directory.file .lock) = none := by
  obtain ⟨returned, reached, missing, choices, durable, _⟩ := source.returns admission valid localUnlock
  have selected : before.image.metadata.active ∈ source.final.image.metadata.crashImages := by
    rw [choices]
    exact List.mem_singleton_self _
  have restarted := reached.crash selected (survives := true) (by rw [durable]; rfl)
  refine ⟨returned, ⟨⟨restarted.metadata.activeMaySurvive, restarted.metadata.crashValid⟩, restarted.marked⟩,
    ?_, rfl, rfl, ?_⟩
  · exact calls.markerAbsent.1
  · simp [state, bootstrapPowerLoss, LockOwners.set]

/-- The next markerless call reuses the surviving keeper. Its stale
staging probe refers to the reported scratch survivor on that same root.
The checked detach failure returns from the production stage without
opening a replacement and carries its exact cleanup and reached files. -/
theorem retriesDetach {input nextInput : FilePath} (observed : BootstrapMarkerFlushSurvivor source)
    (admission : OpenAdmissionReports input directory calls.slot) (valid : BootstrapValid before.image)
    (localUnlock : calls.unlock.LocalFlock)
    {nextCalls : BootstrapOpenCalls (Cache Handle) directory observed.state}
    {nextCapture : BootstrapCacheOpen nextCalls.toBootstrapAdmissionCalls}
    {nextListing : BootstrapCheckedListing nextCapture} {nextKeeper : BootstrapZeroKeeperRoute nextListing}
    (sameRoot : nextCapture.root = captured.root) (sameView : nextCapture.view = observed.view)
    (sameInodes : nextKeeper.keeperImage = observed.inodes)
    (detach : BootstrapMarkerDetachError nextKeeper)
    (nextAdmission : OpenAdmissionReports nextInput directory nextCalls.slot)
    (nextUnlock : nextCalls.unlock.LocalFlock) :
    calls.run admission = .error source.returnedError source.final ∧
    detach.stale.child = source.child.child ∧
    nextKeeper.keeperChild = keeper.keeperChild ∧
    nextKeeper.settledImage.visible (nextKeeper.keeperView.modelObject detach.stale.child) = observed.scratchBytes ∧
    detach.view.child nextCapture.root stageName = (if detach.detached then none else some source.child.child) ∧
    (detach.view.child nextCapture.root stageName).map (fun child => detach.reached.2.visible
      (detach.view.modelObject child)) = (if detach.detached then none else some observed.scratchBytes) ∧
    nextCalls.run nextAdmission = .error detach.returnedError detach.final ∧
    BootstrapValid detach.final.image ∧
    detach.final.image.metadata.active.walBoundary = none ∧
    detach.final.image.metadata.staged .walBoundary =
      (if detach.detached then none else some (observed.scratchBytes, false)) := by
  obtain ⟨returned, after, _, _, scratch, _⟩ := observed.afterError admission valid localUnlock
  obtain ⟨_, zero, _, _, _, _⟩ := observed.physical
  have reused : nextKeeper.keeperView = nextCapture.view := by
    cases nextKeeper with
    | fresh report =>
      have missing := report.absentSegment
      change WalSegmentRotation.Binding.durable = .absent at missing
      contradiction
    | reused _ => rfl
  have existing : nextKeeper.keeperView.child nextCapture.root stageName = some source.child.child := by
    rw [reused, sameView, sameRoot, observed.scratch]
  have stale := detach.stale.child_eq existing
  have exactKeeper : nextKeeper.keeperChild = keeper.keeperChild := by
    have same := nextKeeper.settledCustody.2.2.1
    rw [reused, sameView, sameRoot, zero] at same
    exact (Option.some.inj same).symm
  have payload : nextKeeper.settledImage.visible (nextKeeper.keeperView.modelObject detach.stale.child) =
      observed.scratchBytes := by
    change nextKeeper.keeperImage.visible (nextKeeper.keeperView.modelObject detach.stale.child) = _
    rw [sameInodes, stale, reused, sameView]
    rfl
  obtain ⟨failed, nextValid, markerAbsent, stage⟩ := detach.returns nextAdmission after nextUnlock
  obtain ⟨nameAfter, bytesAfter, _⟩ := detach.physicalScratch
  exact ⟨returned, stale, exactKeeper, payload, stale ▸ nameAfter, by simpa only [payload] using bytesAfter,
    failed, nextValid, markerAbsent, by simpa only [scratch] using stage⟩

end BootstrapMarkerFlushSurvivor
end Alvoki.Storage.DiskSession
