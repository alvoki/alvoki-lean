import Alvoki.Storage.Disk.BootstrapClientTrace
import Alvoki.Storage.Disk.BootstrapKeeperMarkerHandoff

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

namespace BootstrapKeeperMarkerHandoff

private abbrev Handle := DescriptorInventory × DescriptorSlot × Nat

variable {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {calls : BootstrapOpenCalls (Cache Handle) directory before}
  {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls}
  {listed : BootstrapCheckedListing captured} {keeper : BootstrapZeroKeeperRoute listed}
  {marker : BootstrapMarkerCustody listed}

/-- The reported bootstrap from an empty managed image is the first
client session. Both the initial invariant and the ready installed writer
follow from the empty image and reached keeper and marker operations. -/
theorem startFromEmpty {input : FilePath} (observed : BootstrapKeeperMarkerHandoff keeper marker)
    (admission : OpenAdmissionReports input directory calls.slot)
    (empty : before.image = ⟨DirectoryPublication.Image.settled ⟨none, none⟩, .absent⟩) :
    ∃ start : BootstrapClientStart directory calls.slot.description (calls.run admission),
      start.final.image = marker.publishedState ∧ start.writer.history = [] ∧
      observed.afterMarkerNames (renderWalSegmentName 0) = [some keeper.keeperChild] ∧
      observed.afterMarkerNames "WAL.commit" = [some marker.stageChild.child] ∧
      ((marker.inodeState.completeFileSync marker.inodeState.active).settleBinding).crashBytes
        keeper.settledImage.active = [ByteArray.empty] ∧
      ((marker.inodeState.completeFileSync marker.inodeState.active).settleBinding).crashBytes
        marker.inodeState.active = [WAL.Boundary.encode 0] := by
  have valid : BootstrapValid before.image := empty.symm ▸ bootstrap_fresh
  obtain ⟨keeperName, markerName, keeperBytes, markerBytes, after, bootstrap, returned, image, ready, _⟩ :=
    observed.installs admission valid false
  exact ⟨⟨_, after, bootstrap, returned, rfl, rfl, rfl, ready.held⟩, image, rfl,
    keeperName, markerName, keeperBytes, markerBytes⟩

end BootstrapKeeperMarkerHandoff
end Alvoki.Storage.DiskSession
