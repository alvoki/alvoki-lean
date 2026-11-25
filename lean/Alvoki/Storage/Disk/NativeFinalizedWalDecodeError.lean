import Alvoki.Storage.Disk.NativeRawAlignedWalDecodeError

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair SyncHandleRouting

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
  {admission : CensusOpenAdmissionReports input directory (view.descriptors entry) (view.files entry)}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {fileCalls : MarkedTemporaryReadCalls heap} {directoryCalls : MarkedDirectoryReadCalls heap stream}
  {callbacks : AlignedKeeperCacheCallbacks heap} {slotOf : heap → stream → DescriptorSlot}
  {durable : CheckpointPublication.RunFiles} {checkpoint : Option (PackedTable × UInt64)}
  {selected : RawPresentManifestCheckpointPrefix (admitted := admitted) seed fileCalls durable checkpoint}
  {marker : RawPresentManifestMarkerPrefix selected}

/-- The populated cache drops the remembered keeper handle first.
The checked raw open and remember report fixes that exact live slot. -/
structure RawAlignedWalPendingDrop (seen : RawAlignedWalDecodeRead marker directoryCalls slotOf callbacks) where
  reached : heap
  released : dataErrorDropState fileCalls.release seen.handle seen.remembered = reached
  census : view.descriptors reached = (view.descriptors seen.remembered).afterDrops [seen.keeper.calls.slot.closeEvent]
  files : view.files reached = view.files seen.remembered

namespace RawAlignedWalPendingDrop

variable {seen : RawAlignedWalDecodeRead marker directoryCalls slotOf callbacks}
variable (drop : RawAlignedWalPendingDrop seen)

/-- At the rejected worker's scope exit, account for the effect of
destroying the pending handle, retaining the original diagnostic. -/
def errorScope {α : Type} (_drop : RawAlignedWalPendingDrop seen)
    (worker : EStateM IO.Error heap α) : EStateM IO.Error heap α := fun before =>
  match worker before with
  | .ok value reached => .ok value reached
  | .error cause reached => .error cause (dataErrorDropState fileCalls.release seen.handle reached)

/-- The handle being released is the remembered selected descriptor.
Dropping that slot leaves the original held image and inode map. -/
theorem retiresKeeper :
    view.pending seen.remembered seed.pendingRef = [(directory.file (.walSegment seen.first), seen.handle)] ∧
    (view.handle seen.remembered seen.handle).2.1 = seen.keeper.calls.slot ∧
    seen.keeper.calls.slot ∈ (view.descriptors seen.remembered).slots ∧
    (view.descriptors drop.reached).references seen.keeper.calls.slot.description = [] ∧
    (view.descriptors drop.reached).inode = (view.descriptors entry).inode ∧
    view.files drop.reached = admission.held := by
  have removed : (view.descriptors drop.reached) =
      (view.descriptors seen.afterListing).afterDrops [seen.keeper.calls.slot.closeEvent] := by
    rw [drop.census, seen.rememberedCensus, seen.readCensus, seen.openedCensus, seen.inserted]
    simpa only [List.nil_append] using DescriptorInventory.insert_thenClose _ _ seen.slotFree []
  have fresh : (view.descriptors drop.reached).references seen.keeper.calls.slot.description = [] := by
    rw [removed, DescriptorInventory.references_afterDrops, seen.fresh]
    rfl
  have inodes : (view.descriptors drop.reached).inode = (view.descriptors entry).inode := by
    rw [removed, seen.returnsListing.2, seen.listing.afterClose_eq]
    exact marker.reachesScan.2.2.2
  exact ⟨seen.pending, seen.rememberedSlot, seen.remembersSelected.2.2.1, fresh, inodes,
    drop.files.trans seen.remembersSelected.2.2.2.2⟩

/-- The raw decoder error now enters the existing directory drop,
unlock and final lock close at the heap after the keeper drop. -/
noncomputable def finalizedAttempt (cause : String)
    (corrupt : WAL.decodeOrdinalsFrom (seen.first + 1) seen.bytes = .error cause)
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed drop.reached)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit) (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap DiskTable)
    {release : IO.FS.Handle → heap → heap}
    (finalized : RawOpenErrorLockFinalization view directory release admitted.lock admission.owner disposal.reached) :
    RawFinalizedOpenAttempt view directory calls init release input entry where
  admission := admission
  admitted := admitted
  seed := seed
  beforeCleanup := drop.reached
  disposed := disposal
  recover := fun resolved lock cache =>
    drop.errorScope (calls.recoverMarkedWithCacheRefs fileCalls directoryCalls callbacks seed.directoryRef seed.activeRef
      seed.pendingRef remove write rename bootstrap resolved cache) >>= install resolved lock cache
  cause := IO.userError cause
  rejected := by
    apply disposal.returns _ _ _ drop.retiresKeeper.2.2.2.2.2
    intro cache
    simp only [Bind.bind, EStateM.bind, errorScope, seen.stopsMarkedWorker corrupt remove write rename bootstrap,
      drop.released]
  workerInodes := drop.retiresKeeper.2.2.2.2.1
  finalized := finalized

/-- The final descriptor inventory reports the original keeper first,
the cached directory second, and the acquired lock last. -/
theorem finalizedCensus (disposal : RawOpenCacheDisposal (admitted := admitted) seed drop.reached)
    {release : IO.FS.Handle → heap → heap}
    (finalized : RawOpenErrorLockFinalization view directory release admitted.lock admission.owner disposal.reached) :
    view.descriptors finalized.reached = ((view.descriptors seen.remembered).afterDrops
      [seen.keeper.calls.slot.closeEvent, admission.cached.closeEvent]).afterDrops [admission.owner.closeEvent] := by
  simp only [finalized.census, disposal.returnedCensus, disposal.census, drop.census,
    DescriptorInventory.afterDrops_append, List.cons_append, List.nil_append]

end RawAlignedWalPendingDrop

end Alvoki.Storage.DiskSession
