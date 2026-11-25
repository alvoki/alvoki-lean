import Alvoki.Storage.Disk.NativeHealthyMarkedTableOpen

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {published : CheckpointPublication.Image} {vacant : TryLockObserves retry.owners directory (.ok true)}
  {checkpoint : Option (PackedTable × UInt64)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
  {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)} {stage : LongKeeperStageCallbacks heap}
  {rename : FilePath → FilePath → EStateM IO.Error heap Unit} {stream : Type}

/-- The raw file callbacks and reference allocations keep the same
selected checkpoint and WAL reader through a healthy marked open. -/
structure RawHealthyMarkedOpenEffects
    (opening : MarkedReadyOpenObservations input directory inventory retry layout published vacant selected)
    (view : OpenCloseHeapView heap FileImage) (calls : RawOpenAdmissionCallbacks heap)
    (init : OpenSyncCacheCallbacks heap) (rebooted : heap)
    (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat)
    (allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed)))
    (allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)) (stream : Type)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)) (stage : LongKeeperStageCallbacks heap)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) where
  raw : RawOpenAdmissionReport opening.admission view calls rebooted
  seed : OpenSyncCacheAllocations opening.admission.opened view init raw.afterFlock
  fileCalls : MarkedTemporaryReadCalls heap
  directoryCalls : MarkedDirectoryReadCalls heap stream
  slotOf : heap → stream → DescriptorSlot
  callbacks : AlignedKeeperCacheCallbacks heap
  checkpoint : NativeMarkedCheckpointReadHeap seed opening.chronology fileCalls
  listing : MarkedDirectoryReadReport checkpoint directoryCalls slotOf
  extents : MarkedWalExtentReports checkpoint listing
  beforeKeeper : heap
  repaired : heap
  seals : MarkedSealReadChain seed fileCalls opening.chronology.seals listing.reached beforeKeeper
  keeper : NativeHealthyMarkedKeeperReport seed fileCalls callbacks beforeKeeper remove stage rename opening.finish repaired
  sameLookup : fileCalls.stat = calls.lookup
  flat : optionalMetadataWith (fileCalls.stat (directory.file .wal)) seed.afterPending = .ok none seed.afterPending
  marked : optionalMetadataWith (fileCalls.stat (directory.file .walBoundary)) seed.afterPending =
    .ok (some opening.marker) seed.afterPending
  allocations : ∀ opened,
    opening.finish.markedWorker opening.chronology directory opening.admission.cache
      (opening.admission.reached, opening.admission.held) =
      .ok opened (view.descriptors repaired, view.files repaired) →
    ∃ allocation : OpenReferenceAllocations allocatePhase allocateToken view.phase opened.installed repaired,
      phaseIdentity allocation.phase = opening.callbacks.nextRef ∧
      tokenIdentity allocation.token = opening.callbacks.nextRef + 1 ∧
      CacheAllocationFrame view seed.directoryRef seed.activeRef seed.pendingRef repaired allocation.afterPhase ∧
      CacheAllocationFrame view seed.directoryRef seed.activeRef seed.pendingRef allocation.afterPhase allocation.afterToken

variable {opening : MarkedReadyOpenObservations input directory inventory retry layout published vacant selected}

noncomputable def RawHealthyMarkedOpenEffects.openTable
    (seen : RawHealthyMarkedOpenEffects opening view calls init entry phaseIdentity tokenIdentity
      allocatePhase allocateToken stream remove stage rename)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles) : EStateM.Result IO.Error heap DiskTable :=
  calls.runOpen input init makeCache (fun resolved lock cache => do
    let opened ← recoverHealthyMarkedWithRefs seen.fileCalls seen.directoryCalls seen.callbacks seen.seed.directoryRef
      seen.seed.activeRef seen.seed.pendingRef remove stage rename calls.lookup resolved (bootstrap resolved cache)
    installReady opened.installed allocatePhase allocateToken (fun phase token => pure (assemble resolved lock cache phase token))) entry

end Alvoki.Storage.DiskSession
