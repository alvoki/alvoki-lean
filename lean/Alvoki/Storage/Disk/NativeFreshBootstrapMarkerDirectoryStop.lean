import Alvoki.Storage.Disk.NativeBootstrapMarkerDirectoryStop

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

variable {heap : Type} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {fileCalls : BootstrapOpenCalls (Cache CheckpointOpenHandle) directory before}
  {captured : BootstrapCacheOpen fileCalls.toBootstrapAdmissionCalls} {listed : BootstrapCheckedListing captured}
  {view : OpenCloseHeapView heap WalSegmentRotation.State} {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {seed : OpenSyncCacheAllocations captured.opened view init entry} {calls : FreshBootstrapCacheCalls heap}

/-- The missing keeper branch returns from exclusive create and both
keeper syncs, then stops on the original cached directory handle after
the marker stage, file sync and rename have returned. -/
theorem FreshBootstrapKeeperChronology.stopsHeldAtMarkerDirectory
    (fresh : FreshBootstrapKeeperChronology seed calls)
    (stop : BootstrapMarkerDirectoryStopPrefix seed calls fresh.keeperDirectory.reached) :
    (calls.untilMarkerDirectory directory seed.directoryRef seed.activeRef seed.pendingRef).run seed.afterPending =
      .error (directory.path, seed.handle) stop.afterRename :=
  stop.stopsHeld fresh.prepares fresh.rotates

variable {input : FilePath} {inventory : DescriptorInventory}
  {admission : CensusOpenAdmissionReports input directory inventory before}
  {raw : RawOpenAdmissionCallbacks heap}

/-- The actual initial open creates the keeper, settles its empty bytes,
and reaches the first marker's cached directory fsync without an ordinary
return. The physical keeper observations end at the keeper barrier.
The marker's reached crash bindings require their own reports. -/
theorem FreshBootstrapKeeperChronology.stopsPublicAtMarkerDirectory
    (admitted : RawOpenAdmissionReport admission view raw entry)
    {heldSeed : OpenSyncCacheAllocations captured.opened view init admitted.afterFlock}
    (fresh : FreshBootstrapKeeperChronology heldSeed calls)
    (observed : BootstrapFreshZeroKeeper listed)
    (physical : FreshBootstrapKeeperPhysical observed fresh.keeper fresh.keeperDirectory)
    (stop : BootstrapMarkerDirectoryStopPrefix heldSeed calls fresh.keeperDirectory.reached)
    (owner : admission.owner = fileCalls.slot)
    (listing : fresh.entries = listed.scan.scan.entries directory.path)
    (metadata : ∀ path, calls.metadata path = optionalMetadataWith (raw.lookup path))
    (keeperLookup : calls.readEmpty (directory.file (.walSegment 0)) =
      WalSegmentRotation.readEmptyWith (raw.lookup (directory.file (.walSegment 0)))
        (directory.file (.walSegment 0)) WAL.Boundary.missingOpenMarker)
    (flat : calls.metadata (directory.file .wal) heldSeed.afterPending = .ok none heldSeed.afterPending)
    (absent : calls.metadata (directory.file .walBoundary) heldSeed.afterPending = .ok none heldSeed.afterPending)
    (marked : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap DiskTable) :
    let keeperHeap := fresh.keeperDirectory.reached
    view.handle admitted.afterFlock admitted.lock = (captured.initial, fileCalls.slot, 0) ∧
    calls.list directory.path heldSeed.afterPending = .ok (listed.scan.scan.entries directory.path) fresh.afterList ∧
    WalSegmentRotation.readEmptyWith (raw.lookup (directory.file (.walSegment 0)))
      (directory.file (.walSegment 0)) WAL.Boundary.missingOpenMarker fresh.afterList = .ok none fresh.afterEmpty ∧
    calls.create (directory.file (.walSegment 0)) fresh.prepared = .ok fresh.keeper.handle fresh.keeper.produced ∧
    view.handle fresh.keeper.consumed fresh.keeper.handle =
      ((listed.scan.afterClose.afterDrops observed.beforeCreate).insert observed.slot observed.free, observed.slot, 0) ∧
    observed.namespaceView.child captured.root (renderWalSegmentName 0) = some observed.child.child ∧
    observed.opened.active = (view.descriptors fresh.keeper.consumed).inode observed.slot.description ∧
    (view.files keeperHeap).image = ⟨before.image.metadata.syncDirectory, .durable⟩ ∧
    (physical.inodes keeperHeap).crashBindings = [observed.opened.active] ∧
    (physical.inodes keeperHeap).crashBytes observed.opened.active = [ByteArray.empty] ∧
    fileCalls.slot ∈ (view.descriptors keeperHeap).slots ∧
    view.handle stop.afterRename heldSeed.handle = (view.descriptors stop.afterRename, captured.cached, 0) ∧
    captured.cached ∈ (view.descriptors stop.afterRename).slots ∧
    captured.view.modelObject captured.root = (view.descriptors stop.afterRename).inode captured.cached.description ∧
    ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles) (cache : DiskTable.OpenSyncFiles),
      DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      openSyncFilesWith (init.openDirectory directory.path) init.newRef init.newRef init.newRef makeCache
        admitted.afterFlock = .ok cache heldSeed.afterPending ∧
      cache.UsesBootstrapCacheSchedules directory heldSeed.activeRef heldSeed.pendingRef heldSeed.directoryRef ∧
      raw.runUntilBootstrapDirectory input init makeCache
        (fun resolved _ => calls.untilMarkerDirectory resolved heldSeed.directoryRef heldSeed.activeRef heldSeed.pendingRef)
        marked install entry = .error (directory.path, heldSeed.handle) stop.afterRename := by
  intro keeperHeap
  obtain ⟨handle, _, files, _, child, object, _, binding, bytes, ownerLive, _⟩ := physical.settles fresh.keeperOK
  obtain ⟨cacheOpen, makeCache, cache, action, source, initialized, references, path, _⟩ := heldSeed.installs
  have root := captured.captures.2.2.2.2.trans stop.sameInode.symm
  have empty := fresh.empty
  rw [keeperLookup] at empty
  have rawListing := fresh.checked
  rw [listing] at rawListing
  have initial := (admitted.lockedCensus.trans admitted.appendCensus).symm.trans heldSeed.entrySlots
  have rawLock : view.handle admitted.afterFlock admitted.lock = (captured.initial, fileCalls.slot, 0) := by
    rw [admitted.sameLock.trans admitted.appendHandle, initial, owner]
  have ran := admitted.stopsBootstrapDirectory heldSeed initialized metadata flat absent
    (fresh.stopsHeldAtMarkerDirectory stop) marked install
  exact ⟨rawLock, rawListing, empty, fresh.keeper.returnedHandle, handle, child, observed.active.trans object, files,
    binding, bytes, ownerLive,
    stop.rawHandle, stop.live, root, cacheOpen, makeCache, cache, action, source, initialized,
    cache.bootstrapCacheSchedules references path, ran⟩

end Alvoki.Storage.DiskSession
