import Alvoki.Storage.Disk.CachedWalChunkReports

namespace Alvoki.Storage.WalSegmentRepair

open System DiskSession SyncHandleRouting

/-- The directory barrier after an aligned keeper read uses the directory
description already in the cache. Its observed live slot and inode binding
identify the directory whose names settle. The syscall report distinguishes
an error before settlement from one after settlement. The keeper entry stays
pending in either case. -/
theorem readWalKeeperWithChunks_syncCapturedDirectory
    {reads : CheckpointRunChunkReads} (directory : DiskDirectory) (keeper : Nat)
    {selectedBytes tail : ByteArray}
    (seen : reads.ObservesFile (directory.file (.walSegment keeper)) (selectedBytes ++ tail))
    (fits : selectedBytes.size < USize.size) (aligned : selectedBytes.size = seen.metadata.byteSize.toNat)
    (cache : Cache (DescriptorInventory × DescriptorSlot × Nat))
    (inventory : DescriptorInventory) (slot : DescriptorSlot) (offset : Nat)
    (hasDirectory : cache.directory = some (inventory, slot, offset)) (drops : List LockReferenceDrop)
    (issuing : slot.reference ∈ (inventory.afterDrops drops).references slot.description)
    (bindings : FilePath → Option Nat) (boundAtSync : bindings directory.path = some (inventory.inode slot.description))
    (outcome : DelayedDirectorySyncOutcome) (initial : LockedFileState FileImage)
    (openRead : FilePath → EStateM IO.Error (LockedFileState FileImage) (DescriptorInventory × DescriptorSlot × Nat))
    (fsync : (DescriptorInventory × DescriptorSlot × Nat) → EStateM IO.Error (LockedFileState FileImage) Unit) :
    let path := directory.file (.walSegment keeper)
    let remembered := cache.remember path (seen.inventory, seen.slot, 0)
    let report := inventory.delayedDirectorySync drops directory slot.description slot.reference issuing
      bindings boundAtSync outcome
    fsync (inventory, slot, offset) initial = report.run initial →
    readWalKeeperWithChunks reads path selectedBytes.size seen.metadata.byteSize.toNat (cache, initial) =
        .ok selectedBytes (remembered, initial) ∧
      sync directory.path openRead fsync directory.path (remembered, initial) =
        withCache remembered (report.run initial) ∧
      SyncPathGroup.run (sync directory.path openRead fsync) #[directory.path] (remembered, initial) =
        SyncPathGroup.run (m := EStateM IO.Error (Cache _ × LockedFileState FileImage))
          (fun _ (current, before) => withCache current (report.run before))
          #[directory.path] (remembered, initial) := by
  intro path remembered report effect
  have routed : sync directory.path openRead fsync directory.path (remembered, initial) =
      withCache remembered (report.run initial) := by
    simp [sync, Cache.resolve, remembered, Cache.remember, hasDirectory, effect]
  refine ⟨?_, routed, ?_⟩
  · simpa [remembered, Cache.captureKeeper, aligned] using readWalKeeperWithChunks_exact seen fits cache initial
  · rw [SyncPathGroup.run_single, routed]
    let reportSync (_ : FilePath) :
        EStateM IO.Error (Cache (DescriptorInventory × DescriptorSlot × Nat) × LockedFileState FileImage) Unit :=
      fun (current, before) => withCache current (report.run before)
    exact (SyncPathGroup.run_single reportSync directory.path (remembered, initial)).symm

/-- A successful aligned keeper read records its exact open description.
The directory barrier leaves that cache entry untouched. The keeper barrier
uses the entry, consumes it on every result, and acts on the observed inode.
Slot survival, the effect-time binding, and both syscall effects come from
the native report. -/
theorem readWalKeeperWithChunks_syncAligned
    {state : Type} {reads : CheckpointRunChunkReads} {dir path : FilePath}
    {selectedBytes tail : ByteArray} (seen : reads.ObservesFile path (selectedBytes ++ tail))
    (fits : selectedBytes.size < USize.size) (aligned : selectedBytes.size = seen.metadata.byteSize.toNat)
    (separate : path ≠ dir) (cache : Cache (DescriptorInventory × DescriptorSlot × Nat))
    {directoryHandle : DescriptorInventory × DescriptorSlot × Nat}
    (hasDirectory : cache.directory = some directoryHandle)
    (openRead : FilePath → EStateM IO.Error state (DescriptorInventory × DescriptorSlot × Nat))
    (fsync : (DescriptorInventory × DescriptorSlot × Nat) → EStateM IO.Error state Unit)
    {initial authorized : state} (directoryEffect : fsync directoryHandle initial = .ok () authorized)
    (drops : List LockReferenceDrop)
    (issuing : seen.slot.reference ∈ (seen.inventory.afterDrops drops).references seen.slot.description)
    (bindings : FilePath → Option Nat) (boundAtSync : bindings path = some seen.object)
    (persist : Nat → state → state) {effective : Bool}
    (effect : FsyncResult authorized (persist seen.object authorized) effective
      (fsync (seen.inventory, seen.slot, 0) authorized)) :
    let captured := (seen.inventory, seen.slot, 0)
    let remembered := cache.remember path captured
    readWalKeeperWithChunks reads path selectedBytes.size seen.metadata.byteSize.toNat (cache, initial) =
        .ok selectedBytes (remembered, initial) ∧
      sync dir openRead fsync dir (remembered, initial) = .ok () (remembered, authorized) ∧
      sync dir openRead fsync path (remembered, authorized) =
        withCache (cache.consume path) (fsync captured authorized) ∧
      ∃ observed : FsyncObservation (fun handle => handle.2.1.description)
          (fun handle => handle.1.inode handle.2.1.description) captured authorized persist (fsync captured authorized),
        observed.issuer = seen.slot.reference ∧ observed.effective = effective ∧
        bindings path = some observed.effectInode := by
  intro captured remembered
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [remembered, captured, Cache.captureKeeper, aligned] using
      readWalKeeperWithChunks_exact seen fits cache initial
  · simp [sync, Cache.resolve, remembered, Cache.remember, hasDirectory, directoryEffect, withCache]
  · rw [show remembered = cache.remember path captured from rfl,
      syncRemembered separate captured openRead fsync authorized]
    cases fsync captured authorized <;> rfl
  · have observedEffect : FsyncResult authorized (persist (seen.inventory.inode seen.slot.description) authorized)
        effective (fsync captured authorized) := by
      rw [seen.sameObject]
      exact effect
    let observed := FsyncObservation.ofInventory seen.inventory drops
      (fun handle => handle.2.1.description) (fun handle => handle.1.inode handle.2.1.description)
      captured seen.slot.reference issuing rfl authorized persist observedEffect
    refine ⟨observed, rfl, rfl, ?_⟩
    change bindings path = some (seen.inventory.inode seen.slot.description)
    simpa only [seen.sameObject] using boundAtSync

end Alvoki.Storage.WalSegmentRepair
