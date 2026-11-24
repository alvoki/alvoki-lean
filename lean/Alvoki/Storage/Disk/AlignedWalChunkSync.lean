import Alvoki.Storage.Disk.CachedWalChunkReports

namespace Alvoki.Storage.WalSegmentRepair

open System DiskSession SyncHandleRouting

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
