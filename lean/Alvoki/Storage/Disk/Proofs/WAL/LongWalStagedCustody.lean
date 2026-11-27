import Alvoki.Storage.Disk.Proofs.Recovery.CachedWalChunkReports
import Alvoki.Storage.Disk.Proofs.Filesystem.StagedHandleCustody

namespace Alvoki.Storage.WalSegmentRepair

open System DiskSession SyncHandleRouting
open WAL.Boundary (WalInodeImage)

/-- For a longer keeper, the checked prefix leaves the read cache unchanged.
At the reached replacement steps, the shared cache passes the description
returned by staging that prefix to the staged-file barrier. A complete
effect persists precisely that inode's checked bytes, even if fsync then
reports an error. The stage report and live effect-time binding are primitive
observations. The preceding prune and following rename are separate steps. -/
theorem readWalKeeperWithChunks_syncStaged
    {reads : CheckpointRunChunkReads} (directory : DiskDirectory) (plan : Plan) {tail : ByteArray}
    (seen : reads.ObservesFile (directory.file (.walSegment plan.keeper)) (plan.keeperBytes ++ tail))
    (bytes : plan.keeperBytes.size = plan.keeperSize) (fits : plan.keeperBytes.size < USize.size)
    (long : plan.keeperBytes.size < seen.metadata.byteSize.toNat)
    (separate : directory.file .stagedWal ≠ directory.path)
    (cache : Cache (DescriptorInventory × DescriptorSlot × Nat))
    (stage : FilePath → ByteArray → EStateM IO.Error WalInodeImage (DescriptorInventory × DescriptorSlot × Nat))
    (openRead : FilePath → EStateM IO.Error WalInodeImage (DescriptorInventory × DescriptorSlot × Nat))
    (fsync : (DescriptorInventory × DescriptorSlot × Nat) → EStateM IO.Error WalInodeImage Unit)
    (remove : FilePath → EStateM IO.Error (Cache (DescriptorInventory × DescriptorSlot × Nat) × WalInodeImage)
      (Except IO.Error Unit))
    (rename : FilePath → FilePath →
      EStateM IO.Error (Cache (DescriptorInventory × DescriptorSlot × Nat) × WalInodeImage) Unit)
    (atRead beforeStage written : WalInodeImage)
    (inventory : DescriptorInventory) (slot : DescriptorSlot) (offset : Nat)
    (drops : List LockReferenceDrop)
    (issuing : slot.reference ∈ (inventory.afterDrops drops).references slot.description)
    (bindings : FilePath → Option Nat) :
    let path := directory.file .stagedWal
    let captured := (inventory, slot, offset)
    let inode := inventory.inode slot.description
    let persist := fun inode (state : WalInodeImage) => state.completeFileSync inode
    let run := performPaths directory plan remove throw (fun path bytes => stageFreshWithCache path bytes stage)
      (SyncPathGroup.run (sync directory.path openRead fsync)) rename
    stage path plan.keeperBytes beforeStage = .ok captured written →
    bindings path = some inode →
    written.visible inode = plan.keeperBytes →
    ∀ {effective : Bool}, FsyncResult written (persist inode written) effective (fsync captured written) →
      readWalKeeperWithChunks reads (directory.file (.walSegment plan.keeper))
          plan.keeperBytes.size seen.metadata.byteSize.toNat (cache, atRead) =
        .ok plan.keeperBytes (cache, atRead) ∧
      (∃ observed : FsyncObservation (fun handle => handle.2.1.description)
          (fun handle => handle.1.inode handle.2.1.description) captured written persist (fsync captured written),
        observed.issuer = slot.reference ∧ observed.effective = effective ∧
          bindings path = some observed.effectInode) ∧
      FsyncResult (cache.consume path, written) (cache.consume path, persist inode written) effective
        ((run (.replace .writeStaged) >>= fun _ => run (.replace .syncStaged)) (cache, beforeStage)) ∧
      (persist inode written).crashBytes inode = [plan.keeperBytes] := by
  intro path captured inode persist run staged bound visible effective effect
  let observed := FsyncObservation.ofInventory inventory drops
    (fun handle => handle.2.1.description) (fun handle => handle.1.inode handle.2.1.description)
    captured slot.reference issuing rfl written persist (effective := effective) effect
  refine ⟨?_, ⟨observed, rfl, rfl, bound⟩, ?_, ?_⟩
  · simpa only [Cache.captureKeeper, ite_eq_right (Nat.ne_of_lt long)] using
      readWalKeeperWithChunks_exact seen fits cache atRead
  · have writeExact := show plan.keeperBytes.extract 0 plan.keeperSize = plan.keeperBytes by
      rw [← bytes, ByteArray.extract_zero_size]
    have route := syncRemembered (dir := directory.path) (path := path) (cache := cache)
      separate captured openRead fsync written
    have stageExact : stageFreshWithCache path plan.keeperBytes stage (cache, beforeStage) =
        .ok () (cache.remember path captured, written) := by
      simp only [stageFreshWithCache, staged]
    change FsyncResult (cache.consume path, written) (cache.consume path, persist inode written) effective
      ((stageFreshWithCache path (plan.keeperBytes.extract 0 plan.keeperSize) stage >>= fun _ =>
          SyncPathGroup.run (sync directory.path openRead fsync) #[path]) (cache, beforeStage))
    rw [writeExact]
    simp only [Bind.bind, EStateM.bind, stageExact, SyncPathGroup.run_single, route]
    generalize fsync captured written = returned at effect ⊢
    cases effect <;> constructor
  · simp [persist, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, visible]

end Alvoki.Storage.WalSegmentRepair
