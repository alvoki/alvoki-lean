import Alvoki.Storage.Disk.Proofs.WAL.ReachableWalSeals
import Alvoki.Storage.Disk.Proofs.WAL.WalSegmentCachedOpenWork

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WalSegmentRotation

/-- A complete WAL pass on a writer reached from bootstrap bounds the
canonical names in a later reader's checked listing. Each surviving seal
ends after the checkpoint and at or before the keeper start. The keeper
contributes one name, even when it is empty. -/
theorem SegmentedBatchDatabaseTrace.walNameCountAfterCollection
    {directory initialDescriptor allowCollection log descriptor before after}
    {boot : LockedFileState WalSegmentRotation.State} (bootstrap : BootstrapReady boot.image)
    (held : boot.owners.Owns directory initialDescriptor)
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor (bootstrap.writerState boot.owners)
      allowCollection log descriptor before)
    {report : SegmentedCollectionReport directory before} (installed : report.Installs after)
    (complete : report.offsets = before.wal.collectionOffsets) {owners readerDescriptor tail}
    (observed : HealthyBoundedWalReports directory owners readerDescriptor after.wal after.target.pair
      after.target.range.watermark after.published.durable tail) :
    let count := listedWalNames (observed.list directory.path)
    count ≤ after.wal.active.first - after.target.range.watermark + 1 ∧
      count ≤ after.target.range.through - after.target.range.watermark + 1 := by
  intro count
  have ready := (trace.preservesRetained (bootstrap.writerReady held).toRetained).1
  have positive := trace.positiveSeals_fromBootstrap bootstrap held
  have noEmpty : (before.wal.sealed.filter fun segment => decide (segment.first = segment.last)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro segment member
    simp [Nat.ne_of_lt (positive segment member)]
  have counted := installed.retainedWalNameCount_fromListing ready complete observed
  have bounded := Nat.le_trans counted (Nat.min_le_right _ _)
  obtain ⟨nextReady, _, keeper, _, target, _, _, _⟩ := installed.outcome ready
  have fromKeeper : count ≤ after.wal.active.first - after.target.range.watermark + 1 := by
    simpa [count, observed.listing, listedWalNames, keeper, target, noEmpty] using bounded
  have through : after.wal.active.first ≤ after.target.range.through := by
    rw [nextReady.resumed.through, ← nextReady.layout.activeEnd]
    exact nextReady.layout.forward _ (List.mem_append_right _ (List.mem_singleton_self _))
  exact ⟨fromKeeper, Nat.le_trans fromKeeper (by omega)⟩

/-- The cached recovery worker uses the same listing and manifest bound to
the collected writer. Its callback budget uses only the selected run count
and the distance from the checkpoint to the keeper. Admission, physical
bytes, and native system calls have separate costs. -/
theorem SegmentedBatchDatabaseTrace.cachedRecoveryRequestsAfterCollection
    {directory initialDescriptor allowCollection log descriptor before after}
    {boot : LockedFileState WalSegmentRotation.State} (bootstrap : BootstrapReady boot.image)
    (held : boot.owners.Owns directory initialDescriptor)
    (trace : SegmentedBatchDatabaseTrace directory initialDescriptor (bootstrap.writerState boot.owners)
      allowCollection log descriptor before)
    {report : SegmentedCollectionReport directory before} (installed : report.Installs after)
    (complete : report.offsets = before.wal.collectionOffsets) {owners readerDescriptor tail}
    (observed : HealthyBoundedWalReports directory owners readerDescriptor after.wal after.target.pair
      after.target.range.watermark after.published.durable tail)
    (sizes : SizedCheckpointRunReports directory observed.reports after.target.pair.manifest after.published.durable)
    (cached : CachedWalFileReports directory observed.reports after.wal after.target.range.watermark tail)
    (removeFile : FilePath → Except IO.Error (Except IO.Error Unit))
    (write : FilePath → ByteArray → Except IO.Error Unit)
    (sync : Array FilePath → Except IO.Error Unit)
    (renameFile : FilePath → FilePath → Except IO.Error Unit) :
    countCachedMarkedOpenRequests directory observed.reports.readOptional
      (checkpointRunSizeReport observed.reports) sizes.readPrefix observed.list
      (fun path => .ok (observed.reports.lstat path)) cached.readSeal cached.readKeeper
      removeFile write sync renameFile ≤
      9 + 2 * decodedCheckpointRunCount (.ok after.target.pair.manifest) +
        2 * (after.wal.active.first - after.target.range.watermark + 1) := by
  have requests := countCachedMarkedOpenRequests_bound directory observed.reports.readOptional
    (checkpointRunSizeReport observed.reports) sizes.readPrefix observed.list
    (fun path => .ok (observed.reports.lstat path)) cached.readSeal cached.readKeeper
    removeFile write sync renameFile
  rw [observed.manifest] at requests
  exact Nat.le_trans requests (Nat.add_le_add_left
    (Nat.mul_le_mul_left 2 (trace.walNameCountAfterCollection bootstrap held installed complete observed).1) _)

end Alvoki.Storage.DiskSession
