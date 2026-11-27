# WAL keeper proofs

Tracks keeper reads, descriptors and the observations used in long-keeper repair and retry.

Start with [KeeperReadCustody](KeeperReadCustody.lean) · [NativeLongKeeperFinalSyncError](NativeLongKeeperFinalSyncError.lean). KeeperReadCustody is imported by [CachedWalChunkReports](../Recovery/CachedWalChunkReports.lean). See the [disk proof guide](../README.md) for related areas and the refinement boundaries.

To check the first module from `lean/`, run `lake build Alvoki.Storage.Disk.Proofs.Keeper.KeeperReadCustody`. These theorems use the assumptions stated in their Lean declarations.
