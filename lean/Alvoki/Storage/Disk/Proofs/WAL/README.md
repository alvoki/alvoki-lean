# WAL proofs

Studies WAL path identity, bounded reads, commit effects and checkpoint retention.

Start with [WalSegmentPathIdentity](WalSegmentPathIdentity.lean) · [WalSegmentCommitEffects](WalSegmentCommitEffects.lean). WalSegmentPathIdentity is imported by [SegmentedCollectionInventory](../Collection/SegmentedCollectionInventory.lean). See the [disk proof guide](../README.md) for related areas and the refinement boundaries.

To check the first module from `lean/`, run `lake build Alvoki.Storage.Disk.Proofs.WAL.WalSegmentPathIdentity`. These theorems use the assumptions stated in their Lean declarations.
