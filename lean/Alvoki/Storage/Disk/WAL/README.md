# Segmented WAL

The disk engine uses a segmented write-ahead log (WAL) to record writes before acknowledging them. A durable marker selects an absolute byte boundary in the segment history; reopening uses that boundary to decide what to recover. Start with `DiskTable.write`, `writeBatch`, `rotateWal` and `open` in [DiskTable.lean](../DiskTable.lean).

## Write and publish

`write` and `writeBatch` prepare the next table and sequence numbers before WAL publication. A single write calls `commitWalWrite` and `WalSegmentCommit.commitAt`; a nonempty batch prepares events with [WalBatch.lean](WalBatch.lean) and calls `commitBytesAt` in [WalSegmentCommit.lean](WalSegmentCommit.lean). An empty batch returns the current sequence without WAL publication.

The commit schedule appends encoded frames to the active segment, writes a staged absolute byte boundary, syncs the active segment and staged marker, renames the marker to `WAL.commit`, then syncs the directory. [WriteAheadLog.lean](WriteAheadLog.lean) encodes frames and [WalBoundary.lean](WalBoundary.lean) encodes the marker. A single write or nonempty batch returns its acknowledgement only after publication succeeds; a reported publication failure may have an uncertain commit outcome. The durability argument depends on the [filesystem assumptions](../../../../../docs/proofs/native-storage.md).

## Rotate

`DiskTable.rotateWal` rolls over at the committed frame count when the active segment has data. [WalSegmentRotationIO.lean](WalSegmentRotationIO.lean) creates or reuses an empty successor and syncs the file and directory; `DiskTable` then installs it as the next append target. The absolute marker does not change. [WalSegmentBootstrapIO.lean](WalSegmentBootstrapIO.lean) handles the initial empty segment.

## Recover

`DiskTable.open` reaches marked recovery through `recoverSegmentedWal` and `reopenMarkedBoundedWithCachedExtents` in [WalSegmentCachedExtentOpen.lean](WalSegmentCachedExtentOpen.lean). The cached path lists the directory, probes and sorts extents, selects the interval through the marker, and reads the selected sealed prefixes and keeper. [WalSegmentReadIO.lean](WalSegmentReadIO.lean) provides the non-cached read schedule; [WalSegmentReplay.lean](WalSegmentReplay.lean) validates spans and assembles replay bytes. On reopen, [WalSegmentRepairIO.lean](WalSegmentRepairIO.lean) and [WalSegmentRepairOpen.lean](WalSegmentRepairOpen.lean) handle repair.

[WalSegmentFileName.lean](WalSegmentFileName.lean) checks canonical names. [WalSegmentInventory.lean](WalSegmentInventory.lean) and [WalSegmentReadPlan.lean](WalSegmentReadPlan.lean) relate reported paths and read plans to the segment model. The [disk proof guide](../Proofs/README.md) links the recovery and filesystem observations; the [invariant map](../../../../../docs/proofs/native-storage.md#refinement-boundaries) states their boundaries and remaining work.

## Collect covered segments

After checkpointing, `DiskTable.collectCoveredWal` can remove covered segments. [CollectionPlan.lean](CollectionPlan.lean) validates the checkpoint and marker, reads listed segment extents and selects covered segments; [CollectionRange.lean](CollectionRange.lean) contains the strict marker and checkpoint decoding used by the plan. [WalSegmentCollection.lean](../Proofs/Collection/WalSegmentCollection.lean) separately models segment histories and eligible deletions. Directory listing and filesystem effects depend on the assumptions in the invariant map.

## Experiment and compatibility

The separate [single-file WAL experiment](../../../Experiments/WAL/README.md) explores recovery policies and a modeled client contract. It is distinct from the segmented `DiskTable` path; `DiskTable` rejects a flat WAL binding on open. The [design note](../../../../../docs/design/wal-recovery.md) describes the experiment and limits of its proof.

`DiskTable` no longer transitively imports the WAL publication and crash models. Code using those declarations must import [WalSegmentCollection.lean](../Proofs/Collection/WalSegmentCollection.lean) or the relevant model module explicitly. The former `WalSegmentCollection` and `WalSegmentCollectionPlan` module paths remain as compatibility imports.

Run `bash scripts/check-sequential.sh` from the repository root to build and audit the storage modules, including the collection modules.
