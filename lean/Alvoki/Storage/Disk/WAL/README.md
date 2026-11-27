# Segmented WAL

Start with `DiskTable.collectCoveredWal` in [DiskTable.lean](../DiskTable.lean).
[CollectionPlan.lean](CollectionPlan.lean) validates the checkpoint and marker,
reads the listed segment extents and selects covered segments. The strict marker
and checkpoint decoding used by that plan is in [CollectionRange.lean](CollectionRange.lean).

[WalSegmentCollection.lean](../Proofs/Collection/WalSegmentCollection.lean)
models segment histories and proves properties of eligible deletions. Its crash
model is separate from the executable collection decision. Actual directory
listing and filesystem effects depend on the assumptions described in the
[native-storage invariant map](../../../../../docs/proofs/native-storage.md#refinement-boundaries).

Run `bash scripts/check-sequential.sh` from the repository root to build and
audit the storage modules, including these collection modules.

`DiskTable` no longer transitively imports the WAL publication and crash models.
Code that used those model declarations through a `DiskTable` import must import
[WalSegmentCollection.lean](../Proofs/Collection/WalSegmentCollection.lean)
or the relevant model module explicitly. The former `WalSegmentCollection` and
`WalSegmentCollectionPlan` module paths remain as compatibility imports.

## Discovery and selected reads

`DiskTable.open` reaches the marked recovery path through `recoverSegmentedWal`
and `reopenMarkedBoundedWithCachedExtents` in
[WalSegmentCachedExtentOpen.lean](WalSegmentCachedExtentOpen.lean). It lists
the directory, uses [CollectionPlan.lean](CollectionPlan.lean) to probe and
sort extents, selects the bounded interval with `selectWalExtentsThrough`
in [WalSegmentCachedExtentOpen.lean](WalSegmentCachedExtentOpen.lean), then
reads the selected sealed prefixes and keeper. The separate
[WalSegmentReadIO.lean](WalSegmentReadIO.lean) provides the non-cached
segment-read schedule. [WalSegmentFileName.lean](WalSegmentFileName.lean) checks
canonical names; [WalSegmentReplay.lean](WalSegmentReplay.lean) validates
segment spans and assembles replay bytes. [WalSegmentInventory.lean](WalSegmentInventory.lean)
and [WalSegmentReadPlan.lean](WalSegmentReadPlan.lean) relate reported paths
and read plans to the segment model.
