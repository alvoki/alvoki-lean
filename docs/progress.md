# Current handoff

The [invariant map](proofs/native-storage.md#refinement-boundaries) connects filesystem
observations to client history. The [roadmap checklist](proof-roadmap.md#completion-checklist-for-native-key-value-refinement)
tracks the open production paths and the six system guarantees.

**What composes.** A fresh open and first acknowledged write establish a write
entry and a bounded WAL namespace. On the covered mixed-call paths, the actual
phase read, cache and ledger connect writes and snapshots to rotation or checkpoint.
After a failed rotation, a surviving directory map and a complete bounded scan
determine the selected seals, keeper and any names to prune.
[Fresh execution](../lean/Alvoki/Storage/Disk/NativeFreshOpenedSessions.lean) ·
[Rotation](../lean/Alvoki/Storage/Disk/NativeRotationWalReplay.lean) ·
[Checkpoint](../lean/Alvoki/Storage/Disk/NativeFreshFinalCheckpoint.lean)

**Which writes survive.** An append interrupted before marker publication retains
the previous history under the descriptor and byte-prefix assumptions. A late
publication error may instead retain the whole batch. For the fresh writer's
second batch, the public stop and successful publication prefix identify the
issued directory fsync before reboot. A successful marked open reads the
selected checkpoint files and bounded WAL and returns a table whose latest
lookup agrees with that history. For an aligned keeper with no later
WAL files, the selected checkpoint, marker, listing and WAL read callbacks
determine the actual prepared replay and measured keeper extent. With the
reached admission, two syncs and phase and token allocations, this gives
the exact public return. A latest snapshot lookup on that table uses its
allocated phase and token, and returns the selected replay's value and
sequence. The reached callbacks still supply the marked probes, phase
initialization and preservation, and token comparison for that lookup.
[Public append and continuation](../lean/Alvoki/Storage/Disk/NativeRawWriteRootStop.lean) ·
[Literal reader and repair](../lean/Alvoki/Storage/Disk/NativeAlignedWriteRecovery.lean) ·
[Aligned public open](../lean/Alvoki/Storage/Disk/NativeMarkedOpenInterpreter.lean)

**What another open sees.** A live retry starts at the public failure's cleanup
heap. Each accepted suffix removal stays visible as an absent name. If a removal
reports an error, its observed effect determines whether that name survives.
Unvisited names keep their bindings. If the entire loop returns and the directory
sync fails, the live suffix is already pruned. Another reboot selects a directory
map admitted by the observed durability effects.
[Failed repair and retry](../lean/Alvoki/Storage/Disk/NativeLongKeeperFinalSyncObservation.lean)

**Where a marked open failed.** Once the flat-WAL and marker probes select
the marked branch, a worker error comes from preparation, repair or installation.
If repair ran, its plan, keeper extent and entry heap come from the successful
reader of that worker. The failed-retry proof uses this same boundary.
[Worker classification](../lean/Alvoki/Storage/Disk/NativeMarkedOpenInterpreter.lean) ·
[Measured preparation](../lean/Alvoki/Storage/Disk/NativeAlignedMarkedWorker.lean)

For a failed marked worker, observing its successful keeper rename connects the
same measured preparation, staged-file sync and final directory error to cleanup
and a subsequent sampled reboot. The rename observation is cleared before
installation. Frames apply to the staging and rename heaps reached by that open.
[Worker observation](../lean/Alvoki/Storage/Disk/NativeMarkedOpenInterpreter.lean) ·
[Retry and reboot](../lean/Alvoki/Storage/Disk/NativeLongKeeperFinalSyncObservation.lean)

The marked open carries its allocated directory slot to the final fsync. The
successful staging-file fsync makes the trimmed prefix durable on the fresh
inode. Rename binds that inode at the keeper path, and the cache load preserves
its live and durable bytes. This same staged inode feeds live retry and reboot.
The returned prune, staged write and fsync, rename and cache load determine the
logical image at the issued directory fsync. Its error may occur before or after
the directory update takes effect. The proof tracks lock ownership separately through cleanup.
The cache allocations and reached marked reads carry the entry image through
the keeper's release into both repair-error proofs.
[Final sync and retry](../lean/Alvoki/Storage/Disk/NativeLongKeeperFinalSyncObservation.lean)

If the `WAL.next` fsync fails, the reached descriptor identifies scratch
and is distinct from the canonical keeper. The completed prune barrier and
observed effects through cleanup preserve the keeper, selected files and
pruned names on one reboot map. When the initial WAL window reaches the
selected cutoff, the next successful public open returns the exact ready
handle with no pins. Its ledger retains prior reads and records the original
uncertain batch once. The common ready-call proof then extends that ledger
with supported writes and snapshot responses on the returned handle, using
the reached callback reports. The native write path uses one inode-byte
projection for the initial write, recovery and subsequent calls.
[Staged-file sync and reboot](../lean/Alvoki/Storage/Disk/NativeLongKeeperFinalSyncObservation.lean) ·
[Returned handle and ready calls](../lean/Alvoki/Storage/Disk/NativeLateWriteRecovery.lean)

For a final directory-fsync error, the observed rename proves the measured
keeper was long. The checked plan bounds the unlinks. Their returned images,
the scratch write and sync, rename and final cache load determine the repair
trace for either fsync effect. Cleanup preserves the acquired inode and its
payload. The sampled recovery observations at the cutoff supply the entry for
the shared opener. Both rename-error and final-directory-error paths derive
their retry frame from the returned authorization, unlinks and staging operations.

Exclusive creation supplies an empty scratch inode. The write and flush determine
its visible bytes. Registration preserves the scratch field. The scratch-fsync,
rename and final directory-fsync error proofs reconstruct the registered image
from these bytes and callback frames for the rest of the image. On the latter
two paths, the pending cell still holds only that scratch handle when cleared.
Removing its sole entry preserves the file image, and successful fsync of its inode makes that
payload durable under the local file-sync projection. On reboot, one sampled namespace covers
the keeper, immutable children, bounded WAL interval and every actually removed name.

**Next source boundary.** The rename-error consumer still receives the returned
authorization, prune, scratch write and grouped sync separately. Derive that
prefix from a worker observation that identifies the failed rename, retaining
both physical outcomes of the rename error.

[Filesystem assumptions](proofs/native-storage.md#premise-provenance) ·
[Verification commands](../README.md#reproduce-on-linux-x86-64)
