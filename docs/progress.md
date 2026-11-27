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
publication error may instead retain the whole batch. A successful marked open
reads the selected checkpoint files and bounded WAL and returns a table whose
latest lookup agrees with that history. Once the keeper sync or trimmed
replacement establishes a writable session, the same finite-call proof extends
its ledger with subsequent writes and snapshots.
[Public append and continuation](../lean/Alvoki/Storage/Disk/NativeRawWriteRootStop.lean) ·
[Literal reader and repair](../lean/Alvoki/Storage/Disk/NativeAlignedWriteRecovery.lean)

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

**Next source boundary.** Derive the staged inode in the final-directory-error
proof from the reached create and cache operations.

[Filesystem assumptions](proofs/native-storage.md#premise-provenance) ·
[Verification commands](../README.md#reproduce-on-linux-x86-64)
