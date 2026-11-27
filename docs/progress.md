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

**Next source boundary.** Trace a failed keeper replacement from the marked
open worker itself. Its successful preparation determines the selected files,
the measured keeper extent and the heap at which repair begins. The error
at the final directory sync must feed the same retry and ledger proof.
[Marked worker](../lean/Alvoki/Storage/Disk/NativeMarkedOpenInterpreter.lean) ·
[Replacement error](../lean/Alvoki/Storage/Disk/NativeLongKeeperFinalSyncObservation.lean)

[Filesystem assumptions](proofs/native-storage.md#premise-provenance) ·
[Verification commands](../README.md#reproduce-on-linux-x86-64)
