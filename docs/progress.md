# Current handoff

Start with the [invariant map](proofs/native-storage.md#refinement-boundaries)
for the argument from filesystem observations to client history. The
[completion checklist](proof-roadmap.md#completion-checklist-for-native-key-value-refinement)
tracks the remaining production paths and the six public guarantees.

**From a returned table to a client history.** On the covered aligned reopen
paths, the sampled checkpoint and WAL bytes determine the table that the
literal open returns. Writes and snapshots on that handle extend its
incoming ledger. If a subsequent checkpoint reaches fsync, the preceding
calls on the same handle determine its ready entry. An uncertain write
would have poisoned the handle. The final directory barrier uses the
identified cached root descriptor and its explicit filesystem effect.
[Checkpoint composition](../lean/Alvoki/Storage/Disk/NativeFreshFinalCheckpoint.lean)

**From write failure to recovery.** Before the first checkpoint, the marker
selects the committed WAL prefix. After a late publication error, one
surviving directory map selects the previous history plus zero or all of
the submitted batch. After a failed sync group, the recovered ledger can
continue through a failed open or through a successful open, another write
and a snapshot read. Failed opens may have effects: an unlink may remove
a name, a directory sync may take effect before returning an error, and a
failed replacement may leave either keeper inode. The next reboot samples one allowed
crash map from the reached filesystem state.
[Write and repair boundaries](proofs/native-storage.md#refinement-boundaries)

**Current WAL milestone.** Fresh open and the first acknowledged write
establish the physical write entry and bounded WAL namespace. On a
failed nonempty rotation, the exclusive successor starts at the committed
cutoff. A sampled reboot chooses whether that name survives. The reader
observes the selected marker, keeper and sealed files. Failed opens
that preserve the bounded WAL name map, including missing names, and the
selected bytes carry this absence to the retry heap. If that bound covers the
successful retry's held listing, it has no later segment to unlink.
Directory and keeper sync still take place.
[Fresh execution](../lean/Alvoki/Storage/Disk/NativeFreshOpenedSessions.lean)
· [Writable retry](../lean/Alvoki/Storage/Disk/NativeAlignedReadyCalls.lean)

The mixed-prefix proof starts from an established write entry and bounded
namespace on a returned handle. The ready phase read at rotation excludes
an earlier poisoned return. The preceding writes and snapshots supply the
actual client ledger, cache and unchanged manifest at the rotation entry.
The same sampled-WAL proof then carries that ledger to the returned table.
[Mixed rotation and retry](../lean/Alvoki/Storage/Disk/NativeRotationWalReplay.lean)

**An interrupted append.** The public write dispatcher and the exit proof
use the same stopped append helper. It identifies the active-cache read,
the selected handle and the heap reached by the issued write. Given a
live descriptor bound to the keeper, a filesystem effect preserving its
old byte prefix and the protected files is enough for a reboot to select
the old target. The interrupted request contributes no acknowledged rows.
Before the first checkpoint, the sampled plan also feeds the literal WAL
reader under its reset, enumeration and read assumptions.
[Write interruption](../lean/Alvoki/Storage/Disk/NativeRawWriteRootStop.lean)

**Next obligation.** Connect the checkpoint-backed reader to this same
append sample when the actual keeper can contain a partial batch. For layouts with extra files,
derive the next retry entry from a modifying failed repair, including an
effective directory barrier that reports failure.

[Filesystem premises](proofs/native-storage.md#premise-provenance)
· [Verification commands](../README.md#reproduce-on-linux-x86-64)
