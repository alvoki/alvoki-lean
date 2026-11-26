# Current handoff

Start with the [invariant map](proofs/native-storage.md#refinement-boundaries). The
[roadmap checklist](proof-roadmap.md#completion-checklist-for-native-key-value-refinement)
tracks the remaining obligations.

**What composes.** On the covered aligned recovery path, the sampled checkpoint
and WAL determine the table that `open` returns. Writes and snapshots on that
table extend its incoming client history. If a later checkpoint reaches fsync,
the preceding same-handle calls determine its ready entry: an uncertain write
would have poisoned the handle. At the final directory barrier the proof
identifies the cached root descriptor. Its durability effect remains an explicit
filesystem premise. A later confirmed or uncertain write also establishes its ready
prefix. A failed keeper/marker sync group joins this ledger to a sampled reboot
and either a final failed reopen or a successful reopen followed by an acknowledged
write and a snapshot read on the returned handle, under local storage effects.

**Retries.** The first reboot selects the committed prefix and keeper. Given the
bounded WAL catalog at that sample, the actual admission, listing and read frames
carry them to prune authorization. Its fsync settles the protected names.
A failed attempt can remove some later WAL files, and a failed root fsync can
take effect before reporting its error. Under the scoped file effects, the same
second-reboot proof covers an error during removal or at the following barrier.
It uses one surviving directory map for the selected files, gaps through the
marker, and the later names to enumerate on retry.

A later repair can replace the keeper. If the rename or final directory fsync
fails, either the old or the replacement inode can satisfy the committed target
at the next reboot. Both paths use the same successful post-prune fsync and
staged-file sync. A subsequent successful open that observes the repaired
binding and exact trimmed bytes retains that inode.

An immediate successful open can use the second sample’s selected entry and
bounded catalog. The common open proof supplies the returned table, its storage
entry and the recovery ledger. The same write and snapshot proof used by the
grouped, late and checkpoint callers extends that ledger. It takes the next write’s
observed return and local effects, and the snapshot token at that write’s return heap.

For checkpoint and write recovery, the held directory handle identifies the
cached root inode at installation. Allocating the phase and token needs to
preserve visible bytes only for the inode named by the selected keeper.

At checkpoint reopen, one filesystem assumption connects the closed directory
scan to the physical WAL names above the marker. The reader uses it to interpret
a missing-file stat. The installer uses it to show that pruning covered every
later name. Write retries share the stat proof using their held inode bindings.

**Next obligation.** Supply the remaining read, cache and installation effects
from the fixed production callbacks. The original write’s admitted old-or-whole
target and incoming ledger must come from the same execution prefix. Further
interrupted calls, mixed sessions and maintenance remain in the roadmap.

**Verification baseline.** See the [verification commands](../README.md#reproduce-on-linux-x86-64).
