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
and the final failed reopen under the local storage effects.

**Retries.** Admission, read and cleanup callbacks preserve the selected files.
A failed prune may already have removed later WAL segments. Even if all removes
return and the following directory fsync reports EIO, the retry starts from the
actual changed namespace. The live keeper stays in place through this barrier.
A later repair can replace it with a new inode.

**Next obligation.** Carry the replaced keeper's new binding and bytes through
later failed and interrupted open attempts. A successful scan still needs the
local enumeration law covering every physically present later WAL name. The
remaining mixed sessions and maintenance cases are listed in the roadmap.

**Verification baseline.** See commit `43bb5c19` and the [verification commands](../README.md#reproduce-on-linux-x86-64).
