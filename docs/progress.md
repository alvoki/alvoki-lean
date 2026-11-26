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

**Retries.** Under their local effect laws, admission, read and cleanup preserve the selected files.
A failed prune may already have removed later WAL segments. Even if all removes
return and the following directory fsync reports EIO, the retry starts from the
actual changed namespace. The live keeper stays in place through this barrier.
A later repair can replace it with a new inode. At the public final-sync error,
the replacement is live with exactly the trimmed bytes. If those bytes and the
same binding reach the next successful open, the returned writer retains that
inode. An error before flock supplies the frame for this handoff.

After a failed write or an interrupted recovery followed by power loss, the same
rule constructs the retry entry from the files sampled in one namespace.

For a public final directory fsync error, the second reboot can select the old or the
replaced keeper. Under the scoped filesystem effects, both recover the same committed
prefix and protected files. A failed keeper rename also preserves these disk choices.

**Next obligation.** Carry the bounded WAL name inventory, including gaps, from the
successful post-prune directory fsync through staging and cleanup to the second reboot.
This supplies the scan's input on the chosen namespace. A successful scan also needs
the local enumeration law covering every physically present later WAL name. The
remaining mixed sessions and maintenance cases are listed in the roadmap.

**Verification baseline.** See commit `ed159f33` and the [verification commands](../README.md#reproduce-on-linux-x86-64).
