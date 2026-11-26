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

**WAL before the first checkpoint.** For a settled writer,
one sampled crash namespace determines the keeper, marker and repair plan.
Under the local filesystem laws, every successful fixed `open` installs the
replay of the writer’s entire history in the phase used by the returned
table. The cutoff comes from the marker, and the actual scan determines
which later segments to prune. This uses the physical write state and the
settled WAL name interval at acknowledgement. [Sampled files](../lean/Alvoki/Storage/Disk/NativeDurableWriteReboot.lean)
· [Literal open and replay](../lean/Alvoki/Storage/Disk/NativeAlignedWriteRecovery.lean)

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

For a late publication error, the observed calls on the original handle
determine the prior client history, reads and submissions. The final write's
preparation identifies the attempted batch even when the old marker survives.
Under the local write effects, the marker and keeper from one reboot select
a replay of that history with zero or all of the batch. After this selection, failed attempts and a later successful
open use the same target. The final failed attempt preserves its pending
ledger. A successful open extends the incoming ledger and returns the exact
table and heap for the next write.

At fresh open, one successful fsync on the identified root descriptor settles
the protected children and the WAL names through the write bound. Given the
pre-sync association of those names with the held root, both facts survive
phase and token allocation and feed the first uncertain-write prefix.

A failed MANIFEST stat after flock feeds the same selected recovery target
as a rejection before flock. The stat, cache disposal, unlock and final lock
drop supply its public error and return heap under local file frames. For
WAL names outside the protected files and keeper, retry only needs presence.
If cache initialization itself fails, the same public open runs unlock and
releases its lock handle. A failed unlock supplies the public diagnostic.

A failed first root fsync now yields the worker’s exact error and heap. The
common cleanup carries the observed descriptor closes at that heap through
unlock and final lock release to derive the public diagnostic and inventory.
Several cache references may share a handle. The fsync may already have taken effect.

On a fresh table, a first acknowledged batch, one sampled crash and a successful
reopen now compose through a latest snapshot lookup for any key. The lookup
uses the reopened table’s actual phase and token and returns the value obtained
by replaying the prepared batch. Its pin carries the sequence returned by the write.
For a subsequent late publication error after the file group succeeded, the
selected old-or-whole history also feeds that same open and snapshot proof.
Both reader paths accept retained sealed segments under the derived offset
selection and the bounded directory observation.

If the write stops during the final directory fsync, the cached handle and its
actual reached heap feed the same crash selection under scoped filesystem frames.
A barrier that took effect rules out the old marker in the physical result.
The guard, phase update and file calls preserve the protected paths and
bounded WAL names locally. After rename the frame uses the actual cached
root read and the outstanding sync.

**Next obligation.** Carry the fresh writer’s storage entry and directory
window across the first acknowledgement to an interrupted second batch.
The initial window must cover the combined row count. For rotation, establish
the sealed files and the new active binding at the rotation’s actual return. On the
failed-barrier path, the surviving namespace and cleanup inventory still need
to feed the next admission.
Further interruptions, mixed sessions and maintenance remain in the
[checklist](proof-roadmap.md#completion-checklist-for-native-key-value-refinement).

**Verification baseline.** See the [verification commands](../README.md#reproduce-on-linux-x86-64).
