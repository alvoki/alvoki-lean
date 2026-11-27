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

**Writes and rotation from fresh state.** The first acknowledged batch
establishes the cache, bytes, WAL interval and client ledger on the returned
heap. A between-call reboot preserves that batch. If a second write stops
at the final directory fsync, the bootstrap interval must cover both batches.
One sampled namespace then retains the first plus zero or all of the second,
which has no client response. A barrier that took effect excludes the old
marker. A late publication error also feeds this reader. On successful open,
the latest pin and lookup extend the ledger with the observed sequence, key
and value. [Fresh traces](../lean/Alvoki/Storage/Disk/NativeFreshOpenedSessions.lean)

Rotating a nonempty WAL seals the old keeper and establishes the write entry
and bounded name interval for the empty successor. Creating the successor
and reusing an existing private empty file feed the same reader. The fresh
create path uses the cache and storage established by the first write. If
the final directory fsync returns an error, the same file prefix leads to
the exact diagnostic and poisoned return heap under local callback effects.
[Rotation boundaries](proofs/native-storage.md#refinement-boundaries)

After the first confirmed batch, a failed rotation-directory fsync can be
followed through explicit close and a successful live open on the released
heap. The close uses the observed descriptor drops. The reopened session reads
the original batch from the visible marker and WAL segments. A power loss
instead samples one surviving directory map. Both paths use the same reader.
[Fresh write through live reopen](../lean/Alvoki/Storage/Disk/NativeFreshOpenedSessions.lean)

At acknowledgement, the staged inode's file sync, publication rename,
directory sync and phase store establish the visible marker bytes.
The live reader carries those bytes through close. For power loss, the
settled WAL interval rules out a stale successor inode. From the exact
failed directory fsync, one surviving map determines the keeper and the
ordinary reader's lookup on the table returned by a successful open.
The reader uses the observed marker, keeper and seals in both cases.
[Publication](../lean/Alvoki/Storage/Disk/NativeReadyWriteStorage.lean) ·
[Sample to open](../lean/Alvoki/Storage/Disk/NativeRawRotationReboot.lean)

The fresh reboot proof starts with the first acknowledged batch and follows
the exclusive-create handle through file sync to the failed directory
sync. With either permitted successor binding, a lookup through the
table returned by the next successful aligned open extends that batch's
client ledger. [Fresh WAL recovery](../lean/Alvoki/Storage/Disk/NativeFreshOpenedSessions.lean)

The rotation now derives preservation of existing files and other bounded
WAL names from the individual filesystem callbacks. A failed open can be
retried any finite number of times when each attempt preserves the sampled
WAL files. The successful retry reads those files on its own entry heap.

For a subsequent write, reboot must also settle the selected marker, sealed
segments and directory binding. Given those reset and retry effects, the
actual opener supplies its lock, cache and keeper to the same finite write
and snapshot proof used after checkpoint recovery. Its ledger starts with
the original acknowledged batch. [Writable reopen](../lean/Alvoki/Storage/Disk/NativeAlignedReadyCalls.lean)

Both live and rebooted WAL readers project the marker and keeper bytes
from the reached path bindings. The writable opener also derives the seals
below the keeper, including gaps. A complete listing on its held directory
identifies the later canonical names. Subsequent lookups track which of
those names still exist after removal.

**Next obligation.** Connect a failed repair that has already removed a later
segment to the next literal open and writable session. Use a history in
which the later segment is reachable. Establish
its entry from the reached unlink and directory barrier, including the case
where the barrier takes effect and returns an error.
The filesystem's survival and byte-sampling laws
remain explicit. Further mixed calls, interruptions and maintenance
remain in the [checklist](proof-roadmap.md#completion-checklist-for-native-key-value-refinement).

**Verification baseline.** See the [verification commands](../README.md#reproduce-on-linux-x86-64).
