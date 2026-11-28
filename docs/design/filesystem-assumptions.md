# Filesystem assumptions

The component models and Linux adapters separate code facts from filesystem and device premises. Their proofs must state which layer supplies each guarantee.

| Assumption | Why it matters |
|---|---|
| One writer owns a stable directory namespace for the operation. | Name checks, rename, unlink, and descriptor acquisition refer to the intended files without an unmodeled concurrent replacement. |
| A metadata check is tied to the descriptor later used, or the owner keeps the namespace stable between check and open. | A separate `stat` and `open` can otherwise refer to different inodes or follow a replaced symlink. |
| An existing store has an admitted initialized image, and the caller supplies a durably named parent directory. | A bootstrap implementation must derive durability of its new contents and names from the barriers it actually issues. |
| A successful component read supplies its required live bytes. | Native reads can return short chunks. The SSTable adapter checks required extents, and whole-file adapters read through EOF or propagate a reported error. |
| Buffered writes report an explicit flush result before sync. | A close or finalizer can perform more I/O after the write call, and its failure is not evidence that the earlier write was fully flushed. |
| Append and tail repair preserve the already synchronized prefix. | Later writes or truncation cannot silently alter acknowledged data below the repair point. |
| File sync and parent-directory sync are separate effects. | Syncing file contents does not make a rename, unlink, or newly created name durable; sync the containing directory after namespace changes, and sync its parent when the directory's own binding must survive. |
| A sync may take effect even when its call reports an error. | Retry must consume both possible reached states; the error itself does not identify the durable image. |
| Directory enumeration distinguishes clean end-of-directory from an error after partial results. | A partial listing cannot safely be treated as a complete view when recovery or collection selects names from it. |
| Process exit and power loss have different persistence outcomes. | Process exit may retain cache-visible bytes; power loss selects an admitted joint image of file contents and directory entries. |

## Persistence after reported errors

A successful synchronization is interpreted as settling the reached bytes
or namespace covered by its primitive contract. Linux tracks writeback
errors with a cursor per open file description. A previously observed error
can be absent from a later `fsync`, including on a newly opened descriptor.
Recovery therefore needs the premise that its selected bytes remain
available for successful persistence. A later successful call alone gives
no evidence that bytes lost in a failed writeback were repaired. Lost
writeback that leaves misleading clean cache bytes is outside the current
proved fault model. A reproducible ext4 and XFS block-fault experiment records
that case and its consequences for recovery.
[Linux writeback experiment](linux-writeback/README.md)
[Linux VFS writeback errors](https://github.com/torvalds/linux/blob/v6.18/Documentation/filesystems/vfs.rst#handling-errors-during-writeback)

Live atomic rename and crash persistence are distinct effects. DurableBlob
and segmented WAL assume that power loss before the directory barrier
leaves one of their admitted intact bindings. A process stop can leave the
new binding and kernel-cached bytes visible while discarding userspace
buffers. Lock release at process exit assumes no surviving alias to the
open file description.

## Lean runtime resource pitfall

Lean 4.36 on Linux can leak a raw descriptor when `fdopen` fails after
`Handle.mk` acquires it. [Lean #16520](https://github.com/leanprover/lean4/pull/16520)
closes that descriptor. Fault injection confirmed the fix on Lean 4.37.0-rc1.
Upgrade the toolchain once a stable Lean release includes the fix and rerun
the repository checks.

An exclusive open can still leave a newly created name after `fdopen` fails.
Name cleanup requires evidence that this call created and still owns that
name. Model the reached namespace when handle construction fails before
the caller's cleanup starts.

These are premises for component refinement, not claims proved by Lean or by a process-kill test. Map each one to the exact native call and returned handle in the [DurableBlob](../../lean/Alvoki/Experiments/DurableBlob/README.md) and [segmented WAL](../../lean/Alvoki/Experiments/WAL/Segmented/README.md) guides. The WAL-specific [counterexamples](wal-recovery.md) show why the assumptions must remain separate from model correctness.
