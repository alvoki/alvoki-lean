# Filesystem assumptions

The component models and Linux adapters separate code facts from filesystem and device premises. Their proofs must state which layer supplies each guarantee.

| Assumption | Why it matters |
|---|---|
| One writer owns a stable directory namespace for the operation. | Name checks, rename, unlink, and descriptor acquisition refer to the intended files without an unmodeled concurrent replacement. |
| A metadata check is tied to the descriptor later used, or the owner keeps the namespace stable between check and open. | A separate `stat` and `open` can otherwise refer to different inodes or follow a replaced symlink. |
| Initialization creates the required files and durably publishes their names before normal use. | Reopen can distinguish a new component from a partially initialized one. |
| Reads return the requested live bytes or an error. A read error is not an empty file. | Recovery cannot turn an I/O failure into lost history. |
| Buffered writes report an explicit flush result before sync. | A close or finalizer can perform more I/O after the write call, and its failure is not evidence that the earlier write was fully flushed. |
| Append and tail repair preserve the already synchronized prefix. | Later writes or truncation cannot silently alter acknowledged data below the repair point. |
| File sync and parent-directory sync are separate effects. | Syncing file contents does not make a rename, unlink, or newly created name durable; sync the containing directory after namespace changes, and sync its parent when the directory's own binding must survive. |
| A sync may take effect even when its call reports an error. | Retry must consume both possible reached states; the error itself does not identify the durable image. |
| Directory enumeration distinguishes clean end-of-directory from an error after partial results. | A partial listing cannot safely be treated as a complete view when recovery or collection selects names from it. |
| Process exit and power loss have different persistence outcomes. | Process exit may retain cache-visible bytes; power loss selects an admitted joint image of file contents and directory entries. |

## Lean runtime resource pitfall

In Lean 4.36, `Handle.mk` can leak a raw descriptor if `fdopen` fails.
[Lean #16520](https://github.com/leanprover/lean4/pull/16520) closes the descriptor
in this case. For `Handle.mk`, cleanup of any new name is a separate obligation.
The [SSTable output adapter](../../lean/native/open_fresh.cpp) also attempts to
unlink after a successful exclusive creation and a failed `fdopen`. It relies
on stable name ownership and preserves the acquisition error. A failed
exclusive open has no name to clean up. Other open modes require their own
ownership argument before any unlink.

These are premises for component refinement, not claims proved by Lean or by a process-kill test. Map each one to the exact native call and returned handle in the [DurableBlob](../../lean/Alvoki/Experiments/DurableBlob/README.md) and [segmented WAL](../../lean/Alvoki/Experiments/WAL/Segmented/README.md) guides. The WAL-specific [counterexamples](wal-recovery.md) show why the assumptions must remain separate from model correctness.
