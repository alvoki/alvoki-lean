# Durable blob replacement

The owner starts offline with one initialized durable byte string. First call
`reopen`. A successful `publish bytes` makes the supplied bytes durable. If
publication fails or its reply is lost, stop using the session and reopen.
The first successful reopen returns the previous value or the complete
proposal, according to the surviving state. With no intervening publication,
another successful reopen returns that same value, even after power loss.
A failed reopen returns no value and may be retried. The caller serializes
operations and observes this session discipline. [Client contract](Contract.lean)

[Protocol](Protocol.lean) writes the private staging file, syncs
its bytes through the same write handle, renames it over the active name,
and syncs the parent directory. Reopen reads the active file and syncs
the directory before returning. A process exit after rename can leave the
new file visible before the name is durable. Returning the read alone would
allow a second crash to reverse a successful reopen.

The [Linux adapter](Native.lean) reserves `BLOB` and `BLOB.next` in a
durably named, stable directory. The caller supplies exclusive ownership
and an initialized active file. Both names, whenever present, refer to
distinct regular files without aliases to other files. Missing active data
or a read error propagates as an error. The staging file can be left behind
and overwritten by the next publication.

The native backend and the proof interpreter instantiate the same
`Primitives.backend`. This fixes the paths, modes, descriptor passed to
each write, flush and fsync, and the order and error handling of the calls.
The interpreter in [Proofs](Proofs.lean) takes outcomes of those individual
primitives. `LinuxEffects.reopen` and `LinuxEffects.publish` extend the
existing `Run` with the exact returned or submitted bytes.
`Run.refines` yields the public `Allows` trace, while
`LinuxEffects.reopenSettles` gives the public open step and the settled
image directly. `Run.healthy_open` shows that a reachable offline image
can reopen when the read and barrier succeed.

## Primitive correspondence

For a reached call, the Linux IO result and its physical effect must match
the following interpretation. Success/failure flags come from that call.
For rename and fsync, an observed error allows either effect. Reports for
unreached operations are immaterial.

| Linux primitive at the reached argument | Correspondence to `LinuxEffects.primitives` |
| --- | --- |
| `readBinFile BLOB` | Success returns the exact bytes of the visible binding, `Image.active`. A failure returns an error. Neither changes the binding or its crash choices. |
| Open the directory for read | Success holds the managed directory and yields `.directory`. Failure skips fsync. Opening leaves the blob image unchanged. |
| Open `BLOB.next` for write, then write and flush | Successful open holds the private, truncated or newly created inode and yields `.writer`. The write records the supplied bytes for staging. Successful flush makes those full bytes visible on that inode. Open, write or flush failure can leave arbitrary scratch contents, including effects of a late close. Scratch effects preserve the active binding and every active crash choice. |
| File fsync through `.writer` | The effect persists the flushed bytes on that inode, recorded in `Image.synced`. A pre-effect error preserves the prior projected image. Closing after successful flush and sync preserves the synced bytes. |
| Rename `BLOB.next` over `BLOB` | The effect switches the visible binding atomically to the synced inode. Until a barrier, the model covers both intact crash choices. Physical writeback may narrow that set. |
| Directory fsync through `.directory` | The effect settles the visible binding and narrows the modeled survivors to that binding. A pre-effect error leaves the previous choices. |

The shared schedule fixes which paths and modes are used and passes the
actual handle returned by each open to the relevant primitives. The runtime
must keep that handle tied to its open file description, including through
the native fsync wrapper. The owner's exclusive stable namespace ties the
directory handle to the parent of both names and keeps the staging name
bound to the writer's inode until rename. Non-aliasing also keeps scratch
effects private. These facts make the two abstract identities sufficient
within each call. Each successful open resolves its own descriptor again,
so neither tag asserts descriptor equality across calls or restarts.
Compiler and runtime fidelity, the primitive effects above, and the device's
preservation of synced data remain external. [Filesystem premises](../../../../docs/design/filesystem-assumptions.md)

A process stop retains the reached visible binding. A power loss selects a
surviving binding. An interruption uses the effect at the cut, or the
completed effect if the final reply was lost. `LinuxEffects.publishUncertain`
and `LinuxEffects.reopenInterrupted` retain that image without issuing an
acknowledgement or ready session. `LinuxEffects.reopenAgain` checks that a
second successful open after stop or power loss returns the first reply.
The focused manifest check exercises rename and barrier errors in the
interpreter and uses the native adapter for its Linux fixture.

## L0 producer check

The initialized open/publication and failed-open/retry proofs live in
[L0 ManifestComposition](../L0/ManifestComposition.lean) and are checked by
the native L0 script. They use the Linux primitive interpreter, the blob
producer theorems and the real typed manifest backend. Native callers still
need to tie the primitive reports to the reached filesystem effects.

## Follow-up for WAL and SSTable

PR #5 already retains the original `CONTROL` writer for WAL sync. Try
sharing the staged writer and directory barrier with that path once its
producer establishes durability of newly referenced segments and settles
the control binding before collection. WAL owns its codec and segment
lifetime. For SSTable, try sharing held-file identity, exact positional
reads and file sync with its checked open or builder. SSTable owns content
immutability, range checks, codec validity and publication by the caller.
Extract a primitive only after the second consumer shows what proof or
executable code it can reuse.
