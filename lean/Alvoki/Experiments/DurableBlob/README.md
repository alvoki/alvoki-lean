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

The Linux interpretation assumes the following primitive effects at the
reached paths and descriptions:

- A successful directory open holds the managed directory. A successful
  stage open holds the private staging inode, truncated or created.
  Open errors, partial writes, failed flushes and late finalization of
  scratch can affect scratch. They preserve the active bytes and binding.
  Scratch bookkeeping between attempts may be stale. Each publication
  overwrites it and must complete write and flush before syncing or renaming.
- A successful read returns the exact bytes of the visible active binding.
  The read and directory open do not modify that binding. Write followed
  by successful flush provides the complete staged bytes on the held writer.
  File fsync persists the bytes through that descriptor. Releasing it
  after a successful flush and sync preserves the persisted bytes.
- Rename atomically replaces the visible active binding with the staged
  inode. Directory fsync on the held directory settles its visible bindings.
  A failed rename or fsync can have either the before or after effect.
  Before the barrier, a crash can select either intact binding. The model
  can retain both choices until a barrier even if writeback has narrowed
  the physical choices.
- The runtime and compiler preserve the meanings of these reached calls,
  including descriptor lifetime and the native fsync wrapper. The filesystem
  and device preserve synced data under the specified crash model. Recovery
  may fail on resource or I/O errors. The owner supplies the stable,
  exclusive namespace described above.
  [Filesystem premises](../../../../docs/proofs/filesystem.md)

A process stop retains the reached visible binding. A power loss selects a
surviving binding. An interruption uses the effect at the cut, or the
completed effect if the final reply was lost. `LinuxEffects.publishUncertain`
and `LinuxEffects.reopenInterrupted` retain that image without issuing an
acknowledgement or ready session. `LinuxEffects.reopenAgain` checks that a
second successful open after stop or power loss returns the first reply.
The focused manifest check exercises rename and barrier errors in the
interpreter and uses the native adapter for its Linux fixture.

A future segmented WAL change could reuse this protocol for `CONTROL`.
PR #5 retains the original CONTROL writer for sync.
Before sharing publication code, establish that WAL preparation makes any newly referenced segment
durable, that recovery settles the selected control before collecting files,
and that the WAL's directory ownership and initialization satisfy the blob
premises. The WAL retains its control codec and segment-lifetime rules.
