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

The filesystem must provide exact reads or errors, flushed staged writes,
file sync durability, atomic same-directory replacement, and directory sync
durability for visible bindings. Before the directory barrier, power loss
may select either intact binding. Filesystem errors at sync or rename can
precede or follow their effects. The model excludes post-sync data loss,
external modification of the directory or files, and corrupted bytes.
The native callback mapping depends on the runtime, filesystem and device.
[Filesystem premises](../../../../docs/proofs/filesystem.md)

`Run.refines` interprets the same Lean protocol using primitive effects and
checks arbitrary finite traces of publication, recovery, process exit and
power loss. `Run.healthy_open` shows that any reachable offline image can
reopen when its read and barrier succeed. A response lost after a completed
publication leaves a durable new value, even though the caller must recover
to learn the outcome. [Proofs](Proofs.lean)

The focused manifest check also runs a model regression that exposes the new
binding before the directory barrier, reopens successfully, then simulates
power loss and reopens again.

A future segmented WAL change could reuse this protocol for `CONTROL`.
First establish that WAL preparation makes any newly referenced segment
durable, that recovery settles the selected control before collecting files,
and that the WAL's directory ownership and initialization satisfy the blob
premises. The WAL retains its control codec and segment-lifetime rules.
