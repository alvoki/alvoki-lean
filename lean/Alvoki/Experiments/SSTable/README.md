# Immutable SSTable

ALVSST05 replaces the earlier experimental SSTable format. Existing
ALVSST03 files require rebuilding from their source data. Backward
compatibility is outside this experimental milestone.

`ALVSST05` uses one index and reader for fixed or variable key and value
widths. The writer validates declared widths and strictly increasing byte
keys. The reader compares the independent expected table ID with the
checked footer before loading the root.

The byte API sorts keys lexicographically and returns an exact-match value
from `lookup`. `seek` returns the first row index whose key reaches the query,
or the row count. `next i` returns row `i` and its successor cursor, or
`none` at and beyond the row count. The caller can supply separate key and
value codecs through [`TypedTable`](Core.lean). The key codec must preserve the
caller's order and both codecs must round-trip.
[Public contract](Representation.lean) · [Typed refinement](Proofs/Typed.lean)

```text
File   [ data packets … ][ leaf index ] … [ data packets … ][ leaf index ][ root ][ footer ]
Read   root (held once) → leaf index → data packet → in-memory row search
```

Root and leaf references store the last child key, its physical offset and
length, and its first row number and row count. The row range supports
arbitrary `next i` cursors. Each level uses binary search. The reader checks
the selected child's extent, row coverage and last key against its parent
before using it. A lookup that falls past the root's last key needs neither a
leaf nor a data read.

| Key / value | Data packet body |
| --- | --- |
| fixed / fixed | Packed rows with direct addressing |
| fixed / variable | Packed rows and local row offsets |
| variable / fixed | Packed rows and local row offsets |
| variable / variable | One key length per row, packed bytes and local row offsets |

Local offsets include an end offset. The format encodes lengths
and offsets as little-endian 64-bit words. Each packet ends with a four-byte
CRC32C bound to its kind, table ID and starting offset. The footer uses a
fixed checksum context and carries the table ID in its body. The expected ID
must come from outside the file. CRC32C detects accidental corruption and
does not authenticate a file.

The streaming writer buffers one data packet, one leaf index and the root.
It emits completed packets without seeking and appends the root and footer
once. Data and leaf targets are configurable. Each packet, including its
checksum, fits within the 16 MiB native read cap. The root has the same hard
cap. An individual row can exceed the target if the resulting packet and
its index key fit. The synced writer flushes and syncs the original
descriptor. Directory sync and publication are the caller's responsibility.

## Capacity and memory

The 16 MiB limit is an encoded packet limit, including the checksum.
Data and leaf targets control ordinary packing. A single row or reference
may exceed its target up to the hard limit. The root is always one packet.
Root entries cost 40 bytes plus their fence-key length. An append that
would make the root exceed the cap fails the build. The maximum number of
leaves therefore depends on their fence-key lengths.

A writer retains pending data rows, leaf references, root references and
the current input row. Encoding also allocates packet bytes and, for variable
widths, a local offset array. An open table retains decoded root references
and the descriptor. During an in-flight operation it can also retain a
decoded leaf, a data packet and temporary checksum and decoding buffers.
Account for array capacity, object overhead and temporary copies when sizing
a process heap. The encoded limits do not establish an exact heap bound.
The caller budgets its supplier, concurrent operations and number of live
tables separately.

## Verification and status

Run `bash scripts/check-immutable-sstable.sh` with the pinned Lean toolchain,
GCC and G++ on Linux x86-64. This is part of the standard reproduction suite.
Lake builds the audited modules and the native fixture from their imports.
The focused check independently replays the compiled modules with
`leanchecker` and audits the listed theorems. The same
[shared CRC32C library](../../Codec/README.md#crc32c) supplies the pinned
Google archive to the fixture and to other Lake-native consumers.
[Lean Google CRC32C benchmark](../../../../benchmarks/sstable/checksums.md) ·
[End-to-end lookup benchmark](../../../../benchmarks/sstable/unified.md)

The [portable checksum definition](../../Codec/CRC32C.lean) fixes the
incremental CRC32C convention. The [native binding](../../Codec/CRC32C.lean)
borrows the existing Lean byte array and calls the upstream implementation.
Agreement of the native library with the logical definition is an explicit
runtime assumption. Native tests compare the two.

The kernel-checked [end-to-end theorem](Proofs/UnifiedEndToEnd.lean)
connects a successful run of the actual streaming writer with an exact
model sink to `Table.Represents` on the returned fast table. The source
must serve the bytes emitted by that run. The writer proof establishes
that every index entry describes exactly its child packet and logical row
range. Both index levels and the in-block search consume those facts.
`TypedTable.represents_of_bytes` transports the result to caller values.

This theorem concerns successful immutable reads. The reader's structural
and checksum checks reject malformed packets as they are visited. A checked
footer and CRC do not authenticate bytes or certify global key order in an
externally supplied image. The [read-safety proof](Proofs/UnifiedReadSafety.lean) compares
successful checked byte and typed lookups with the healthy reference.
It requires exact results for successful primitive calls and permits
errors on any call. The reached-state propagation on failure is covered
separately by the reader's error proofs. The [error propagation proofs](Proofs/UnifiedReadErrors.lean)
cover footer and root failures during open and failures at the leaf, data and
row probes selected by lookup, seek and iteration. They also cover caller
codec failures in typed reads. In the stateful model, an error returns the
state reached at the failed action.

The native fixtures cover all four field-width combinations, corrupt and
substituted files, truncated reads, and positional I/O failures. They also
exercise successful sync, failed sync cleanup, and an open descriptor
surviving pathname replacement. Durable publication and descriptor effects
remain assumptions of the native adapter and its caller.

## Native refinement boundary

[The composed theorem](Proofs/UnifiedNativeEndToEnd.lean) uses the schedules
executed by `buildFileSynced` and `openNativeChecked`. It derives the image
from the actual row callback and append schedule in the effect interpreter,
then ties its bytes to the inode synced through the original flushed writer.
On checked open, the reader uses the acquired descriptor for both extent and
positional reads. Its healthy read interpretation takes the bytes from the
writer's durable inode evidence. The caller supplies the binding from the
selected read descriptor to that inode and keeps it immutable while in use.

The external assumptions apply to individual operations. On the pinned Lean
runtime, `.writeNew` uses exclusive creation, a successful `Handle.write`
reports a full `fwrite`, and a successful flush completes `fflush`. The
writer owns the fresh name and byte stream, and the supplier advances its
row cursor without touching that file. On Linux the [sync bridge](../../../native/fsync.c)
uses `fileno` on that very handle. The filesystem must honor successful
`fsync` for the flushed inode contents. Neither successful file sync nor
failed-sync cleanup certifies durability of a directory entry. A reported
sync failure may follow a completed effect. The proof preserves the primary
error and runs cleanup from the reached state.

Failed acquisition remains an availability risk on pinned Lean 4.36.
If `open` succeeds and `fdopen` fails before returning a handle, the
runtime may leak a raw descriptor. Fault injection on Lean 4.37.0-rc1
confirmed that the merged fix closes the raw descriptor. Upgrade when
a stable Lean release includes the fix.
[Lean handle-acquisition fix](https://github.com/leanprover/lean4/pull/16520)

Both runtimes can leave a new unpublished name after failed exclusive
creation. Under the namespace ownership and publication contracts this
orphan is safe for data. Cleanup requires evidence that the acquisition
created and still owns the name. A general acquisition failure can also
mean an existing name was rejected and must be preserved. The open
resource-cleanup guarantee does not block this datasafety milestone.

Native open expects a path to an ordinary file in the caller's managed
namespace. The descriptor check runs after the blocking open, so a FIFO
with no writer can block before the type check.

The [read bridge](../../../native/sstable.c) checks the descriptor with
`fstat` and uses bounded `pread` on that descriptor. Successful operations
on the immutable regular inode must return its extent and requested
bytes. Short reads and errors are handled separately. The native proof
interprets these primitive effects and does not verify libc, the Linux
filesystem or CRC32C's native implementation in Lean.
[Pinned Lean I/O implementation](https://github.com/leanprover/lean4/blob/v4.36.0/src/runtime/io.cpp)

Run `bash scripts/check-sstable-l0-consumer.sh` with the pinned PR #5 revision
available locally to compile the component theorem into the real L0 typed
consumer. The native fixture checks scoped hit, tombstone, ordinary miss,
and that a packet or typed-decoding error aborts the real lookup loop.
A separate proof and fault fixture route an injected position-read failure
through a selected data packet after a newer table misses. Both preserve
the error and stop before a known older hit.
The check stages PR #5 code in a temporary checkout and adapts checked open
to accept its table ID.

## Roadmap

The [L0 adapter](https://github.com/alvoki/alvoki-lean/pull/5) supplies the
expected catalog ID, durable directory binding and file lifetime. L0 publication
and reopen must establish that the selected name resolves to the inode produced
by the builder. The caller bounds live descriptors and root buffers across tables.

A candidate shared file-construction contract is the exact concatenation of
successful writes, flushed and synced on one held descriptor. SSTable would
supply multiple chunks through its writer. [DurableBlob](../DurableBlob/README.md)
would supply one whole value through its staging writer. DurableBlob opens a
reusable staging name and models the staged whole value. SSTable acquires a
fresh name and models incremental appends. Leave acquisition mode, cleanup,
rename and directory persistence with each caller. Extract the shared
descriptor contract once both proof consumers derive and use it, alongside
the work on a common filesystem model.

For the next performance iteration, measure whether a block iterator can
reuse a validated leaf and data packet across successive rows. Compare scan
time and read counts to the current indexed cursor and preserve its logical
order and end-of-table behavior. Measure packet alignment separately on
the target filesystem.
