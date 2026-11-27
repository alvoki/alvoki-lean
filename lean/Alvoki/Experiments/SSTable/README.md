# Immutable SSTable

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
GCC and G++ on Linux x86-64. The runner also runs in the standard reproduction suite. It builds Google CRC32C 1.1.2 from
pinned source using upstream's SSE4.2 dispatch and portable fallback. It can
use an already checked-out copy via `CRC32C_DIR`. The shell runner links the native CRC32C library. Lake builds the Lean modules, and a separate native executable using `UnifiedNative` must link the CRC32C library too.
[Lean Google CRC32C benchmark](../../../../benchmarks/sstable/checksums.md) ·
[End-to-end lookup benchmark](../../../../benchmarks/sstable/unified.md)

The [portable checksum definition](UnifiedIntegrity.lean) fixes the
incremental CRC32C convention. The [native binding](UnifiedNativeIntegrity.lean)
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
externally supplied image. The explicit [leaf-read error theorem](Proofs/UnifiedOpen.lean)
covers an error from the positional read on the selected lookup path.
The native fixtures cover all four field-width combinations, corrupt and
substituted files, truncated reads, and positional I/O failures. They also
exercise successful sync, failed sync cleanup, and an open descriptor
surviving pathname replacement. Durable publication and descriptor effects
remain assumptions of the native adapter and its caller.

## Roadmap

The component refinement milestone connects successful native build and
checked open to the model theorem. SSTable owns the proof that the row stream
produces the exact flushed bytes, that file sync acts on the original inode,
and that healthy positional reads on the acquired descriptor serve that inode.
The [L0 adapter](https://github.com/alvoki/alvoki-lean/pull/5) supplies the
expected catalog ID, durable directory binding and file lifetime. L0 publication
and reopen must establish that the selected name resolves to the inode produced
by the builder. The caller bounds live descriptors and root buffers across tables.

As part of the future work on a common filesystem model, investigate whether
durable immutable file creation and [DurableBlob](../DurableBlob/README.md)
can share streaming file construction. Compare a streaming extension of
DurableBlob with a smaller shared building block.

For the next performance iteration, measure whether a block iterator can
reuse a validated leaf and data packet across successive rows. Compare scan
time and read counts to the current indexed cursor and preserve its logical
order and end-of-table behavior. Measure packet alignment separately on
the target filesystem.
