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

## Verification and status

Run `bash scripts/check-immutable-sstable.sh` with the pinned Lean toolchain,
GCC and G++ on Linux x86-64. The opt-in runner builds Google CRC32C 1.1.2 from
pinned source using upstream's SSE4.2 dispatch and portable fallback. It can
use an already checked-out copy via `CRC32C_DIR`. The runner only adds the pinned CRC32C dependency for this experiment.
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

The next refinement milestone is to migrate the
[L0 adapter](https://github.com/alvoki/alvoki-lean/pull/5) to checked open.
It is complete when the L0 publication and reopen proof supplies the catalog
ID and the immutable-source premise for the actual reopened descriptor.
Work from the original write descriptor, its flush and sync, and the
directory barrier. Follow the shared native and model schedules down to
filesystem primitives as in [DurableBlob](../DurableBlob/README.md).
Publication and merging belong to L0. The caller bounds live descriptors
and root buffers across tables and measures lookup through its scoped open.

As part of the future work on a common filesystem model, investigate whether
durable immutable file creation and [DurableBlob](../DurableBlob/README.md)
can share streaming file construction. Compare a streaming extension of
DurableBlob with a smaller shared building block.

For the next performance iteration, measure whether a block iterator can
reuse a validated leaf and data packet across successive rows. Compare scan
time and read counts to the current indexed cursor and preserve its logical
order and end-of-table behavior. Measure packet alignment separately on
the target filesystem.
