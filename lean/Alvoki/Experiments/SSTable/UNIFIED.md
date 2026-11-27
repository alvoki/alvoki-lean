# Unified SSTable prototype

`ALVSST05` uses one index and reader for fixed or variable key and value
widths. The writer validates declared widths and strictly increasing byte
keys. The reader compares the independent expected table ID with the
checked footer before loading the root.

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

Local offsets include an end offset. The current prototype encodes lengths
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

Run `bash scripts/check-unified-sstable.sh` with the pinned Lean toolchain,
GCC and G++ on Linux x86-64. The opt-in runner builds Google CRC32C 1.1.2 from
pinned source using upstream's SSE4.2 dispatch and portable fallback. It can
use an already checked-out copy via `CRC32C_DIR`. The normal checks for
existing formats require no new dependency.
[Direct Lean checksum comparison](../../../../benchmarks/sstable/checksums.md) ·
[End-to-end lookup benchmark](../../../../benchmarks/sstable/unified.md)

The [portable checksum definition](UnifiedIntegrity.lean) fixes the
incremental CRC32C convention. The [native binding](UnifiedNativeIntegrity.lean)
borrows the existing Lean byte array and calls the upstream implementation.
Agreement of the native library with the logical definition is an explicit
runtime assumption. Native tests compare the two.

The prototype implements the logical lookup, seek and indexed iteration
semantics exercised by the fixtures. The producer-to-reader proof for its
actual handle remains open. In particular, the writer must establish that
the persisted references partition the supplied rows and give exactly each
child's last key. That supplies the premise for reusing the lower-bound
proof at both index levels. Keep the prototype out of the default reader
until that proof and the native adapter boundary are reviewed.
