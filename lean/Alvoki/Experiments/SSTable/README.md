# Immutable SSTable

An immutable SSTable stores strictly increasing byte-array keys with byte-array
values. Keys compare lexicographically by unsigned bytes. A strict prefix sorts
before the longer key, and lookup uses exact byte equality. Empty keys and values
are supported.

A caller can use its own key and value types by providing two explicit
[`Codec`](Contract.lean) values. Use `Entry.encode` on the build side and `TypedTable` on the read side.
For typed reads the caller needs decoding to
recover what encoding wrote. The key encoding must also preserve the caller's
order. The [typed refinement](Proofs/Typed.lean) derives typed lookup, seek
and iteration from the byte-level representation and these codec laws. For example, big-endian
unsigned integers preserve numeric order. A query can use arbitrary bytes as a
lower bound, including a prefix of an encoded key.

| Operation | Caller-visible behavior |
| --- | --- |
| `buildFile path nextRow` | Consumes one row at a time and writes to a fresh, exclusively owned path. Rejects non-increasing keys, oversized rows and output beyond the file-offset limit. Returns the row count after flushing the footer. Cleanup preserves the original build error. |
| `buildFileSynced path nextRow` | Builds and flushes the same image, then calls Linux `fsync` on the original output handle before returning. The caller owns directory syncing and publication. |
| `openNative path` | Reads the fixed-size footer, checks the index extent against the file size, and retains the open descriptor. |
| `table.lookup key` | Returns the value or `none` for a missing key. |
| `table.seek key` | Returns the first index with key at least the target, or the row count. |
| `table.next i` | Returns row `i` and the next index. At or past the row count it returns `none` without reading. |

The reader returns I/O and decoding errors through `EIO String`. For a row count
below 2^b, seek uses at most b row probes. Each probe reads the pair of offsets
and then the row. Lookup may read one more row to distinguish an exact match.
[Contract](Contract.lean) · [Reader](Core.lean) · [Native adapter](Native.lean)

## File layout

```text
Start of file                                             End of file
[ Row 0 ][ Row 1 ] … [ Row n−1 ][ Offset table ][ Footer · 24 bytes ]

Row i         [ Key length · 8 B ][ Key bytes ][ Value bytes ][ FNV-1a · 8 B ]
Offset table  [ o₀ ][ o₁ ] … [ oₙ ]                     (8 bytes per offset)
Footer        [ ALVSST03 · 8 B ][ Row count · 8 B ][ Index start · 8 B ]
```

The footer's index start locates the offset table. Row `i` occupies bytes
`[oᵢ, oᵢ₊₁)`, so `oₙ` is both the end of the row data and the start of the
offset table.

- Each row contains an eight-byte key length, the key bytes, the value bytes and
  an eight-byte FNV-1a checksum of the preceding row bytes. The offset pair
  determines the total row size, so only the key length is stored. A row,
  including the length and checksum, can occupy at most 16 MiB.
- The index contains one eight-byte absolute offset for each row and one
  terminal offset equal to the start of the index.
- The 24-byte footer contains the eight ASCII bytes `ALVSST03`, the row count
  and the start of the index. Integer fields are little-endian. An empty table
  has just the terminal offset and footer. Open requires this format ID in the
  footer.

The builder writes row bytes directly to the destination and offsets to a
temporary file. It copies the completed index with a bounded buffer before
appending the footer. Memory use is bounded by row and buffer limits. The
temporary file uses eight bytes per offset.

Open checks metadata and file extent. Each visited row is checked for valid
offsets, size, field boundaries and checksum before its contents are used.
The caller keeps the file immutable while a handle is live. An unvisited
corruption may remain undiscovered. The offset table and footer have no
checksum in this format. Redirecting a probe to another intact row may pass
validation, as may a checksum collision. Crash-safe publication belongs to
the caller.

## Storage assumptions and proof boundaries

- **Successful modeled writes.** `modelBuild_ok_iff` checks the shared streaming
  schedule against a successful two-stream sink. It identifies the exact row
  bytes, offsets, footer and count. The interpretation of native writes, flush
  and scratch copying as those sink operations is an adapter assumption.
  [Builder proof](Proofs/Builder.lean)
- **Healthy immutable reads.** `open_built_table` gives
  [`Table.Represents table rows`](Representation.lean) for the returned handle,
  assuming its source serves the exact built image with successful positional
  reads. The caller keeps the file immutable while any handle is live. The
  representation gives the logical lookup, lower bound and next row, and the
  typed refinement transports those observations through the caller's codecs.
  [Reader proof](Proofs/Reader.lean) · [Typed proof](Proofs/Typed.lean)
- **Read failures and corruption.** Stateful read theorems propagate required
  probe errors, including a failed final lookup read, with their reached state.
  Format proofs establish the row roundtrip and rejection of a checksum
  mismatch. Validation is lazy and subject to the limitations above.
  [Read errors](Proofs/ReadErrors.lean) · [Format proofs](Proofs/Format.lean)
- **Persistence and crashes.** `buildFileWithSync` runs the supplied sync
  callback on the original write handle after the complete image is flushed.
  `buildFileSynced` supplies Linux `fsync`. A sync error is returned and cleanup
  is best effort. The proofs establish neither post-crash file survival nor
  the durability of the filename, cleanup, publication or recovery. The
  native adapter's effects and Linux persistence guarantees are external
  assumptions. An LSM caller owns the fresh name, directory sync, manifest
  publication and WAL policy. A shared filesystem model is future work.
  [Native adapter](Native.lean)

## Roadmap

A minimal LSM can build sorted, unique byte rows, publish the completed file
under its own crash protocol and use lookup, seek and iteration. The consumer
owns crash-safe publication and merging. It must bound live descriptors and
memory across the tables it retains.

As part of the future work on a common filesystem model, investigate whether
durable immutable file creation and [DurableBlob](../DurableBlob/README.md)
can share streaming file construction. Compare a streaming extension of
DurableBlob with a smaller shared building block.

Measure sequential scans, point reads and seeks before changing the physical
layout. Independently known key and value widths can permit cheaper field
access, and two fixed widths can permit direct addressing. Buffered reads and
data blocks with a sparse index are further options. Metadata integrity and physical optimizations are follow-up work.

## Verification

Run `bash scripts/check-immutable-sstable.sh` from the repository root using
the pinned toolchain and a C compiler. It kernel-checks the modules and audits
the theorems. Fixtures compare reads with literal wire bytes and a list oracle,
exercise corruption and I/O failures, and copy a streamed index larger than the
native buffer. [Deterministic tests](Tests.lean) · [Native tests](NativeTests.lean)
