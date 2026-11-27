# Immutable SSTable

An immutable SSTable stores strictly increasing byte-array keys with byte-array
values. Keys compare lexicographically by unsigned bytes. A strict prefix sorts
before the longer key, and lookup uses exact byte equality. Empty keys and values
are supported.

A caller can use its own key and value types by providing two explicit
[`Codec`](Contract.lean) values. Use `Entry.encode` on the build side and `TypedTable` on the read side.
For typed reads the caller needs decoding to
recover what encoding wrote. The key encoding must also preserve the caller's
order and map equal logical keys to the same bytes. For example, big-endian
unsigned integers preserve numeric order. A query can use arbitrary bytes as a
lower bound, including a prefix of an encoded key.

| Operation | Caller-visible behavior |
| --- | --- |
| `buildFile path nextRow` | Consumes one row at a time and writes to a fresh, exclusively owned path. Rejects non-increasing keys, oversized rows and output beyond the file-offset limit. Returns the row count after flushing the footer. Cleanup preserves the original build error. |
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

## Why reads agree with construction

The native writer and model run the same streaming loop, which writes each
encoded row and records its position. The format proofs connect the index and
record bytes to the input sequence. The end-to-end theorem `open_built_table`
takes a successful modeled construction and a stable source serving those
bytes. It yields the actual opened handle and
[`Table.Represents table rows`](Representation.lean). In a consumer proof,
`rep.lookup key` gives the logical value, `rep.seek key` locates the lower
bound, and `rep.next i` advances through the same ordered rows. The Linux
adapter's effects are exercised with real files and remain environmental
assumptions of the byte-level proof.
[Builder proof](Proofs/Builder.lean) · [Format](Proofs/Format.lean) ·
[Reader](Proofs/Reader.lean) · [Search](Proofs/Search.lean) ·
[Read errors](Proofs/ReadErrors.lean)

## Roadmap

A minimal LSM can build sorted, unique byte rows, publish the completed file
under its own crash protocol and use lookup, seek and iteration. The consumer
owns crash-safe publication and merging. It must bound live descriptors and
memory across the tables it retains.

Measure sequential scans, point reads and seeks before changing the physical
layout. Independently known key and value widths can permit cheaper field
access, and two fixed widths can permit direct addressing. Buffered reads and
data blocks with a sparse index are further options. Checksums for metadata or
checksums bound to position and table identity can strengthen corruption
detection while preserving the read contract.

## Verification

Run `bash scripts/check-immutable-sstable.sh` from the repository root using
the pinned toolchain and a C compiler. It kernel-checks the modules and audits
the theorems. Fixtures compare reads with literal wire bytes and a list oracle,
exercise corruption and I/O failures, and copy a streamed index larger than the
native buffer. [Deterministic tests](Tests.lean) · [Native tests](NativeTests.lean)
