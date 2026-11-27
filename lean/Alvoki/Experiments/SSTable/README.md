# Immutable SSTable

This experiment stores a strictly increasing sequence of unsigned 64-bit keys with unsigned 64-bit values. The file starts with the eight ASCII bytes `ALVSST02` and a little-endian 64-bit row count. Each 24-byte record stores its key, value and a 64-bit FNV-1a checksum of the preceding 16 bytes, all in little-endian order. An empty table has just the header. Opening the earlier experimental `ALVSST01` format returns a format error.

| Operation | Caller-visible behavior |
| --- | --- |
| `buildFile path nextRow` | Streams one row at a time to a fresh, exclusively owned path. Rejects duplicates, decreasing keys and counts that exceed the file-offset limit. Returns the row count after flushing the final header. A build failure preserves the original error even if removal of the incomplete file also fails. |
| `openNative path` | Checks the header and exact file length and retains the open descriptor. Reads 16 bytes of content. |
| `table.lookup key` | Returns the value or `none` for a missing key. |
| `table.seek key` | Binary search returns the first index with key at least the target, or the row count. |
| `table.next i` | Returns a row and the next index. At or beyond the row count it returns `none` without reading. Start at zero for a full scan. |

The [logical contract](Contract.lean) describes lookup, lower-bound seek and iteration over an ordered sequence. The native reader returns I/O and decoding errors through `EIO String`. Each row probe reads 24 bytes by descriptor and offset. If the row count is below 2^b, seek uses at most b probes. Lookup may read one more row to distinguish an exact match. [Reader](Core.lean) · [Linux adapter and streaming builder](Native.lean)

## Why reads agree with construction

1. The native builder and a small in-memory sink run the same streaming loop. It reserves the header, writes checked rows, flushes, rewinds, overwrites the header and flushes again. The proof follows the executable row loop directly: each accepted row advances the count, updates the last key and extends the output by its encoded bytes. On a fresh model file with successful sink operations, `modelBuild_ok_iff` proves exactly which streams succeed, the returned count and the final flushed bytes. [Builder proof](Proofs/Builder.lean)
2. The header recovers the row count. Each row occupies a disjoint fixed-width slice and decodes back to its input entry. The entire file fits a signed 64-bit offset. [Format and bounds](Proofs/Format.lean)
3. The end-to-end theorem `open_built_table` takes a successful construction and a stable source serving those bytes. It yields the actual opened handle and [`Table.Represents table rows`](Representation.lean). Carry this relation into a consumer proof: `rep.lookup key` gives the logical value, `rep.seek key` locates the lower bound, and `rep.next i` advances through the same ordered rows. A stable source is an assumption at the producer boundary. These equations describe healthy reads; the separate error theorems cover failed probes. [Source contract and reader proofs](Proofs/Reader.lean) · [Search and probe bound](Proofs/Search.lean)

The caller keeps the file immutable while any table handle is live. Open detects a malformed header, an unsupported count and a size mismatch. Reads detect short records and propagate backend errors. Validation is lazy. Each visited record is checked before its key or value is used. In the stateful read model, failure at a required probe or at the final lookup reread propagates the original error and its reached state. [Error proofs](Proofs/ReadErrors.lean)

A checksum mismatch in an unvisited record can stay undiscovered, including after a successful lookup. A collision, a replacement with a matching checksum, or swapping intact records can pass validation. The header has no separate checksum. Its magic and count are checked against the format and the file extent. The native writer's file effects and the operating system's positional-read implementation are exercised with real files and remain environmental assumptions of the byte-level proof. Crash-safe publication belongs to the caller.

## Roadmap

**For a minimal LSM.** A first UInt64 consumer can build a table from sorted, unique rows, publish the completed immutable file under its own crash protocol, then use lookup, seek and iteration. Define descriptor ownership and release on success and error, and bound memory and open handles across the tables the consumer can hold at once. Publication, file lifetime and merging results across tables belong to the caller.

**For general keys and values.** Accept opaque byte sequences and let the consumer encode composite keys, sequence numbers, tombstones or MVCC values. Choose the order before fixing the next format. Lexicographic byte comparison allows one built-in order if callers provide order-preserving key encodings. A supplied total comparator admits other encodings but must give the same order and key equality during construction and every reopen. Today’s numeric UInt64 order differs from lexicographic order on its little-endian bytes. Keep lookup, lower-bound seek and iteration specified against the chosen logical order. Choose fixed or variable widths independently for keys and values. Known widths can enable direct addressing or cheaper scans without changing those guarantees.

**Independent optimizations.** Start with reproducible measurements of sequential scans, point reads and seeks, including read sizes and peak memory. Use those results to evaluate buffered iteration, blocks with a sparse index, and block checksums bound to position and table identity. Bloom filters, compression and caching can follow independently while preserving the same read contract.

## Verification

From the repository root run `bash scripts/check-immutable-sstable.sh` with the pinned Lean toolchain and a C compiler. The script kernel-checks the modules and audits the public theorems. Its tests compare reads against a hand-encoded fixture and a list oracle, inject corruption and read failures, and exercise construction and positional reads on Linux. [Deterministic tests](Tests.lean) · [Native tests](NativeTests.lean)
