# Immutable SSTable

This experiment stores a strictly increasing sequence of unsigned 64-bit keys with unsigned 64-bit values. The file starts with the eight ASCII bytes `ALVSST01` and a little-endian 64-bit row count. Each following 16-byte record stores its key and value in the same byte order. An empty table has just the header.

| Operation | Caller-visible behavior |
| --- | --- |
| `buildFile path nextRow` | Streams one row at a time to a fresh, exclusively owned path. Rejects duplicates, decreasing keys and counts that exceed the file-offset limit. Returns the row count after writing the final header. |
| `openNative path` | Checks the header and exact file length and retains the open descriptor. Reads 16 bytes of content. |
| `table.lookup key` | Returns the value or `none` for a missing key. |
| `table.seek key` | Binary search returns the first index with key at least the target, or the row count. |
| `table.next i` | Returns a row and the next index. At or beyond the row count it returns `none` without reading. Start at zero for a full scan. |

The native reader returns I/O and decoding errors through `EIO String`. Each row probe reads 16 bytes by descriptor and offset. If the row count is below 2^b, seek uses at most b probes. Lookup may read one more row to distinguish an exact match. [Reader](Core.lean) · [Linux adapter and streaming builder](Native.lean)

## Why reads agree with construction

1. The writer's checked push enforces increasing keys and emits one encoded row. Every accepted stream is strictly ordered, fits the offset bound, and emits its canonical image. Conversely, every ordered input within that bound is accepted. [Builder proof](Proofs/Builder.lean)
2. The header recovers the row count. Each row occupies a disjoint fixed-width slice and decodes back to its input entry. The entire file fits a signed 64-bit offset. [Format and bounds](Proofs/Format.lean)
3. The end-to-end theorem `open_built_table` takes a successful construction and a stable source serving those bytes. Opening binds the returned table to the source and count. Each iteration step returns the corresponding input row. Seek partitions the input at the target key, and lookup agrees with linear search. [Source contract and reader proofs](Proofs/Reader.lean) · [Search and probe bound](Proofs/Search.lean)

The caller keeps the file immutable while any table handle is live. Open detects a malformed header, an unsupported count and a size mismatch. Reads detect short records and propagate backend errors. Same-length value changes, key substitutions and reordered records can pass these checks. There is no checksum or whole-file ordering scan. The native writer's file effects and the operating system's positional-read implementation are exercised with real files and remain environmental assumptions of the byte-level proof. Crash-safe publication belongs to the caller.

## Verification

From the repository root run `bash scripts/check-immutable-sstable.sh` with the pinned Lean toolchain and a C compiler. It kernel-checks the modules, audits the public theorems, runs a hand-encoded fixture and an independent list oracle, then exercises streaming construction and positional reads on Linux. [Deterministic tests](Tests.lean) · [Native tests](NativeTests.lean)
