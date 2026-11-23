# Immutable sorted block, version 1

Every field is an unsigned 64-bit little-endian integer. The format has no padding and imposes no address alignment requirement.

| Byte offset | Field |
|---:|---|
| 0 | Record count `n` |
| 8 | Format version, exactly 1 |
| `16 + 16*i` | Key of record `i` |
| `24 + 16*i` | Value of record `i` |

The byte length must be exactly `16 + 16*n`. Keys are strictly increasing in unsigned order. Empty blocks and the full `u64` domain are valid. The parser rejects short headers, unknown versions, truncated or trailing records, count mismatches, duplicate keys and out-of-order keys. It derives the maximum record count from the actual payload before comparing the header count. There is no checksum.

The encoder expects strictly ordered input. Parsing performs the order check. Lower bound returns the first index with a key greater than or equal to the target, or `n`. Point lookup returns the associated value if the lower-bound key is equal to the target. A scan over `[start, end)` walks from the lower bound of `start` to the lower bound of `end` in record order. Equal or reversed endpoints yield no records. An exclusive upper endpoint of `u64::MAX` excludes that key. The benchmark chooses `end` by saturating addition from each query's key and declared width.

## Experimental version 2

The optimization suite also reads a columnar block. It uses the same 16-byte header, with version set to 2 and the same total byte length. Keys occupy one contiguous region at offsets `16 + 8*i`. Values start at `16 + 8*n` and occupy offsets `16 + 8*n + 8*i`. Key and value at the same index form a record. Validation, lookup, and range semantics are the same as in version 1.

Version 2 is exercised through the separate optimization binaries. The experimental encoders produce version 1.

## Version-1 run merge

Given two valid version-1 runs, a materialized merge produces a version-1 block containing each key in either input exactly once, in strictly increasing unsigned order. When a key is present in both inputs, the output uses the right input's value. Otherwise it uses the value from the only input containing that key. Either run may be empty.

The direct merged checksum scan consumes the same logical records without producing a block. It sums each record's key XOR value with wrapping 64-bit addition. The replay benchmark accepts a supplied sequence of cursor moves only when each move matches the ordered, right-biased choice at the two current heads and the moves consume both runs completely. [Verification status](verification-status.md)

## Experimental versioned runs

The compaction experiment uses version 3, with a sequence and kind field for each entry. The workload specifies tombstone precedence, retention at the oldest snapshot, and visibility for later reads. [Versioned format and visibility](compaction.md#format-and-visibility)

## WAL and checkpoint manifest

Each frame and manifest occupies exactly 48 bytes. All fields use unsigned 64-bit little-endian words. The checksum is 64-bit FNV-1a over the first 40 bytes in storage order, with wrapping multiplication. It detects ordinary corruption and has no cryptographic guarantee.

| Byte offset | WAL frame | Checkpoint manifest |
|---:|---|---|
| 0 | ASCII `ALVOWAL1` | ASCII `ALVOMNF1` |
| 8 | Write sequence | Run generation |
| 16 | Key | Committed sequence watermark |
| 24 | Kind, `0` for put and `1` for delete | Retention floor at or below the watermark |
| 32 | Value, exactly zero for a delete | Run count |
| 40 | Checksum | Checksum |

The committed part of the WAL is a concatenation of complete frames. Decode validates every frame passed to it and rejects unknown formats, bad checksums and noncanonical operation fields. Replay rejects gaps, duplicates and reordered writes in the suffix above the checkpoint watermark. The manifest indexes the ordered immutable v3 files from zero through `runCount - 1`. Opening a checkpoint requires all referenced files and verifies that their versions are at or below the watermark. [WAL codec](../lean/storage/disk/WriteAheadLog.lean) · [Manifest codec](../lean/storage/disk/Manifest.lean) · [Publication protocol](architecture.md#sequential-storage)

### Durable WAL boundary

`WAL.commit` is a 24-byte file containing three unsigned 64-bit little-endian words. They are the eight ASCII bytes `ALVOCMT1`, the committed WAL byte count, and the 64-bit FNV-1a checksum of the preceding 16 bytes. The count must be a multiple of 48 and at most the WAL file size. Reopen checks the sequence against the one-based position of every selected frame, including those covered by a checkpoint. It skips the covered frames for replay and checks that the total frame count matches the recovered sequence. If any bytes follow the committed prefix, reopen replaces the WAL with that prefix before accepting another write. Errors within the committed prefix fail recovery.

An absent `WAL.commit` denotes an empty database or a legacy directory under the stable-directory assumptions. The adapter validates the legacy WAL using its existing short-tail rule, syncs the selected prefix, and installs the initial boundary before returning from open. A legacy WAL with a malformed full frame fails validation. Use an adapter that supports `WAL.commit` after this upgrade. [Boundary codec and selector](../lean/storage/disk/WalBoundary.lean)
