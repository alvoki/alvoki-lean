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

Each WAL frame occupies 48 bytes. A checkpoint manifest has a 48-byte v2 header followed by a 16-byte integrity record for each run. All fields use unsigned 64-bit little-endian words. Checksums use 64-bit FNV-1a with wrapping multiplication.

| Byte offset | WAL frame | Checkpoint manifest v2 |
|---:|---|---|
| 0 | ASCII `ALVOWAL1` | ASCII `ALVOMNF2` |
| 8 | Write sequence | Run generation |
| 16 | Key | Committed sequence watermark |
| 24 | Kind, `0` for put and `1` for delete | Retention floor at or below the watermark |
| 32 | Value, exactly zero for a delete | Run count |
| 40 | Checksum over the first 40 bytes | Checksum over the first 40 bytes followed by the ordered integrity records |

Starting at offset 48, each manifest record stores a run's file length and checksum over its complete bytes. The records index immutable v3 run files from zero through `runCount - 1`. Open checks the recorded lengths and checksums and structurally validates the same ordered run bytes before using the checkpoint watermark. Changes confined to one payload byte change the checksum. Multiple changes can collide. [Manifest codec](../lean/Alvoki/Storage/Disk/ManifestIntegrity.lean) · [Single-byte detection](../lean/Alvoki/Storage/Disk/ManifestIntegritySingleByte.lean)

The committed part of the WAL is a concatenation of complete frames. Decode validates every frame passed to it and rejects unknown formats, bad checksums and noncanonical operation fields. Replay rejects gaps, duplicates and reordered writes in the suffix above the checkpoint watermark. [WAL codec](../lean/Alvoki/Storage/Disk/WriteAheadLog.lean) · [Publication protocol](architecture.md#sequential-storage)

### Durable WAL boundary

`WAL.commit` is a 24-byte file containing three unsigned 64-bit little-endian words. They are the eight ASCII bytes `ALVOCMT1`, the committed WAL byte count, and the 64-bit FNV-1a checksum of the preceding 16 bytes. The count must be a multiple of 48 and at most the WAL file size. Reopen checks the sequence against the one-based position of every selected frame, including those covered by a checkpoint. It skips the covered frames for replay and checks that the total frame count matches the recovered sequence. If any bytes follow the committed prefix, reopen replaces the WAL with that prefix before accepting another write. Errors within the committed prefix fail recovery.

When `WAL.commit` is absent, bootstrap requires an absent manifest and an absent or empty WAL. Open creates the empty WAL if needed, syncs it and the directory, and publishes a zero boundary. A checkpoint or nonempty WAL without a marker fails before WAL or checkpoint mutation. [Boundary codec and selector](../lean/Alvoki/Storage/Disk/WalBoundary.lean)
