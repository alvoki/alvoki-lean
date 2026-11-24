# Binary formats and behavior

## Immutable sorted block, version 1

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

## Versioned runs, version 3

`PackedTable` uses this layout for its immutable runs. Disk checkpoints write those bytes to `run-<generation>-<index>.v3`. Each field is an unsigned 64-bit little-endian integer.

| Byte offset | Field |
|---:|---|
| 0 | Entry count `n` |
| 8 | Format version, exactly 3 |
| `16 + 32*i` | Key of entry `i` |
| `24 + 32*i` | Sequence of entry `i` |
| `32 + 32*i` | Kind, `0` for put and `1` for tombstone |
| `40 + 32*i` | Value, exactly zero for a tombstone |

The byte length must be exactly `16 + 32*n` and fit in a machine word. Keys sort in increasing unsigned order. For a given key, sequences sort in strictly decreasing order. A key and sequence pair can appear at most once per run. The run format has no internal checksum. The checkpoint manifest covers each run's complete bytes. [Executable parser](../lean/Compaction.lean) · [Codec proofs](../lean/CompactionCodec.lean)

At a snapshot, the highest sequence at or below the snapshot determines each key's value. A winning tombstone makes the key absent. When merging two runs with the same key and sequence, the right run supplies the entry. Compaction retains every version above the floor and the newest version at or below the floor for each key, including boundary tombstones that can mask older values. The table serves snapshots between its retained floor and committed sequence, inclusive. [Compaction model](../lean/CompactionModel.lean) · [Snapshot table](../lean/Alvoki/Storage/Table/SnapshotTable.lean)

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

Starting at offset 48, each manifest record stores a run's file length followed by the checksum over its complete bytes. The manifest length is exactly `48 + 16*runCount`. Records describe the v3 files in increasing index order for the named generation. The native reader accepts a v2 manifest or absence. It checks the recorded lengths and checksums and structurally validates the same ordered run bytes, including that row sequences stay at or below the watermark. Changes confined to one byte in a run change its checksum. Multiple changes can collide. [Manifest codec](../lean/Alvoki/Storage/Disk/ManifestIntegrity.lean) · [Single-byte detection](../lean/Alvoki/Storage/Disk/ManifestIntegritySingleByte.lean)

The commit marker selects a prefix of complete WAL frames. Frame decoding checks the format, checksum, and canonical operation fields. Recovery checks consecutive write sequences before replay. [WAL codec](../lean/Alvoki/Storage/Disk/WriteAheadLog.lean) · [Publication protocol](architecture.md#sequential-storage)

### Durable WAL boundary

`WAL.commit` is a 24-byte file containing three unsigned 64-bit little-endian words. They are the eight ASCII bytes `ALVOCMT1`, the committed WAL byte count, and the 64-bit FNV-1a checksum of the preceding 16 bytes. The count must be a multiple of 48 and at most the WAL file size. Reopen checks the sequence against the one-based position of every selected frame, including those covered by a checkpoint. It skips the covered frames for replay and checks that the total frame count matches the recovered sequence. If any bytes follow the committed prefix, reopen replaces the WAL with that prefix before accepting another write. Malformed frames, checksum mismatches, and unexpected sequences within the selected prefix fail recovery.

When `WAL.commit` is absent, bootstrap requires an absent manifest and an absent or empty WAL. Open creates the empty WAL if needed, syncs it and the directory, and publishes a zero boundary. A checkpoint or nonempty WAL without a marker fails before WAL or checkpoint mutation. [Boundary codec and selector](../lean/Alvoki/Storage/Disk/WalBoundary.lean)
