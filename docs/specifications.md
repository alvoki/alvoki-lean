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

Alvoki is pre-release and has one active encoding per on-disk artifact. The run version and checkpoint manifest version label independent encodings. The version-1 run layout above is used by the codec and merge experiments. Changes to the active format can remove obsolete readers, proof branches, and fixtures without a migration path.

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

Starting at offset 48, each manifest record stores a run's file length followed by the checksum over its complete bytes. The manifest length is exactly `48 + 16*runCount`. Records describe the v3 files in increasing index order for the named generation. The native reader accepts a v2 manifest or absence. It checks the recorded lengths and checksums and structurally validates the same ordered run bytes, including that row sequences stay at or below the watermark. Changes confined to one byte in a run change its checksum. Multiple changes can collide. [Manifest codec](../lean/Alvoki/Storage/Disk/ManifestIntegrity.lean) · [Single-byte detection](../lean/Alvoki/Storage/Disk/Proofs/Session/ManifestIntegritySingleByte.lean)

The commit marker selects a prefix of complete WAL frames. Frame decoding checks the format, checksum, and canonical operation fields. Recovery checks consecutive write sequences before replay. [WAL codec](../lean/Alvoki/Storage/Disk/WriteAheadLog.lean) · [Publication protocol](architecture.md#sequential-storage)

### Durable WAL boundary

`WAL.commit` is a 24-byte file containing three unsigned 64-bit little-endian words. They are the eight ASCII bytes `ALVOCMT1`, the absolute committed WAL byte count, and the 64-bit FNV-1a checksum of the preceding 16 bytes. The count is a multiple of 48. Dividing by 48 gives the number of committed frames since bootstrap, including frames below the checkpoint watermark.

Canonical segment names are `WAL-segment-<first>`, where `first` is the number of frames before that file. Its first frame has ordinal `first + 1`. During reopen every listed canonical segment, including names after the committed boundary, must be a regular file with exactly one hard link. An existing `LOCK` must also be a regular file with exactly one hard link. A sealed segment's length is exactly 48 times the gap to the next selected start. Reopen begins at the greatest available start at or below the checkpoint watermark, checks every required frame's absolute ordinal, and replays the frames above that watermark. The greatest start at or below `markerBytes / 48` is the keeper. An empty keeper at that frame offset is valid. The keeper must contain all frames needed through the marker. Repair can remove its bytes beyond the marker and later segment names, leaving every required earlier segment intact. [Segment names and selection](../lean/Alvoki/Storage/Disk/WalSegmentFileName.lean) · [Segment validation](../lean/Alvoki/Storage/Disk/WalSegmentReplay.lean)

When `WAL.commit` is absent, bootstrap requires an absent checkpoint and no other engine data beyond an absent or empty `WAL-segment-0`. A regular leftover `WAL.commit.next` may accompany that existing empty segment. Open syncs the empty segment and directory before publishing the zero marker. The presence of the old flat `WAL` binding is an error for this layout. [Bootstrap and marker dispatch](../lean/Alvoki/Storage/Disk/DiskTable.lean)

### Durable write batches

`DiskTable.writeBatch` takes an ordered list of puts and deletes. An empty list returns the current committed sequence from a ready session and leaves disk untouched. A successful nonempty batch returns its last sequence. Each mutation receives its own consecutive sequence in list order. Explicit historical snapshots can address those individual sequences after a successful publication.

The writer prepares the entire new table before mutating the WAL. It appends all batch frames to one active segment and publishes a single marker at the end of the batch. The same barriers as for a single write apply to that publication. The grouped WAL and staged-marker sync must succeed before rename. The directory sync must succeed before the latest table becomes visible or the batch is acknowledged.

A preflight error is a rejection. A reported publication error has an unknown outcome and poisons the session until close and reopen. Under the storage model's filesystem assumptions, a surviving marker selects the previously acknowledged history or that history with the whole batch. A partly appended suffix can be removed while preserving the previous prefix. The on-disk frame and marker layouts are the same for single writes and batches. [Native batch schedule](../lean/Alvoki/Storage/Disk/DiskTable.lean) · [Preparation and replay](../lean/Alvoki/Storage/Disk/WalBatch.lean)
