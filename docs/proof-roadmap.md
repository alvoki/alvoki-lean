# Proof roadmap

The stock Lean v1 API and the v3 compaction prototype now have executable codec, merge, and read refinements. The sequential table model lifts v3 retention to older and newer runs and active snapshots. Persistent storage and concurrent publication still need engine contracts and implementations. [Current proof inventory](verification-status.md) · [Engine roadmap](roadmap.md)

## Codec guarantees we already have

| Code | Kernel-checked guarantee |
|---|---|
| `splitByte`, `joinBytes`, `pushWordFast`, and `word` | Joining the eight little-endian lanes of a word recovers the word. Extracting a lane after joining recovers that byte for lanes 0 through 7. Reading at the old length after appending a word returns that word, for any prefix. |
| `wordFast`, `wordMachine`, and checked packed access | `wordFast` agrees with `word`. The machine-offset reader agrees with the byte reader when the word extent is in bounds and the array size fits. Checked record access agrees with the logical record at its index and returns `none` outside the run. |
| `encodeV1` → `parseRun` → `Run.decodeV1` | For a strictly ordered record array whose count fits a 64-bit word and whose full byte length fits the parser's machine bound, parsing succeeds and decoding returns the exact input array. |
| `parseRun` → `Run.decodeV1` → `encodeV1` | Every accepted v1 block re-encodes to its exact original bytes, including header and payload. |
| `parseView` and `View.logicalRecord` | Acceptance preserves the input bytes, count, version, and layout. Logical keys are strictly ordered. The record-offset theorems cover interleaved v1 and columnar v2 layouts. |
| `ScopedBytes.Builder` | Appending a valid slice preserves the prefix and adds its exact bytes. Appending a list of slices agrees with their ordered concatenation, and combining adjacent slices preserves the bytes. |

The full-block round trips name the executable codec in `BlockCodec`. The baseline, scalar, and indexed codec results below extend the same canonical bytes or decoded records to those entry points. Independent fixtures also check both stock v3 writers and scans. [Word proofs](../lean/Proofs.lean) · [Packed reader proofs](../lean/PackedViewProofs.lean) · [v1 round trips](../lean/BlockCodec.lean) · [v3 experiment](compaction.md)

## Versioned compaction and its codec

### Logical histories and retention

- [x] `winner_latest` proves that a snapshot selects the largest eligible sequence. `winner_union` resolves equal key-and-sequence ties in favor of the right input. `read` projects the winning value only after resolving precedence, so a winning tombstone yields absence.
- [x] `retain_key` characterizes the retained rows for each key as every row above the floor followed by the first eligible row at the floor. `winner_retain` preserves every key at every snapshot at or above the floor. The proof ranges over all `UInt64` keys and sequences, including both endpoints. `retain_ordered` and `versions_unique` preserve ordering and uniqueness.
- [x] `winner_retain_in_context` preserves the winning entry with older runs in the read context, including boundary tombstones. `winner_advanceFloor` preserves reads still supported by the higher floor. [Logical compaction theorems](../lean/CompactionModel.lean)

### Executable v3 format and kernels

- [x] `parse_iff` characterizes acceptance by exact header, count, length, machine-size bound, key and sequence ordering, and canonical tags and tombstone payloads. Named rejection theorems cover short blocks, versions, lengths, order, duplicates, tags, and nonzero tombstone payloads. [Byte validity](../lean/Compaction.lean) · [Rejection corollaries](../lean/CompactionCodec.lean)
- [x] `encodeV3_roundtrip` and `decodeV3_reencode` recover the original canonical rows and original accepted bytes respectively. The packed field refinements connect the selected positions to natural byte offsets, and `encodeV3Row_extract` proves the exact bytes of each in-bounds source slice. [Codec proofs](../lean/CompactionCodec.lean)
- [x] `compact_eq_encode` and `compactSpans_eq_encode` prove both writers emit the exact reference encoding of the retained history. `compact_roundtrip` gives parser acceptance for parsed inputs when output length fits a machine word. `compact_history` links a reparsed output to the sequential model's run replacement. [Compaction refinements](../lean/CompactionProofs.lean)
- [x] Both executable scans refine a fold over the exact visible rows in increasing key order. `compact_visibleRows_eq` proves row equality before checksumming and `compact_scan_eq` gives checksum equality at supported snapshots. [Scan refinements](../lean/CompactionProofs.lean)

## V1 API and codec contracts

- [x] **Parser and canonicality.** `parseRun_iff` characterizes v1 acceptance by the version, exact count and length, machine bound, and strict natural-offset key order. The rejection corollaries cover short headers, mismatched versions or lengths including truncation and trailing bytes, and non-increasing keys. `decodeV1_reencode` gives canonical bytes and `encodeV1_injective` makes that encoding unique on valid record arrays. [Parser and API proofs](../lean/RunProofs.lean) · [Canonical codec](../lean/BlockCodec.lean)
- [x] **Lookup and range.** `Run.lookup_some_iff` and `Run.lookup_none_iff` characterize the executable result against decoded records. `Run.rangeRows_eq` identifies the exact decoded interval in key order. `Run.rangeChecksum_eq` and `Run.rangeChecksum_empty` connect the packed loop to that list, including empty and reversed ranges. [Parser and API proofs](../lean/RunProofs.lean)
- [x] **Merge.** `mergedRecords_ordered`, `mergedKeys_unique`, and `merge_eq_encode` establish the format and ordering. `merge_roundtrip` gives acceptance when output length fits. `merge_lookup` gives right-preferred map union and `merge_lookup_absent` identifies exactly the union of input keys. The existing adaptive, bounded-window and checked streaming replay equality theorems transfer these guarantees to those paths. [Merge API proofs](../lean/RunMergeProofs.lean) · [Writer equalities](../lean/MergeProofs.lean)
- [x] **Codec variants.** The baseline, scalar and indexed encoders emit the canonical v1 bytes. The decoder theorems connect baseline, scalar and packed materialization and the streaming checksum to the decoded records. `storeWord_byte` gives exact little-endian bytes in the written interval and preserves all other positions. The indexed loop proves the full byte output, machine offset bounds and scalar fallback. [Codec equivalences](../lean/CodecVariants.lean) · [Store contracts](../lean/Optimizations.lean)
- [ ] **V2 if adopted.** The columnar layout is experimental. A supported v2 encoder would need full round trips and complete acceptance and rejection coverage. Prove interleaved and columnar encodings for the same records have identical observable lookup and scan results. [V1 and v2 formats](specifications.md)

A bit change can produce another valid v1 block. If a format gains a checksum, prove the covered bytes, placement, and reader/writer contract with explicit assumptions about detectable corruption. If a codec gains streaming framing, prove exact byte consumption and that truncated frames cannot yield complete records. [Current file formats](specifications.md)

## Refine alternative paths when they become supported

| Candidate | Proof to add before depending on it |
|---|---|
| Prepared replay and online replay coalescing | Plan construction preserves each validated move's source bytes and order. Grouping adjacent slices preserves the full stream, and each executable writer equals checked streaming replay. |
| Disjoint merge, eager spans, and comparison-selected scan | Each enabled shortcut agrees with the proved merge or direct fold, including empty inputs and boundaries where adjacent ranges touch. |
| Packed value transforms | Output parses with the same key order. Unchanged bytes are preserved and each target value satisfies the specified transform. |
| Native fixed-width copy or scoped builder | Every fast-path guard justifies the bounds, overlap and exclusivity conditions. The native implementation returns the exact bytes and length specified by the Lean contract, preserves aliases, exposes only initialized bytes, and agrees with stock behavior on fallback. Record compiler, runtime, and ABI assumptions. |
| Packed Rust as a supported engine path | Apply the shared byte-format and snapshot specifications to the Rust code actually shipped. Link its packed operations to the verified search behavior and prove the safety and semantics of any enabled unsafe kernels. |

Benchmark-only variants can retain exact-output differential tests and code-generation checks. Each promoted implementation should refine an existing contract, so higher-level proofs apply across choices. [Replay proof boundary](../lean/ReplayProofs.lean) · [Native prototypes](scoped-builder.md) · [Verified Rust search core](../verus/search.rs)

## Carry the proofs into storage-engine features

- [x] **Sequential multi-run model.** Define point and range visibility across oldest-to-newest runs and in-memory writes. Prove lookup and range preservation after flush and adjacent compaction in arbitrary older and newer contexts. Pin acquisition and release maintain the floor invariant. Floor advancement preserves all active snapshots. The model proves that purging a tombstone preserves reads if absence is preserved across the complete remaining history at every supported snapshot where it wins. [Sequential model](../lean/SequentialModel.lean)
- [ ] **Executable sequential table.** Integrate in-memory writes, the packed runs, publication and snapshot pins in an engine API. The packed compactor already refines adjacent-run replacement. Connect the engine's lookup, range, flush, and actual tombstone reclamation to the model and exercise publication across multiple runs. [Packed replacement theorem](../lean/CompactionProofs.lean)
- [ ] **Persistent codecs and crash recovery.** Give WAL frames and manifests validity, round-trip, and version-compatibility contracts. Define the filesystem and crash model. Prove that restart preserves acknowledged writes, applies complete batches as specified, and safely handles partial writes and interrupted manifest publication. Establish safe and repeatable recovery before adding concurrency.
- [ ] **Indexes and filtering if adopted.** Prove that indexes identify all eligible records, that a negative filter result cannot hide a present key under the declared construction assumptions, and that indexed reads agree with reference scans.
- [ ] **Concurrency and transactions.** Specify the isolation level before proving it. Show that concurrent reads, writes, snapshot lifecycle, and background compaction refine that contract. For transactions, prove atomic effects and the chosen visibility and conflict rules.
- [ ] **Remote storage and reactive views if adopted.** Specify the object-store consistency and publication assumptions. Connect version selection and recovery to that model. Prove that incremental materialization agrees with recomputing the query at the same snapshot under the declared event-order and replay rules. [Engine roadmap](roadmap.md)

For each completed item, record the theorem on the executable entry point, its preconditions, and its remaining trusted boundaries. Add it to the kernel and axiom audit in the stock correctness workflow and preserve relevant independent fixtures. Keep performance comparisons in the benchmark suites. [Correctness command](../scripts/check.sh)
