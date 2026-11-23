# Proof roadmap

Start with snapshot preservation for versioned compaction. Connect that law to the v3 parser, writers, and readers. Finish the v1 public API alongside that work by composing the codec, search, and merge theorems. These two tracks turn the proofs we already have into guarantees about what callers can read. [Current proof inventory](verification-status.md) · [Engine roadmap](roadmap.md)

## Codec guarantees we already have

| Code | Kernel-checked guarantee |
|---|---|
| `splitByte`, `joinBytes`, `pushWordFast`, and `word` | Joining the eight little-endian lanes of a word recovers the word. Extracting a lane after joining recovers that byte for lanes 0 through 7. Reading at the old length after appending a word returns that word, for any prefix. |
| `wordFast`, `wordMachine`, and checked packed access | `wordFast` agrees with `word`. The machine-offset reader agrees with the byte reader when the word extent is in bounds and the array size fits. Checked record access agrees with the logical record at its index and returns `none` outside the run. |
| `encodeV1` → `parseRun` → `Run.decodeV1` | For a strictly ordered record array whose count fits a 64-bit word and whose full byte length fits the parser's machine bound, parsing succeeds and decoding returns the exact input array. |
| `parseRun` → `Run.decodeV1` → `encodeV1` | Every accepted v1 block re-encodes to its exact original bytes, including header and payload. |
| `parseView` and `View.logicalRecord` | Acceptance preserves the input bytes, count, version, and layout. Logical keys are strictly ordered. The record-offset theorems cover interleaved v1 and columnar v2 layouts. |
| `ScopedBytes.Builder` | Appending a valid slice preserves the prefix and adds its exact bytes. Appending a list of slices agrees with their ordered concatenation, and combining adjacent slices preserves the bytes. |

The full-block round trips name the executable codec in `BlockCodec`. The baseline `Block.encode` and `Block.decode`, and the scalar and indexed benchmark codecs, have separate implementations and fixtures. Proving their equivalence would extend coverage to those entry points. The v3 experiment has bounds and progress proofs and differential tests for its parser, writers, and snapshot scans. [Word proofs](../lean/Proofs.lean) · [Packed reader proofs](../lean/PackedViewProofs.lean) · [v1 round trips](../lean/BlockCodec.lean) · [v3 experiment](compaction.md)

## Versioned compaction and its codec

### Prove the retention law on logical entries

- [ ] Define a history and a reference read for a key at a snapshot. The largest visible sequence wins, the right-hand input wins exact key-and-sequence ties, and a visible tombstone yields absence. Specify the precedence of any older runs in the read context.
- [ ] After resolving key-and-sequence ties, prove that retaining all rows above the floor and the first row at or below it preserves the result for **every key and every snapshot at or above that floor**. Include puts, deletes, reinserts, equal-sequence ties, empty runs, and the sequence-number endpoints. Prove that the retained sequence is sorted and has unique key-and-sequence pairs.
- [ ] Lift preservation to a context containing older runs. The proof must account for boundary tombstones masking those runs and for the precedence of the replacement run. Reapplying retention at a higher floor should preserve the reads still supported by the higher floor. [Versioned semantics](compaction.md#format-and-visibility)

### Connect the executable v3 format and kernels

- [ ] Define a byte-level validity predicate independently of the parser. Specify the exact header, count and length, unsigned little-endian field offsets, key-ascending and sequence-descending order, and valid put and tombstone representations. Prove that `Compaction.parse` succeeds exactly for these bytes under the machine-size bound. Derive named rejection cases for malformed headers, lengths, order, duplicate pairs, tags, and tombstone payloads.
- [ ] Give v3 a reference encoder and decoder. Prove both round trips, including byte-for-byte canonical re-encoding of accepted inputs. Prove that packed field reads agree with the decoded entry and that source ranges for copied rows fit their buffers.
- [ ] Prove that `compact` and `compactSpans` produce exactly the reference encoding of the retained entries. This connects the selection loop, coalesced copies, and rewritten header to one contract. Derive output parser acceptance.
- [ ] Prove that `Compaction.scan` and the materialized-run scan fold over the exact ordered visible rows. Derive equality of their checksum results for supported snapshots, and use the stronger row-level theorem for any future iterator. [v3 executable paths](../lean/Compaction.lean) · [Existing slice proofs](../lean/ScopedBytesProofs.lean)

## Complete the v1 API and codec contracts

- [ ] **State the parser contract as one equivalence.** Package the existing acceptance facts and round trips into `parseRun` succeeds iff the bytes satisfy the v1 format and machine bounds. Corollaries should cover malformed headers, unknown versions, count/length disagreement, truncation, trailing bytes, duplicate keys, and unsorted keys. Derive uniqueness of the encoding and injectivity on valid record arrays. These are mostly consequences of existing results.
- [ ] **Prove actual lookup and range behavior.** For a parsed run, `Run.lookup` returns exactly the decoded entry for an existing key and `none` for an absent key. The executable range fold consumes exactly the decoded rows in the half-open range, in increasing key order. Derive `rangeChecksum` from that fold, including empty and reversed intervals.
- [ ] **Prove the public merge law.** Show that the reference union is sorted and unique and has exactly the keys of either input. Show that its values agree with right-preferred map union. Connect its byte representation to `encodeV1` so that, when the output fits, the actual merge parses and lookup on it obeys that law. The adaptive and bounded-window writers and checked streaming replay inherit the result through existing equality theorems.
- [ ] **Refine the codec paths we choose to support.** Compare baseline and optimized encoders to `encodeV1` and materializing or streaming decoders to `Run.decodeV1` or its exact fold. For indexed writing, prove length and untouched-byte preservation, exact little-endian data in the target interval, the specified fallback, and absence of offset wrap on valid calls. Use those lemmas to prove the whole-block output.
- [ ] **Set the supported v2 contract if we adopt the layout.** Prove complete acceptance and rejection for columnar input and cover both round trips once there is a supported v2 encoder. Prove that interleaved and columnar encodings for the same records have identical observable lookup and scan results. [v1 and v2 formats](specifications.md) · [Experimental writer paths](../lean/Optimizations.lean) · [v1 merge model](../lean/MergeModel.lean)

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

- [ ] **Sequential multi-run state.** Define the logical contents of a table with multiple runs and in-memory writes. Prove lookup and range reads against that state. Establish that flush, compaction, and run publication preserve every live snapshot. Prove that the retention floor respects snapshot acquisition and release. Reclaim tombstones only when the proof rules out exposure of a masked value in any applicable older run.
- [ ] **Persistent codecs and crash recovery.** Give WAL frames and manifests validity, round-trip, and version-compatibility contracts. Define the filesystem and crash model. Prove that restart preserves acknowledged writes, applies complete batches as specified, and safely handles partial writes and interrupted manifest publication. Establish safe and repeatable recovery before adding concurrency.
- [ ] **Indexes and filtering if adopted.** Prove that indexes identify all eligible records, that a negative filter result cannot hide a present key under the declared construction assumptions, and that indexed reads agree with reference scans.
- [ ] **Concurrency and transactions.** Specify the isolation level before proving it. Show that concurrent reads, writes, snapshot lifecycle, and background compaction refine that contract. For transactions, prove atomic effects and the chosen visibility and conflict rules.
- [ ] **Remote storage and reactive views if adopted.** Specify the object-store consistency and publication assumptions. Connect version selection and recovery to that model. Prove that incremental materialization agrees with recomputing the query at the same snapshot under the declared event-order and replay rules. [Engine roadmap](roadmap.md)

For each completed item, record the theorem on the executable entry point, its preconditions, and its remaining trusted boundaries. Add it to the kernel and axiom audit in the stock correctness workflow and preserve relevant independent fixtures. Keep performance comparisons in the benchmark suites. [Correctness command](../scripts/check.sh)
