# Proof roadmap

**The open goal is one theorem about the production sequential Linux engine.** From a fresh directory, every finite execution admitted by the filesystem contract should have one legal key-value history explaining the client’s acknowledgements, reads and reopened states. The existing induction gives that history for executions supplied with the required per-step evidence. The work below is to derive that evidence from the ordered production calls. The invariant map explains why the six public guarantees follow, and the handoff identifies the next source boundary. [Correctness argument](proofs/native-storage.md#current-system-guarantees) · [Invariant map](proofs/native-storage.md#refinement-boundaries) · [Current handoff](progress.md)

## End-to-end storage guarantees

Every acknowledged batch occurs in order. An uncertain batch may survive in full or be omitted. Every applied mutation came from a submission. Recovery must select the history before accepting submissions in the next session. One history must explain every successful point and range read at its recorded snapshot. Earlier observations still hold when a supported sequence is reacquired. Checkpoint publication, restart and reclamation must preserve this contract. Progress and space have additional resource and scheduling conditions. [Replay and trust boundaries](proof-architecture.md) · [Current executable coverage](verification-status.md#storage-engine-guarantees)

### Completion checklist for native key-value refinement

1. **Derive admitted execution from production.** Start with the engine-owned empty directory, actual request arguments, primitive returns, interruptions and reached heaps. Define admission independently of correctness reports. Derive fresh authority, then preserve the storage, descriptor, session and client-history invariants by one induction. A completed call has its actual result and successor. A pending or interrupted call has the issued operation and one reached state from which execution can end, exit, reboot or continue as appropriate. Include the terminal prefix even when recovery never succeeds. [Execution target](proofs/native-storage.md#target-execution-argument) · [Existing induction](../lean/Alvoki/Storage/Disk/Proofs/Native/Open/NativeOpenedRestartSessions.lean)
2. **Close one path before broadening coverage.** The early checkpoint pilot already connects a fresh open, acknowledged write, interrupted run-file or first directory fsync, a joint reboot sample, a failed MANIFEST open and a later read on the returned table. Use its terminal and continuation proofs for the next source-derived cut. Challenge the derivation with an ordinary error before the cut, two directory barriers on the same handle, an ambiguous second write, and a rename that can select either checkpoint. Require the same returned table, phase, token, file identities and incoming ledger throughout. [Pilot and acceptance test](proofs/native-storage.md#migration-test) · [Checked pilot](../lean/Alvoki/Storage/Disk/Proofs/Native/Checkpoint/NativeFreshCheckpointReplay.lean)
3. **Complete marked and initial open.** At the current long-keeper boundary, a failed rename or a returned rename followed by a directory-sync error identifies the completed repair prefix. Next derive the failed scratch-file fsync and the preceding stage and cache calls from the worker itself. Extend the same return, cleanup and stop rules to remaining pre-lock and held-admission failures, fresh or reused keeper bootstrap, initial marker creation and its crash survivors, stale-stage collision, detach and retry, selected metadata and payload read failures, pruning, repair and installation. Include nonregular entries, corrupt or truncated bytes, identity mismatches, allocation failures and effects from finalizers. A failed attempt may have changed the files or retained the lock. Feed its exact files, released or surviving owner, diagnostic and census into any later attempt. [Measured repair](../lean/Alvoki/Storage/Disk/Proofs/Keeper/NativeLongKeeperFinalSyncObservation.lean) · [Open dispatch](../lean/Alvoki/Storage/Disk/Proofs/Native/Open/NativeHealthyMarkedTableOpen.lean)
4. **Connect remaining mutations to restart.** For writes, cover remaining partial append and marker-stage boundaries, grouped file sync and publication cuts. For rotation, cover early create and file-sync errors and interruptions as well as the final directory barrier. For checkpoint, carry the remaining run-write and run-sync cuts, staged-manifest cuts and old/new manifest outcomes through the shared reopen proof. Carry the selected nonempty WAL suffix where a local checkpoint adapter assumes it empty. Preserve the precise issued request, poisoned phase, every earlier response and each old-or-whole decision. Exercise process exit without power loss, delayed effects, further power losses and intervening failed or mutating opens before the next successful read or write. [Write selection](../lean/Alvoki/Storage/Disk/Proofs/Write/NativeLateWriteRecovery.lean) · [Checkpoint recovery](../lean/Alvoki/Storage/Disk/Proofs/Checkpoint/NativeCheckpointSampledTableOpen.lean)
5. **Finish handle lifecycle and maintenance.** Connect rotation, covered-WAL and obsolete-run collection, row retention, close and their remaining errors and stops on the exact returned references. Preserve snapshot pin registration, floor checks, point and range results, token comparisons and the exact errors for foreign, released, closed and poisoned handles, including calls on an old handle after a later reopen. Carry partially completed maintenance through close, exit, failed opens and recovery. A retained file description can outlive its issuing process or the pathname it opened. [Inactive-session calls](../lean/Alvoki/Storage/Disk/Proofs/Native/Execution/NativeInactiveSessionCalls.lean) · [Reclamation contract](#garbage-collection-contract)
6. **Prove conditional progress and bounds.** For each reachable recoverable state, prove that the required successful primitive returns, available lock and sufficient resources yield a completed installation. With no intervening writes, a later crash and healthy reopen preserve the same data. Give distinct outcomes for persistent corruption and resource exhaustion. Establish the work and retained-space bounds below under explicit maintenance and filesystem conditions. [Recovery progress](../lean/Alvoki/Storage/Disk/Proofs/Recovery/CachedRecoveryProgress.lean) · [Performance requirements](#performance-requirements-for-verified-paths)

A branch closes when the real call establishes the local invariant and its consumer can use it at the reached heap. Review the exact claim, its assumptions and executable coverage. Run the stock kernel and axiom checks, including the negative control, the relevant native fault regressions and reproduction. Preserve independent fixtures, including a changed working directory, descriptor reuse, and a failed directory sync followed by retry. Compare emitted production code for proof-only changes. [Proof-engineering guidance](proof-index.md#how-to-structure-a-proof) · [Correctness checks](../scripts/check-sequential.sh)

## Disk guarantees to prove

### Filesystem assumptions and detailed proof targets

The source proof must derive the selected files and session from the reached primitive effects. The contract specifies inode and directory barriers, failed calls with effects, descriptor lifetime and the resource assumptions. [Full contract](proofs/filesystem.md)

**Recovery work.** The measured marked worker has a bound of nine fixed adapter requests plus two per decoded manifest run and two per recognized WAL entry. [Adapter request bound](../lean/Alvoki/Storage/Disk/Proofs/WAL/WalSegmentCachedOpenWork.lean#L179)

With stable binding and the stated size bounds, manifest acquisition reads the 48-byte header, declared run stamps and at most one trailing byte. [Bounded manifest reader](../lean/Alvoki/Storage/Disk/ManifestAcquisition.lean#L16)

Marker acquisition reads at most 25 logical bytes in at most 25 primitive reads. The selected WAL interval bounds payload bytes and frame checks. With `n ≤ 2^k`, the pinned extent sort uses at most `n × k` comparisons. Assembly copies each selected segment at most once and can reuse a single exact-sized segment. Through the marker, the reader checks format and ordinal at most once per retained frame, including the first failure. Replay attempts each frame above the checkpoint watermark at most once. To obtain an end-to-end bound, include unsuccessful attempts, raw/unmanaged and empty entries, pathname sizes and parsing, descriptor operations and cleanup, allocation, replay insertions, retained memory and runtime/syscall work. Distinguish adapter requests, bytes, primitive calls and elapsed time. [Marked recovery work](../lean/Alvoki/Storage/Disk/Proofs/Recovery/NativeMarkedRecoveryWork.lean) · [Inventory work](../lean/Alvoki/Storage/Disk/Proofs/WAL/WalInventoryWork.lean) · [Maintenance frame budget](../lean/Alvoki/Storage/Disk/Proofs/Native/Recovery/NativeMaintenanceFrameBudget.lean)

**Additional public contracts.** A durable request ID would let the caller retry an ambiguous submission without applying it again. Specify the retention window and what happens when the same ID carries a different request, then prove replay returns the original result. For online backup, show that the backup restores one snapshot and its independent file protections survive checkpoint publication and maintenance until completion. [Engine roadmap](roadmap.md)

### Garbage collection contract

Collection must preserve every selectable checkpoint, its required WAL and all supported snapshot reads. Progress requires scheduled successful collection. A physical block bound additionally needs inode lifetime and allocation evidence. [Full contract](proofs/reclamation.md)

### Performance requirements for verified paths

Keep histories, invariants and proof witnesses out of the runtime path. Executable validation, stored metadata and computations producing runtime values still have a cost. Refine existing packed or machine-indexed kernels. Use packed compaction for row retention and file metadata for file eligibility. Once a cheaper executable drop rule is proved, use exhaustive logical purge as the test oracle.

For changes that alter runtime work, compare the affected native release reads, writes, compaction, checkpoint or replay on the same machine and inspect generated hot-loop code. For reclamation, measure retained bytes, replay work and foreground latency under sustained writes and checkpoints, during collection and with long-lived snapshots. Record the measured tradeoff before accepting a regression in a default path. [Performance baseline](performance/performance-baseline.md) · [Benchmark workloads](performance/benchmarks.md) · [Lean performance guide](performance/high-performance-lean.md)

## Codec guarantees we already have

The stock v1 canonical codec, checked packed lookup and range, merge and writer equivalences give higher layers a shared executable contract. Use the verification inventory for exact entry points, machine-size assumptions and theorem names. [Storage and codec coverage](verification-status.md) · [Compaction and scans](experiments/compaction.md)

## Versioned compaction and its codec

### Logical histories and retention

Snapshot reads use the latest eligible version and give the right input precedence on a tie. Retention preserves supported snapshots by keeping newer rows and a floor anchor where needed, including a tombstone. [Logical history](../lean/Alvoki/Compaction/Model.lean) · [Compaction proofs](../lean/Alvoki/Storage/Proofs/Table/Compaction.lean)

### Executable v3 format and kernels

The checked compaction writers agree on the bytes of the retained rows. Snapshot scans over the encoded data must continue to agree with logical reads as new kernels are promoted. [Executable codec](../lean/Alvoki/Compaction/Codec.lean) · [Compaction contract](experiments/compaction.md)

## V1 API and codec contracts

A supported v2 columnar encoder needs full round trips, complete acceptance and rejection coverage, and identical lookup and scan results for equivalent columnar and interleaved data. If checksums are introduced, specify coverage, placement and detectable corruption. If framing becomes streaming, prove exact byte consumption and rejection of truncation before a full record. [Format specifications](specifications.md)

## Refine alternative paths when they become supported

| Promotion candidate | Required refinement |
|---|---|
| Prepared replay and online coalescing | Validate source ranges, exact bytes and order. Grouping adjacent slices and each promoted writer must agree with checked streaming replay. |
| Disjoint merge, eager spans, comparison-selected scan | Match the existing merge or direct fold, including empty inputs and adjacent touching ranges. |
| Packed value transforms | Preserve input key order and unaffected bytes, establish the specified value transform and prove output parses. |
| Native fixed-width copy or scoped builder | Prove guard bounds, overlap and exclusivity, exact output and length, alias preservation, initialized bytes and stock fallback. State compiler, runtime and ABI premises. |
| Shipped Rust kernels | Apply the shared format and snapshot specification to the shipped code. Connect packed operations to verified search and prove the semantics and safety of enabled unsafe kernels. |

Benchmark-only paths retain exact-output differential tests and code-generation checks. [Fast-path refinement](experiments/fast-path-refinement.md) · [Scoped builder](experiments/scoped-builder.md) · [Rust search core](../verus/search.rs)

## Carry the proofs into storage-engine features

- If indexes or filters become supported, show that the index includes every eligible record, a negative filter cannot hide a present key under its construction assumptions, and indexed reads agree with reference scans.
- Specify isolation before adding concurrent readers, writers, background compaction and transactions. Prove snapshot lifecycle, atomic effects, visibility and conflict rules under that specification. Strict serializability is a separate possible target.
- For remote storage, specify consistency and publication guarantees, then prove version selection and recovery. For reactive views, show that incremental materialization equals full recomputation at the same snapshot under the stated event order and replay rules. [Engine roadmap](roadmap.md)
