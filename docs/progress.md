# Progress

The first VM experiment is implemented and reproducible. The benchmark uses version 1 blocks with sorted unique 64-bit keys and 64-bit values. Both Lean variants and Rust pass the same deterministic oracle checks and reject the malformed fixtures. The initial Lean and Verus proofs cover binary-search properties and Lean additionally proves one packed-word round trip. See the verification status for exact boundaries.

Raw timings, native build output, proof tool output and machine details are in `benchmarks/`. Use `bash scripts/reproduce.sh` to rerun the checks. Adding `--out /tmp/trials.csv` runs the benchmark again.

The next proof dependency is a parser invariant connecting adjacent packed keys to global strict order, plus a block-level codec theorem connecting both record loops. The largest performance gaps are validation and materializing decoded records. Separate scalar reads, managed-object creation, and search callback specialization before changing the format. The independent Lean4Lean binary reported an incompatible olean header. Lean's bundled `leanchecker` rechecked the proof module successfully.

## Native optimization round

The packed read path now has an experimental specialization using machine indices, unrolled proof-carrying reads, and scalar tail-recursive loops. It supports v1 interleaved blocks and a v2 columnar layout in the experiment binaries. The optimized search refines the original lower bound, and the optimized word reader agrees with the original reader on in-bounds inputs. Data, commands, and benchmark limitations are in the [optimization report](optimizations.md).

The main remaining gaps are allocation when materializing owned records and writing packed bytes. Continue refining the parser and view invariants before integrating the experimental path into the original block module.

## Packed ownership and writes

Version-1 packed ownership and 4 KiB chunks now have independent scan and lookup experiments. Direct packed merge passes exact right-biased union fixtures, and nonoverlapping inputs can copy entire payloads. A separate C-backed block encoder came close to Rust while the native indexed encoder retained a large gap. Keep the C code out of the native block paths. Follow up on contiguous spans in overlapping merge and a bulk byte-write API with a checked refinement contract. [Packed experiment results](packed-experiments.md)

## Native SIMD and output builders

Clang vectorizes the simple native Lean scan after an outer extent check. It matches the SIMD Rust scan on this VM. Span copies help longer runs and lose time on perfect alternation. Pair-wise extent checks improve fresh encoding, with a substantial gap still visible. Begin the next native round with short-span emission and eliminating repeated write-side uniqueness checks. [Native experiment results](native-experiments.md)

## Single-record emission and packed updates

The native suite now compares adaptive span gating, cached merge heads and pre-sized record copies. Adaptive gating preserves the mixed-span benefit and avoids most of the eager probe penalty on alternating runs. Copy-and-patch improves packed transforms, with results depending on how many bytes change. General value writes and alternating merge remain the largest measured gaps in these workloads. [Emission experiment results](emission-experiments.md)

## Merge phase isolation

A shared winner trace separates replay writes from online merge selection. At one million input records, Lean selection with checksum is within 18% of Rust, while replaying 16-byte writes takes roughly 4.2–4.6× Rust time. Prioritize a fixed-width emission microbenchmark and compiler or runtime specialization. [Phase isolation results](merge-phases.md)

## Fixed-width copy specialization

A checked runtime wrapper and a generated-code inline variant accelerate constant-width packed copies without changing Lean application code. Inlining reduced the alternating pipeline from 12.79 to 9.80 ms on the VM, with Rust at 7.72 ms. The remaining 16-byte gap motivates amortizing the ownership and extent checks across a builder loop. [Fixed-width copy results](fixed-copy.md)

## Scoped output

A separate runtime lowering fills an exclusively owned packed destination for an entire loop. The best scoped variant per workload was at most 8% slower than the fastest Rust control at one million inputs on all measured write and packed-pipeline cases. Stock Lean retains the write gap. The open engineering work is to expose an equivalent safe builder contract through the standard compiler or runtime and establish refinement. [Scoped builder results](scoped-builder.md)

## Proved stock Lean builder

Stock Lean now builds and checks an append-only packed builder, including exact prefix, source-byte, length, batch and streaming-replay contracts. Online span emission helps clustered traces, while alternating writes still spend one runtime slice-copy call per record and lag the Rust scoped control. The verified builder provides an implementation contract for future standard toolchain optimization. [Proof and benchmark results](stock-builder.md)

## Fused spans and direct scans

The bounded-window fused builder cut clustered merge time from 1.23 to 1.07 ms at one million records, with the prior adaptive baseline faster on the clustered pipeline and most other merges. Direct scanning was substantially faster on alternating, shuffled and update-heavy profiles and avoided a separate packed output. [Timing and memory comparison](fused-merge.md)

## Performance guide and repository review

The performance guide synthesizes the stock Lean techniques, the workload trade-offs, and the native prototype results. The repository review maps the module and proof boundaries and proposes a unified correctness gate, a validated v1 run API, and a shared merge specification. All nine fixture or proof suites passed during the review. Small counterexamples confirmed the current replay, index, and Python assertion boundaries. [Performance guide](high-performance-lean.md) · [Review and recommended order](repository-review.md)

## Review fixes

Replay validation now checks the two current keys at each step. Both languages reject the out-of-order and false-collision counterexamples. The stock Lean run API checks natural-number indices before converting them to machine width. Rust offers checked access and rejects invalid indices before offset arithmetic. A shared benchmark support module refuses to run with Python assertions disabled.

The default Lean build includes the validated v1 run library. Parser and search refinements verify the logical records of an accepted view. The stock per-record merge and branching direct scan refine the same right-biased union. Generic builder proofs now build independently of replay. The stock and opt-in runtime correctness commands passed after a fresh checksum-verified bootstrap. [Current architecture](architecture.md) · [Proof coverage](verification-status.md) · [Correctness command](../scripts/check.sh)

A proven byte cursor removed repeated key offset and extent work from validation. In the interleaved before-and-after run, v1 validation moved from 0.447 to 0.281 ms at one million records. The fused suite now includes a Rust span-copy control with the same probe and window policy. [Review follow-up and measurements](review-follow-up.md)

## Fast-path proofs and versioned compaction

Both v1 codec round trips check. The shared span writer proves the adaptive and bounded-window policies emit the right-biased union. Accepted traces have the union's row count and payload, and checked streaming replay writes its exact bytes. The scalar kernels now use checked record bounds and the proved direct scan has a stable entry point in `PackedRun`. [Fast-path audit and regression timings](fast-path-refinement.md)

The v3 experiment models updates, tombstones, and snapshot retention over two in-memory runs. Lean's direct scans were near Rust latency and the stock materializer took 1.50–2.02× Rust time at one million inputs. The fixed-width candidate reduced per-row writing time by 27–42%, with smaller effects after span coalescing. The stock and opt-in correctness suites passed. [Compaction semantics and measurements](compaction.md)

## Proof roadmap

The roadmap records the executable v1 codec guarantees and the remaining proof obligations. It prioritizes the v3 snapshot preservation law and its connection to the parser and compaction paths, alongside completing the v1 lookup, range, and merge API proofs. It also records the contracts needed when alternative writer paths and future engine features become supported. [Proof roadmap](proof-roadmap.md)

## Packed API and snapshot proofs

The stock v1 parser, lookup, range checksum and right-biased merge now have end-to-end contracts against decoded records. The baseline, scalar and indexed encoders emit the canonical bytes, including the indexed fallback. The indexed store proofs describe the exact written bytes, untouched positions, buffer length, and offset bounds.

Both stock v3 writers produce the reference encoding of the retained history. The parser recognizes exactly the valid v3 bytes, and both codec round trips check. For every snapshot at or above the floor the direct scan and a reparsed output consume the same ordered visible rows, including when a boundary tombstone masks an older run.

The sequential model proves flush and adjacent-run replacement preserve point and range reads in their publication context. Snapshot pins constrain floor advancement. The executable packed compactor implements the model's replacement operation. [Proof roadmap](proof-roadmap.md) · [Verification status](verification-status.md)

## Snapshot and reclamation review fixes

Floor advancement now traverses the active pin list with a checked comparison bound. The sequential snapshot table assigns fresh write sequences and uses per-acquisition handles. A retained handle has stable point and range reads across any sequence of table operations. Handles are local to one sequential table history.

Reclamation now checks the actual before and after run lists, including unmerged equal-sequence candidates. The floor and relevant version boundaries suffice to certify equality at every supported snapshot. The local sequential checker exercises the review regressions and fails on axiom dependencies outside the allowlist. [Local checks](../scripts/check-sequential.sh) · [Proof roadmap](proof-roadmap.md)

## Compaction performance handoff

The handoff records the first unmeasured experiment, a whole-loop v3 writer, and the smaller runtime and compiler alternatives. It points to the existing C prototypes, byte and snapshot contracts, pinned benchmark harness, and raw results. [Resume write-path optimization](compaction.md#resuming-write-path-optimization)

## Packed table and local durability

`PackedTable` refines the sequential snapshot model for writes, handle lifecycle, lookup, range, flush and compaction. Read workers binary-seek within packed v3 runs. Flush appends rows into a byte array and matches the canonical v3 encoding. The differential harness compares histories and reads against `SnapshotTable` in a fixed scenario and 512 generated operations. Packed reclamation remains a separate integration task. [Packed table](../lean/PackedTable.lean) · [Differential fixtures](../lean/PackedTableChecks.lean)

`DiskTable` adds checksummed WAL frames, validated manifests, immutable checkpoint generations, and Linux reopen. The codecs have byte-exact round trips. Replay proofs cover acknowledged prefixes, torn tails and the suffix above an installed checkpoint. Local fixtures cover reopen after compaction, persisted floors, malformed frames, torn-tail repair and interrupted manifest publication. The adapter keeps old runs and WAL entries. The next persistence obligations are a filesystem crash model, safe cleanup, and checksums for run payloads. [Engine API and protocol](architecture.md#sequential-storage) · [Local checks](../scripts/check-sequential.sh)

The disk proof roadmap now spells out database identity, crash and retry durability, complete checkpoint publication, corruption handling, and snapshot session isolation. The native replay benchmark measures reopening ascending, descending and shuffled WALs. The initial 20,000-record medians were 1,328 ms, 4.89 ms and 857 ms respectively. The local comparison command retains raw samples and can flag a slowdown against a saved baseline. [Disk proof obligations](proof-roadmap.md#disk-guarantees-to-prove) · [Replay benchmark](benchmarks.md#disk-replay)

The roadmap sets an end-to-end crash refinement target. The first milestone is recovery safety and progress across repeated crashes, followed by lifting snapshot guarantees to disk traces and proving safe reclamation. Later proof targets cover atomic batches and retries, resource bounds, backups, and format migration. [End-to-end storage guarantees](proof-roadmap.md#end-to-end-storage-guarantees)

Garbage collection is an implementation milestone with separate safety and progress obligations. Old runs and WAL segments can be deleted once every recoverable state is covered, and version collection must preserve supported snapshot reads. The performance criteria cover proof erasure, replay work, retained space, and foreground latency during collection. [Garbage collection contract](proof-roadmap.md#garbage-collection-contract) · [Performance requirements](proof-roadmap.md#performance-requirements-for-verified-paths)

## Disk path identity review

The adapter resolves the canonical absolute directory before taking the lock and uses it for every file role. Lean proves working-directory independence, and the native fixture verifies that a write and checkpoint stay in the locked database after changing directories. Kernel rechecking, the axiom audit, and the sequential suite passed. The review recorded native replay timings before and after the change. The adapter relies on the canonical directory staying in place while open. [Verification status](verification-status.md#packed-output-and-merge) · [Replay measurements](benchmarks.md#canonical-database-path-at-open)

The review found that `FilePath.pathExists` converts every metadata error to absence. The next recovery milestone must propagate lookup errors other than genuine absence, then make the visible WAL name and recovered prefix durable before open succeeds, including after an interrupted repair. [Disk proof obligations](proof-roadmap.md#disk-guarantees-to-prove)

## Reopen sync and lookup fixes

Open now checks WAL and manifest entries without following links, accepts absence only on `ENOENT`, and propagates other lookup errors. An aligned WAL and its directory are synced before open returns. Tail repair syncs a staged file before rename and syncs the directory before returning. Native fixtures inject repeated directory-sync failures during creation and after a repair rename, then verify that successful retry preserves acknowledged data. The audited `recoverCheckpoint_repair` theorem shows that the selected trimming operation preserves the entire replay result. [Recovery protocol](architecture.md#sequential-storage) · [Verification status](verification-status.md#packed-output-and-merge)

The release benchmark measured roughly one millisecond of added latency on a 100-record reopen. The common path uses one GNU `sync` process for both targets. The filesystem model still needs to characterize crashes and failed operations as they affect file content and directory names, including a full-length damaged final frame. [Replay measurements](benchmarks.md#wal-sync-on-successful-reopen) · [Disk proof obligations](proof-roadmap.md#disk-guarantees-to-prove)

## Atomic replacement crash model

WAL-tail repair and manifest replacement now run a shared four-step sequence. The Lean model separates synced staged bytes from the live and crash-recoverable name bindings. It proves that a successful replacement settles the new bytes and that interruption at any cut, followed by arbitrary crashes and retries, preserves the WAL replay result when the initial candidate images agree. Native checks cover each cut and the actual sync failure and retry paths. The repair benchmark and its raw before and after samples cover the changed path. [Publication proof](../lean/DiskPublicationModel.lean) · [Repair benchmark](benchmarks.md#torn-wal-repair)

The review isolated the remaining full-length torn-frame case. The codec theorem shows that a full invalid frame after valid records causes rejection. The next recovery proof needs the append and acknowledgment model and a durable boundary for selecting the bytes that must replay. [Disk proof obligations](proof-roadmap.md#disk-guarantees-to-prove)

## Durable WAL boundary and checkpoint review

`WAL.commit` selects the synced replay prefix. The Linux adapter publishes it after syncing the WAL and staged marker, and acknowledges after directory sync. The checked model shows that interruptions can select the old boundary or the complete new append. A successful publication fixes the new boundary. Native fixtures cover a full-sized damaged tail, a complete unacknowledged frame, corruption inside the boundary, migration, and failures on both sides of rename. [Append and publication proofs](../lean/WalBoundaryModel.lean) · [WAL format](specifications.md#durable-wal-boundary)

The release median rose from 1.28 to 3.11 milliseconds per acknowledged write. This makes publication cost a concrete target for durable batches. The delegated review found that duplicate sequences in checksum-valid frames already covered by a checkpoint can pass the frame-count check. Replay currently verifies consecutive sequences above the checkpoint watermark. Whole-WAL sequence validation and the combined checkpoint and WAL crash proof remain open. [Measurements](benchmarks.md#durable-wal-boundary) · [Disk proof obligations](proof-roadmap.md#disk-guarantees-to-prove)

## Checkpoint publication model

The native adapter and Lean model now share the checkpoint publication schedule. At a fixed synced WAL watermark, the model proves exact run-set durability for every live or crash-selectable manifest through repeated interrupted publication and reopen. The recovery composition proves the actual byte selector, run loader, and frame-count guard succeed for the corresponding ordered WAL history. Native fixtures inject failures at run syncs and directory barriers and verify recovery after orphan generation reuse. The Lean kernel and axiom checks, native fixtures, and reproduction suite passed. Checkpoint release medians stayed within 7% across the measured run counts. [Checkpoint proof](../lean/CheckpointPublicationModel.lean) · [Benchmarks](benchmarks.md#shared-checkpoint-publication-schedule)

The next proof should connect checkpoint issuance and successful reopen to the model's fresh-generation and fixed WAL assumptions across alternating writes and checkpoints. Checkpoint run-content integrity and whole-WAL sequence validation remain separate runtime obligations. [Proof roadmap](proof-roadmap.md#disk-guarantees-to-prove)

## WAL sync latency investigation

Delegated native measurements isolated the cost of launching GNU `sync` during each write. The durable-boundary reference took 2.58 ms per write in the paired experiment. A persistent sync-only helper with rename still under the Lean lock took 0.72 ms and passed scratch fault injection. The production adapter uses the GNU sync protocol. The experiment provides a baseline for deciding whether to add a helper and for measuring future durable batches. [Measurements](benchmarks.md#wal-sync-process-overhead)

## Independent Lean readability review

The reviewer identifies changes against a pinned checkout and rechecks the exact candidate commit from the implementer's isolated branch. The first approved change uses `IO.ofExcept`, keeps partial checkpoint data separate from the installed state, and names the three crash invariant facts. A comment explains why both recovery paths sync the directory before returning a handle. The integrated proof audit, native fault checks, and reproduction suite passed. Same-machine timing checks included an interleaved rerun of the checkpoint comparison. [Agent workflow](../AGENTS.md#agent-work-and-review) · [Timings](benchmarks.md#lean-readability-review)
