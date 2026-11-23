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

`PackedTable` refines the sequential snapshot model for writes, handle lifecycle, lookup, range, flush and compaction. Read workers binary-seek within packed v3 runs. Flush appends rows into a byte array and matches the canonical v3 encoding. The differential harness compares histories and reads against `SnapshotTable` in a fixed scenario and 512 generated operations. Packed reclamation remains a separate integration task. [Packed table](../lean/Alvoki/Storage/Table/PackedTable.lean) · [Differential fixtures](../lean/Alvoki/Checks/PackedTableChecks.lean)

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

WAL-tail repair and manifest replacement now run a shared four-step sequence. The Lean model separates synced staged bytes from the live and crash-recoverable name bindings. It proves that a successful replacement settles the new bytes and that interruption at any cut, followed by arbitrary crashes and retries, preserves the WAL replay result when the initial candidate images agree. Native checks cover each cut and the actual sync failure and retry paths. The repair benchmark and its raw before and after samples cover the changed path. [Publication proof](../lean/Alvoki/Storage/Publication/DiskPublicationModel.lean) · [Repair benchmark](benchmarks.md#torn-wal-repair)

The review isolated the remaining full-length torn-frame case. The codec theorem shows that a full invalid frame after valid records causes rejection. The next recovery proof needs the append and acknowledgment model and a durable boundary for selecting the bytes that must replay. [Disk proof obligations](proof-roadmap.md#disk-guarantees-to-prove)

## Durable WAL boundary and checkpoint review

`WAL.commit` selects the synced replay prefix. The Linux adapter publishes it after syncing the WAL and staged marker, and acknowledges after directory sync. The checked model shows that interruptions can select the old boundary or the complete new append. A successful publication fixes the new boundary. Native fixtures cover a full-sized damaged tail, a complete unacknowledged frame, corruption inside the boundary, migration, and failures on both sides of rename. [Append and publication proofs](../lean/Alvoki/Storage/Disk/WalBoundaryModel.lean) · [WAL format](specifications.md#durable-wal-boundary)

The release median rose from 1.28 to 3.11 milliseconds per acknowledged write. This makes publication cost a concrete target for durable batches. The delegated review found that duplicate sequences in checksum-valid frames already covered by a checkpoint can pass the frame-count check. Replay currently verifies consecutive sequences above the checkpoint watermark. Whole-WAL sequence validation and the combined checkpoint and WAL crash proof remain open. [Measurements](benchmarks.md#durable-wal-boundary) · [Disk proof obligations](proof-roadmap.md#disk-guarantees-to-prove)

## Checkpoint publication model

The native adapter and Lean model now share the checkpoint publication schedule. At a fixed synced WAL watermark, the model proves exact run-set durability for every live or crash-selectable manifest through repeated interrupted publication and reopen. The recovery composition proves the actual byte selector, run loader, and frame-count guard succeed for the corresponding ordered WAL history. Native fixtures inject failures at run syncs and directory barriers and verify recovery after orphan generation reuse. The Lean kernel and axiom checks, native fixtures, and reproduction suite passed. Checkpoint release medians stayed within 7% across the measured run counts. [Checkpoint proof](../lean/Alvoki/Storage/Publication/CheckpointPublicationModel.lean) · [Benchmarks](benchmarks.md#shared-checkpoint-publication-schedule)

The next proof should connect checkpoint issuance and successful reopen to the model's fresh-generation and fixed WAL assumptions across alternating writes and checkpoints. This milestone identified separate obligations for checkpoint run-content integrity and whole-WAL sequence validation. [Proof roadmap](proof-roadmap.md#disk-guarantees-to-prove)

## WAL sync latency investigation

Delegated native measurements isolated the cost of launching GNU `sync` during each write. The durable-boundary reference took 2.58 ms per write in the paired experiment. A persistent sync-only helper with rename still under the Lean lock took 0.72 ms and passed scratch fault injection. The production adapter uses the GNU sync protocol. The experiment provides a baseline for deciding whether to add a helper and for measuring future durable batches. [Measurements](benchmarks.md#wal-sync-process-overhead)

## Independent Lean readability review

The reviewer identifies changes against a pinned checkout and rechecks the exact candidate commit from the implementer's isolated branch. The first approved change uses `IO.ofExcept`, keeps partial checkpoint data separate from the installed state, and names the three crash invariant facts. A comment explains why both recovery paths sync the directory before returning a handle. The integrated proof audit, native fault checks, and reproduction suite passed. Same-machine timing checks included an interleaved rerun of the checkpoint comparison. [Agent workflow](../AGENTS.md#agent-work-and-review) · [Timings](benchmarks.md#lean-readability-review)

## Checkpoint generation after reopen

The checkpoint model now proves that the next generation calculated by the adapter is unreachable after reopen settles the visible manifest. The theorem covers bootstrap and an existing decoded manifest and uses the same overflow guard as the adapter. The next composition proof must establish the model's settlement and WAL coverage premises across real engine traces. [Generation proof](../lean/Alvoki/Storage/Publication/CheckpointPublicationModel.lean)

## Audit and correctness source layout

Proof audit entry points and correctness harnesses first moved under `lean/checks/`. Lake source directories preserved the flat `AxiomPolicy` and `DiskTableChecks` module names and artifact paths for that step. [Current audit and correctness sources](../lean/Alvoki/Checks/) · [Sequential proof and fixture suite](../scripts/check-sequential.sh)

## Publication source layout

The single-file and checkpoint publication modules and their models first moved under `lean/storage/publication/` with flat module names. Lake editor setup, the sequential proof and native fixture suite, and baseline reproduction passed at that stage. [Publication model](../lean/Alvoki/Storage/Publication/DiskPublicationModel.lean) · [Checkpoint model](../lean/Alvoki/Storage/Publication/CheckpointPublicationModel.lean)

## Selected WAL frame ordinals

Disk recovery checks the one-based sequence of every selected WAL frame, including those covered by a checkpoint. It checks ordinals during decoding and skips the covered prefix by length. The codec audit checks that the decoder accepts correctly numbered logs and returns only correctly numbered frames. A native fixture with a valid checkpoint and a checksum-valid duplicate below the checkpoint watermark is rejected. In seven interleaved native reopen measurements against commit `562baf5`, median ratios ranged from 0.97× to 1.02× for checkpointed logs of 2,000 to 50,000 frames and a log-only fixture of 20,000 frames. [WAL decoder](../lean/Alvoki/Storage/Disk/WriteAheadLog.lean) · [Recovery](../lean/Alvoki/Storage/Disk/Recovery.lean)

## WAL bytes selected at a modeled write cut

The audited model proves that a visible or crash-surviving marker selects the exact bytes of the acknowledged prefix or that prefix plus the interrupted write. The existing replay theorems now use this byte-level result. The next proof can feed those bytes directly into the run-set loader for the jointly selected checkpoint. [Selector proof](../lean/Alvoki/Storage/Disk/WalBoundaryModel.lean) · [Shared directory sync obligation](proof-roadmap.md#disk-guarantees-to-prove)

## Disk and table source layout

The disk adapter, codecs and recovery first moved under `lean/storage/disk/`. The sequential table models, packed table and its checked v3 run adapter moved under `lean/storage/table/`. Per-library Lake source directories kept the original flat import names for that step. [Current module map](architecture.md#lean-paths)

## Qualified storage and check imports

The storage module names now follow the source tree under `Alvoki.Storage.Disk`, `Alvoki.Storage.Table`, and `Alvoki.Storage.Publication`. Audit and fixture modules follow `Alvoki.Checks`. The audit scripts use the qualified module names, and the native executables keep the established command names. [Import examples](architecture.md#lean-paths)

## Consecutive WAL replay succeeds

The audited completeness theorem proves that replay accepts every contiguous suffix starting at the checkpoint's next sequence. Each encoded ordinal fits in `UInt64` and establishes that its write passes the overflow guard. When the covered prefix length agrees with the checkpoint watermark, the actual selected-WAL loader succeeds and its final sequence equals the number of selected frames. [Replay completeness](../lean/Alvoki/Storage/Disk/Recovery.lean)

## Combined checkpoint and WAL retry fixture

The native fixture exercises a failed checkpoint, a complete append left unacknowledged, and two failed reopen attempts followed by a successful one. It checks the sync targets and the exact selected WAL bytes, the persisted floor and retained snapshot, the acknowledged overwrite and tombstone, and reuse of the discarded sequence. The sync wrapper tests process-visible outcomes on Linux. The trace proof separately accounts for possible durable bindings after a crash. [Native fixture](../lean/Alvoki/Checks/DiskTableChecks.lean)

The crash refinement review reproduced an old handle reading and releasing a new pin with the same local ID after reopen. The roadmap now records the session identity requirement and the scope of the first crash trace proof. [Disk proof obligations](proof-roadmap.md#disk-guarantees-to-prove)

## Shared directory sync model

The proof model keeps the manifest and WAL marker in a single crash choice. Successful directory sync settles both visible bindings. A failed sync can retain the earlier possibilities or settle both. The audited retry theorem preserves any acceptance predicate that holds for the initial pairs and each possible pair added by rename. Proving that the adapter supplies that rename premise requires the WAL and checkpoint content invariants. [Directory publication model](../lean/Alvoki/Storage/Publication/DirectoryPublicationModel.lean)

## Recovery for one selected checkpoint and WAL marker

Given the exact checkpoint run bytes and a marker allowed by a modeled write cut, Lean proves that the production manifest and run loader, WAL selector and replay succeed. The selected history is the acknowledged prefix or that prefix plus the interrupted write, and its length equals the recovered sequence. The result agrees with replay of the selected suffix on the supplied checkpoint. The trace still needs to show that each reachable pair has those exact bytes and that its checkpoint represents the covered prefix of the same history. [Selected-pair recovery theorem](../lean/Alvoki/Storage/Disk/DiskRecoveryModel.lean)

## WAL replay refines abstract writes

Starting from a packed table that refines an abstract snapshot table, successful replay applies exactly the selected events' keys, values, and sequences in order and refines the resulting abstract table. The proof reuses the existing refinement of one packed write. The candidate generated byte-identical native code for `Recovery`. [Replay refinement](../lean/Alvoki/Storage/Disk/Recovery.lean)

## Reads through a newly acquired snapshot

If a recovered packed table has the same data, committed sequence and floor as a reference, every snapshot in that interval can be acquired again. Point and range reads through the returned pin match the reference at that sequence. The proof uses the actual acquire and read operations. [Snapshot reacquisition theorem](../lean/Alvoki/Storage/Table/PackedTable.lean)

## Marked WAL repair across reopen retries

Trimming to the visible marker preserves the exact selected bytes for each shorter marker. The retry model uses that fact when the visible marker covers every crash candidate. It permits the old or repaired WAL binding until the directory sync, which settles the manifest, marker and WAL names together. The theorem preserves the input to the production replay worker after each modeled retry. The adapter trace must establish the coverage premise and justify the modeled sync steps. [WAL reopen proof](../lean/Alvoki/Storage/Disk/MarkedWalReopenModel.lean)

## Preparing a write extends the WAL history

The audited proof links `prepareWrite` to the exact submitted key and value, the next ordinal, and the byte length the adapter checks before appending. The new history is consecutive and its encoding adds exactly the frame passed to the native append. The candidate generated byte-identical native code for `Recovery`. [Prepared-write proof](../lean/Alvoki/Storage/Disk/Recovery.lean)

## Abstract reads after selected-pair recovery

The selected-pair theorem now combines the executable loader and replay with abstract writes and snapshot reads. If the supplied checkpoint refines an abstract state, recovery applies exactly the selected suffix and the abstract committed sequence equals the selected frame count. A newly acquired packed pin returns the abstract point and range results at every supported snapshot. The proof still requires the pair and its checkpoint to be compatible with the same reachable history. [Selected-pair refinement](../lean/Alvoki/Storage/Disk/DiskRecoveryModel.lean)

## Disk snapshot session isolation

Every successful disk open allocates a distinct session token. Disk handles keep their token alive and the adapter checks reference identity before using the local pin ID. The native fixture rejects stale and foreign point and range reads and checks that releasing either kind of handle leaves a matching live pin active. The fixture failed on the old adapter at the stale point read. The adapter relies on Lean's runtime identity contract for live references. Paired read timings and the reproduction harness are archived. [Disk adapter](../lean/Alvoki/Storage/Disk/DiskTable.lean) · [Native fixture](../lean/Alvoki/Checks/DiskTableChecks.lean) · [Read benchmark](benchmarks.md#disk-snapshot-session-identity)

## Modeled write cuts bound surviving marker lengths

Until marker rename, the visible and every surviving marker point to the old prefix. After rename, the visible marker points to the extended prefix and every crash choice is old or extended. A crash settles the chosen marker. With the byte-limit guards, Lean proves that all of these candidates fit within the visible marker. The repair model can use the bound whenever the joint image's markers agree with that write cut. [Write-cut bound](../lean/Alvoki/Storage/Disk/WalBoundaryModel.lean) · [Repair bridge](../lean/Alvoki/Storage/Disk/MarkedWalReopenModel.lean)

## From interrupted writes to the marked reopen invariant

If each possible WAL file has a write-cut witness with the same visible marker and the corresponding crash markers, the initial marked reopen invariant follows. The actual decoded marker count identifies the old or extended encoded history and every physical candidate yields that exact prefix. The witnesses can differ in staging state. The adapter proof still needs to establish them for each real failure and crash outcome. [Write-cut validity theorem](../lean/Alvoki/Storage/Disk/DiskRecoveryModel.lean)

Every manifest and marker pair available after a modeled reopen retry was available before the first attempt. Repair and aligned sync can settle the currently visible pair, and a crash selects one of the saved pairs. This lets a combined recovery proof reuse the run-set witness for the initial pair. [Metadata pair theorem](../lean/Alvoki/Storage/Disk/MarkedWalReopenModel.lean)

## Shared reopen durability decision

The Linux adapter uses the audited `Publication.runReopen` to choose between staged WAL repair and the grouped sync of an aligned WAL and its directory. The branch equations expose the chosen action for the trace proof. Generated C retains the original staging path placement and sync calls. Median paired reopen ratios ranged from 0.992× to 1.031× across the four native workloads. Correspondence between the model's successful and failed effects and the filesystem operations remains a trace proof obligation. [Shared decision](../lean/Alvoki/Storage/Publication/DiskPublication.lean) · [Reopen timings](benchmarks.md#shared-reopen-durability-branch)

## Directory sync can take effect before an error

A native fixture verifies that the final standalone directory sync really succeeds before the wrapper returns an error. The write receives no acknowledgement. Reopen selects the extended WAL and preserves the acknowledged prefix, the checkpoint floor, and retained snapshot reads. This exercises the Linux adapter's error and retry behavior when the sync has taken effect. [Fault fixture](../lean/Alvoki/Checks/DiskTableChecks.lean)

## Abstract recovery after modeled reopen retries

For one interrupted write and a fixed matching checkpoint, the audited proof traces the final manifest and marker to the original write cut. The actual loader and selector recover the original history or the history with that one appended write. The abstract state applies the same suffix, reaches the same sequence, and agrees with point and range reads through newly acquired pins at every supported snapshot. The next adapter theorem must show that reachable filesystem states provide the physical write-cut and checkpoint witnesses and follow the modeled retry relation. [Composed recovery proof](../lean/Alvoki/Storage/Disk/DiskRecoveryModel.lean) · [Remaining trace obligations](proof-roadmap.md#disk-guarantees-to-prove)

## Grouped sync errors with partial effects

The native fixture makes the aligned reopen sync fail after actually syncing only the directory. During write publication it makes the WAL and staged-marker group fail after actually syncing only the staged marker. The active marker remains unchanged, and reopen trims the unselected append and returns the acknowledged and retained snapshot data. The ordered trace records the successful sync call before each injected error. This tests process-visible effects and retries. It leaves incidental writeback and power-loss outcomes to the filesystem contract. [Native fixture](../lean/Alvoki/Checks/DiskTableChecks.lean)

## Durable checkpoint files in recovery order

`CheckpointForRecovery.of_durable_manifest` connects the checkpoint publication invariant to the recovery loader's ordered run witness. For a published manifest, reading the modeled durable run names at its decoded generation and indices returns the exact ordered checkpoint bytes. An absent manifest supplies the empty checkpoint. The storage contract still governs whether actual reads return those bytes or report an I/O error. [Checkpoint recovery witness](../lean/Alvoki/Storage/Disk/DiskRecoveryModel.lean)

## Write-cut witnesses from ordered write effects

The write model executes the same append and publication schedules as the adapter in a monad that retains state on error. Failed append, staging or grouped sync cannot reach rename. A grouped sync error records WAL durability and staged-marker durability independently. The rename and directory sync can report an error before or after applying their effect. `runWriteEffects_hasWriteCuts` derives the existing physical and marker witnesses for every visible and crash-surviving WAL candidate. A successful execution settles the extended marker and exact encoded frame. [Write-effect model](../lean/Alvoki/Storage/Disk/WalWritePublicationModel.lean)

## Failed checkpoint read leaves the pending repair untouched

The native fixture presents a directory at an installed run path while a complete unselected WAL frame awaits repair. The run read returns `EISDIR`. A failed open issues no sync and preserves the WAL, marker, manifest and staging paths. With the exact run bytes restored, the retry follows the repair sync sequence, trims only the unselected frame, and preserves the latest and retained snapshot reads. [Read-error fixture](../lean/Alvoki/Checks/DiskTableChecks.lean)

## Reopen effects refine the retry model

The marked reopen interpreter uses the shared repair schedule and the same repair-versus-aligned decision as the adapter. Grouped sync can report an error with just the file or directory effect, with both, or with neither. The model keeps conservative WAL candidates when only some effects are known. The audited theorem projects each attempt to the retry relation and proves that a successful schedule settles the visible metadata and WAL choices. Read or validation errors in preflight leave the modeled durable state untouched. Filesystem behavior and the supplied read results remain explicit at the interface. [Reopen effect proof](../lean/Alvoki/Storage/Disk/MarkedWalReopenModel.lean)

## Shared publication file targets

The executable adapter uses `Publication.performReplacement` to select callback paths for staging, grouped file sync, rename and directory sync. An axiom-free equation exposes the exact callback order and targets for both the IO and model instantiations. The equation concerns execution order. The filesystem contract supplies the effects of each callback. Native paired measurements isolate the refactor. [Publication schedule](../lean/Alvoki/Storage/Publication/DiskPublication.lean) · [Benchmarks](benchmarks.md#shared-publication-file-and-sync-targets)

The write-effect proof now identifies the fixed manifest in every selectable metadata pair. If the modeled write reports success, every selectable pair carries the exact extended marker. Pair lineage preserves that choice across modeled reopen attempts. [Marker witnesses](../lean/Alvoki/Storage/Disk/WalWritePublicationModel.lean)

## Retry witnesses from a finite marked reopen trace

An ordered write supplies a visible marker that covers every surviving marker. Each modeled repair, partial sync and crash preserves this bound. For every later reopen attempt, the successful marker and WAL reads identify the visible inputs. The actual selector and the preserved bound supply the repair choice whenever the selected WAL is shorter. The audited trace theorem derives the retry relation from these observations and the shared `runMarkedReopen` schedule, with no separate repair premise per attempt. [Marked reopen traces](../lean/Alvoki/Storage/Disk/MarkedWalReopenModel.lean)

## Abstract recovery from a prepared write and observed reopen effects

The composed theorem starts from one actual prepared write, an already durable marked WAL and a fixed matching checkpoint. It derives the physical write-cut witnesses and retry relation from the modeled callback effects and the observed reopen reads. If the write reports success, every possible final marker recovers the extended history. If it reports an error, recovery can return the old history or include the one submitted write. Run loading, marker selection and replay on the final chosen bytes produce the corresponding abstract suffix and agree on point and range reads at each supported snapshot. Linking the checkpoint observation to the native loaded runs and the returned open session remains part of the Linux adapter refinement. [Composed effect refinement](../lean/Alvoki/Storage/Disk/MarkedAdapterRefinement.lean)
