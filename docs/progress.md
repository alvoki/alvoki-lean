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

## Sequential storage checks on GitHub

The stock correctness workflow runs the sequential storage checks with the pinned Lean toolchain. The suite rechecks the disk and table proofs in Lean's kernel, enforces the axiom allowlist with a negative control, and runs the packed and disk regressions. Both stock workflow commands passed locally. [Workflow](../.github/workflows/correctness.yml) · [Sequential checks](../scripts/check-sequential.sh)

## Write outcomes at the WAL boundary

`DiskTable.writeWithOutcome` returns the acknowledged sequence on success. A rejected submission failed before append was attempted. A submission with an unknown commit outcome may appear after reopen. Both errors retain their `IO.Error`. The native checks cover a failed sync that leaves the write recoverable, a partial sync that leaves it unselected, and rejection before append on poisoned and closed handles. The existing `write` emits equivalent C and the median paired write time was 1.001× the baseline. [Write API](architecture.md#sequential-storage) · [Benchmark](benchmarks.md#typed-disk-write-outcomes)

## Exact replay table after successful marked open

The native adapter and model share checkpoint reads, marked WAL validation and the return of the recovered table after the durability action. The audited composed theorem identifies the table returned by successful modeled reopen, starting from one prepared write and a fixed matching checkpoint. It shows that the table and settled WAL agree with abstract replay and that an acknowledged write survives all admitted retries. The file read and sync assumptions remain explicit. Median paired reopen times were within 4% of the baseline across the six measured workloads and the checkpoint rerun. [Proof and assumptions](verification-status.md) · [Reopen timings](benchmarks.md#shared-marked-open)

## Packed writer ownership diagnostic

Native `markLinear` checks completed 75 exact workload and mode combinations across replay, v3 compaction and dense rewrite. The test deliberately retained an alias to confirm that the diagnostic detects sharing in both overwrite and grow paths. The sampled writer destinations stayed unique during mutation after marking. [Checks and reproduction](../benchmarks/results/packed/linearity)

## Scoped v3 compaction

The opt-in whole-loop lowering selects and copies retained 32-byte rows into a single private buffer. The branching row writer was faster than the existing Rust writer on the five comparison profiles. Row and span pipelines include output validation and a snapshot scan. Both selector variants passed exact byte and snapshot checks, and the build verifies the generated ABI and its borrowed inputs. [Results and trust boundary](compaction.md#whole-loop-v3-writer)

## Stock Lean exact-size encoding

Pre-extending a destination and writing through a cursor sped up encoding of owned v3 rows by 4.59–5.27× from an array and 3.36–3.71× from a prebuilt list compared with append on stock Lean. For packed compaction, counting the retained rows and initializing the exact output size cost more than one-pass append or span coalescing. A mixed-order rerun confirmed the advantage of the scoped row writer across four v3 profiles. [Exact-size cursor](../benchmarks/results/packed/stock-v3-cursor) · [Mixed-order comparison](../benchmarks/results/packed/v3-writer-comparison)

## Wide accessors and published toolchain controls

Unchanged packed writer code passed exact fixtures on Lean 4.36, the 23 November nightly, and the official build of PR #14053. Alternating replay on the three toolchains differed by about 2% in the repeated run. In a separate benchmark that uses the draft accessors, the preallocated owned v3 encoder took 4.13 ms at one million rows, down from 14.65 ms with stock byte stores. The fixed-size `memcpy` variant further cut alternating replay, while the post-store exclusivity assumption changed generated checks with mixed timing effects. Both timing scopes and the exact external toolchain revisions are archived. [Published toolchains](../benchmarks/results/packed/upstream-toolchains) · [Accessor timings and code generation](../benchmarks/results/packed/wide-accessors)

## Exact metadata after marked reopen

The write-cut selector now carries the exact encoded marker alongside the selected history. The composed reopen theorem uses its lineage across retries to identify the final active metadata pair. The fixed manifest and marker for the recovered WAL length are settled together. This gives the next protocol operation a concrete history witness under the existing filesystem contract. [Composed reopen theorem](../lean/Alvoki/Storage/Disk/MarkedAdapterRefinement.lean)

## Acknowledged writes and repeatable recovery

The acknowledged-write trace carries the actual modeled file image between writes. Each prepared frame extends the exact durable prefix, and replay of those frames agrees with the session's table. The composed theorem permits one later write to report an error, then any admitted retries and crashes. Successful reopen preserves all acknowledged writes and can retain that final write once. The recovered session satisfies the next-write invariant. Further retries and crashes with no writes preserve this settled history. The native regression checks both historical reads and exact WAL, marker, manifest and run bytes when a reported error leaves the final write durable, including subsequent successful appends and another reopen. [Write trace](../lean/Alvoki/Storage/Disk/MarkedWriteTrace.lean) · [Recovery proof](../lean/Alvoki/Storage/Disk/MarkedAdapterRefinement.lean) · [Native fixture](../lean/Alvoki/Checks/DiskTableChecks.lean)

## Shared optional WAL reads and conditional reopen progress

The native and modeled adapters share the marker read, marker decode and WAL read order. The read contract distinguishes missing files from read failures. The audited metadata proof identifies the generation and WAL byte count of a successfully loaded session. The completion proof starts with a settled, correctly numbered WAL within the byte bound and a checkpoint whose watermark matches its covered prefix. Replay and reopen succeed when checkpoint loading, locked file reads and aligned sync succeed. Pooled paired median times were 0.953× to 1.014× baseline across the six native reopen workloads. [Read and recovery proof](proof-roadmap.md#disk-guarantees-to-prove) · [Raw measurements](../benchmarks/results/disk/shared-open-wal-reads)

## Clean session closure and opposite write outcomes

A session with only acknowledged writes can close or crash and recover to another ready session with the exact durable history and abstract snapshot reads. The native regression now exercises opposite unknown write outcomes in consecutive sessions. It checks the original checkpoint and exact WAL bytes, discards a complete frame outside the active marker, and writes a different key at the reused ordinal. [Clean recovery proof](../lean/Alvoki/Storage/Disk/MarkedReopenStability.lean) · [Native fixture](../lean/Alvoki/Checks/DiskTableChecks.lean)

## Recovery across writing sessions

`MarkedSessionTrace.refines` passes the table returned by the modeled reopen and the settled file image into the next writing session. With a fixed matching checkpoint, the recovered history contains the original prefix and all acknowledged writes in order. Each session either drops its final ambiguous write or retains its complete submitted frame. A later submission can reuse an ordinal from a dropped write. After at least one reopen, the recovered table agrees with abstract point and range reads at every supported snapshot. [Session trace proof](../lean/Alvoki/Storage/Disk/MarkedSessionTrace.lean)

An acknowledged write sequence also carries the canonical WAL-history invariant into its exact live writer table. It preserves the ready-session invariant, extends the history by the submitted frames and yields a refined abstract table for checkpoint preparation. [Acknowledged-write history proof](../lean/Alvoki/Storage/Disk/CheckpointHistory.lean)

With a fixed checkpoint that represents its covered history, a successful reopen returns an exact refined writer with a fresh pin registry. This applies after clean close or after a final write reports an ambiguous outcome. The writer retains the old durable prefix and all acknowledgements in submission order. Its represented WAL includes the final ambiguous frame exactly when the selected marker covers it. [Session history proof](../lean/Alvoki/Storage/Disk/MarkedSessionHistory.lean)

## Checkpoint preparation and marked WAL recovery

Checkpoint preparation shares the native decision to flush pending rows. Given the table refinement and row and count bounds, it produces the ordered run bytes named by the new manifest. The loader witness preserves the committed watermark and relates the resulting table to the corresponding abstract flush. At a settled WAL, the modeled publication schedule pairs every selectable manifest with the same exact WAL marker. That pair still supplies the exact durable run files and a covered watermark after modeled crashes and reopen retries. The proof that either selected checkpoint represents the appropriate prefix of that WAL remains a separate step. [Preparation witness](../lean/Alvoki/Storage/Disk/DiskRecoveryModel.lean) · [Publication and retry proof](../lean/Alvoki/Storage/Disk/MarkedCheckpointPublication.lean)

## The next writer after checkpoint publication

Completing the shared checkpoint schedule at a settled WAL publishes the prepared runs at the nonwrapping successor generation, which is unreachable from the old selectable manifests. The resulting checkpoint and writer state satisfy the existing next-session invariants with the same WAL history and byte count. The full-watermark loader validates all selected WAL frames and applies no additional writes. It resets the pin registry, preserves the floor and watermark, and agrees with the pre-flush abstract table at supported snapshots. A native fixture advances the floor, syncs the new manifest and then reports an error. It verifies the exact new run set and confirms that a later acknowledged write survives another reopen. [Writer readiness](../lean/Alvoki/Storage/Disk/MarkedCheckpointReady.lean) · [Full-watermark reopen](../lean/Alvoki/Storage/Disk/FullWatermarkReopen.lean) · [Native fixture](../lean/Alvoki/Checks/DiskTableChecks.lean)

## Reads from the table returned after a checkpoint cut

`checkpointMarkedRetry_reopen_refines` uses the actual modeled file observations at the successful reopen. It identifies the ordered durable runs from the selected manifest, the exact same WAL and the suffix after the selected watermark. The returned table agrees with abstract point and range reads from that checkpoint's retained floor. The proof takes a caller-supplied invariant relating each admitted checkpoint model to its prefix of that WAL. The remaining trace proof must derive that invariant from preceding operations for both the old and the new checkpoint. [Returned-table proof](../lean/Alvoki/Storage/Disk/MarkedCheckpointPublication.lean)

## Row sequences through writes, compaction and recovery

Every row of a ready writer is now bounded by its committed sequence. Acknowledged writes and the actual selected-WAL recovery path preserve that invariant, so checkpoint publication can use it directly. The packed-table proofs cover pin changes, retention-floor changes, flush and compaction as well. The checkpoint still checks the representable run count and relies on the live abstract table refinement. [Packed table bounds](../lean/Alvoki/Storage/Table/PackedTable.lean) · [Writer invariant](../lean/Alvoki/Storage/Disk/MarkedWriteTrace.lean)

An exact checkpoint load and selected WAL replay also give a full refinement for the recovered writer with its actual pin registry. This model has the data, committed sequence and retention floor of abstract replay from the original checkpoint model. Its active pin set starts empty. This supplies an abstract state for another checkpoint after reopen. [Recovered session refinement](../lean/Alvoki/Storage/Disk/RecoveredPinRefinement.lean)

## A common WAL history for checkpoint recovery

A numbered WAL beginning at one has a unique abstract replay from the empty table. Tables with the same clock, bounded rows and matching visible entries keep that agreement when replaying the same suffix. Actual checkpoint preparation preserves the live table's history through its flush decision, so the newly prepared files represent the full covered prefix whenever the live table does. After an interrupted checkpoint, a successful reopen agrees with full canonical WAL replay at every snapshot supported by the selected checkpoint, provided each selectable checkpoint represents its own covered prefix. [Replay agreement](../lean/Alvoki/Storage/Disk/WalReplayAgreement.lean) · [Checkpoint history](../lean/Alvoki/Storage/Disk/CheckpointHistory.lean)

Advancing the live floor and compacting a run pair preserve the same represented WAL and produce the exact abstract transition. The floor change narrows the supported snapshots, and compaction preserves the winning entry throughout that range. The remaining composition carries the refined state and its history from an initial database through interrupted operations and later sessions. [Maintenance proofs](../lean/Alvoki/Storage/Disk/CheckpointHistory.lean)

## Resume writing after an interrupted checkpoint

The checkpoint retry proof derives the next ready writer from the table and settled file image returned by the actual modeled open. It constructs the selected checkpoint witness from the exact durable run map and the settled manifest projection. The new writer has the full represented WAL, an empty pin registry and a corresponding abstract table. This uses the logical prefix invariant for each admitted checkpoint. [Checkpoint recovery handoff](../lean/Alvoki/Storage/Disk/MarkedCheckpointReopenReady.lean)

The shared checkpoint schedule now derives its publication cut from file-operation reports, including a final directory sync that took effect before reporting an error. The old checkpoint's witness follows from the ready writer and its covered prefix. The new witness follows from the actual flush, successor generation and ordered prepared bytes. After successful modeled reopen, its read results also determine the installed generation and selected WAL byte count. [Reported checkpoint](../lean/Alvoki/Storage/Disk/MarkedCheckpointReady.lean) · [Recovery metadata](../lean/Alvoki/Storage/Disk/MarkedCheckpointReopenReady.lean)

## A ready database starts from the fresh open

One invariant now ties the ready writer, the selected checkpoint and the installed manifest generation to the same WAL. Acknowledged writes, floor changes, compaction, pin acquisition and release, and fixed-checkpoint reopen preserve it. Each step uses the concrete operation's returned table, and the checkpoint keeps its represented prefix until the manifest changes. [Database-state invariant](../lean/Alvoki/Storage/Disk/MarkedDatabaseState.lean)

Successful fresh initialization derives the first ready writer from the locked absent-file observations and the modeled empty-WAL creation, sync and marker publication. The resulting WAL is empty and settled, with an absent checkpoint and installed generation and byte count zero. The fresh-branch model covers successful callbacks. Recovery from errors or crashes during initialization remains a separate obligation. [Fresh bootstrap proof](../lean/Alvoki/Storage/Disk/FreshMarkedBootstrap.lean)

## Exact history for an existing unmarked WAL

The native unmarked open and proof share WAL selection and replay. For successful input, the complete prefix is exactly the encoding of its numbered history. A short tail leaves the ordinal decoder result unchanged, including a complete-frame error. The observed checkpoint loader supplies the exact base and a recovered fresh-pin model. Once the selected bytes and marker are durable, marked recovery returns the identical table. Native release timings for opens without a marker gave median paired ratios from 0.971× to 1.012× against the baseline. [Legacy recovery proof](../lean/Alvoki/Storage/Disk/LegacyWalRecovery.lean) · [Measurements](../benchmarks/results/disk/legacy-wal-recovery)

## Observed ready states and fresh-bootstrap cuts

Ready-boundary evidence now records the writer state, installed generation and durable run bindings. The matching checkpoint and its refinement are obtained from the invariant. Fixed-checkpoint session evidence uses the run bindings directly, so the same observed file reads, write outcomes and reopen can preserve the invariant without a supplied checkpoint proof for the resulting state. [Observed boundary](../lean/Alvoki/Storage/Disk/ObservedMarkedState.lean)

The fresh-bootstrap cut proof covers empty-WAL creation, partial sync effects, marker publication and power-loss choices. A retry can observe a missing WAL, an existing unmarked empty WAL, or a marked empty WAL. Any selectable marker names an already durable empty WAL. This establishes the input cases for retry completion. [Bootstrap cut proof](../lean/Alvoki/Storage/Disk/FreshMarkedBootstrap.lean)

## Bootstrap and checkpoint retry completion

All three admitted empty-bootstrap observations now lead to the same ready empty writer when the reads and required durability operations succeed. The shared selection and publication protocols derive the actual table, installed metadata and settled file image. An existing unmarked WAL also becomes ready after its validated canonical prefix is made durable and the first marker is installed. That legacy proof requires the observed checkpoint to represent its prefix of the same WAL. [Empty bootstrap](../lean/Alvoki/Storage/Disk/FreshMarkedBootstrap.lean) · [Legacy bootstrap](../lean/Alvoki/Storage/Disk/LegacyMarkedBootstrap.lean)

After an admitted checkpoint cut and reopen attempts, successful reads at the visible manifest and its selected run indices give enough data to derive successful exact replay. A successful aligned sync then produces the returned table and the settled WAL. With an absent manifest, no run reads are required. [Checkpoint retry completion](../lean/Alvoki/Storage/Disk/MarkedCheckpointReopenProgress.lean)

## Mixed marked database traces

The mixed trace carries the writer table, file image, installed generation and durable run map from one ready boundary to the next. Each sequence of acknowledged writes, retention or pin operation, checkpoint outcome and successful reopen derives its next logical checkpoint and history from the previous invariant and observed execution. The fresh entry proof reconstructs that invariant and the empty history from the actual reported result after admitted bootstrap attempts. Every trace prefix retains all acknowledged frames in order and may retain its own complete ambiguous submissions. For any active local pin, executable point and range reads agree with the canonical replay of that prefix's settled history. [Checkpoint transitions](../lean/Alvoki/Storage/Disk/MarkedDatabaseCheckpoint.lean) · [Mixed trace](../lean/Alvoki/Storage/Disk/MarkedDatabaseTrace.lean)

## History survives the first legacy marker publication

Reported legacy repair, sync and marker-publication cuts preserve the complete decoded WAL history. The cut may expose a marker that a later crash still drops. Every admitted combination of metadata and WAL yields the same selected bytes and replayed table when the checkpoint base is the same validated table. If a marker is selectable, all possible WAL copies are already exact and require no tail repair. The invariant assumes an owned directory, a fixed optional manifest, and the same complete ordinal history in each initial WAL choice. [Legacy cut proof](../lean/Alvoki/Storage/Disk/LegacyBootstrapCuts.lean)

## Optional filesystem reads

The native adapter and observation proof share the lstat and read decision for the manifest, WAL marker and WAL. Only an `ENOENT` from directory-entry lookup can yield absence. A dangling symlink or a file read that fails after successful lookup gives an error. The locked and stable namespace contract supplies the correspondence between successful reads and the visible bindings. The native dangling-link fixture now covers all three names. Paired reopen ratios ranged from 0.983× to 1.015×. [Optional read proof](../lean/Alvoki/Storage/Disk/OptionalFileRead.lean) · [Measurements](../benchmarks/results/disk/optional-file-reads)

## Shared native open, checkpoint and session decisions

The native open and the empty-bootstrap proof use the same continuation for WAL reads, validation, repair or aligned sync, first marker publication and installing the result. The native checkpoint dispatcher writes the exact planned run bytes to its generation and index paths, syncs each run, and reaches the run-directory barrier before manifest replacement. Phase checks report closed or poisoned sessions before the handle comparison. Foreign or stale handles return no data and leave release state unchanged. A local active pin reads canonical WAL history at its sequence. The proof uses live reference identity as the contract for `ST.Ref.ptrEq`. [Native open](../lean/Alvoki/Storage/Disk/DiskTable.lean) · [Checkpoint dispatch](../lean/Alvoki/Storage/Disk/CheckpointFileDispatch.lean) · [Session guards](../lean/Alvoki/Storage/Disk/SessionReadGuards.lean)

Native release comparisons cover fresh, legacy and marked open, checkpoint dispatch and the active read guard. The paired medians show no consistent slowdown across those workloads, and session reads measured 0.974× to 1.026× of baseline. Each archive records the raw samples and its baseline for reproduction. [Open](../benchmarks/results/disk/shared-open-bootstrap) · [Checkpoint](../benchmarks/results/disk/shared-checkpoint-file-dispatch) · [Session reads](../benchmarks/results/disk/shared-session-guards)

The shared open continuation now matches both recovery interpreters for an existing WAL. For an already marked directory, the theorem relates all observed read, parse and durability outcomes. For an existing unmarked WAL with a successfully loaded checkpoint, it preserves the result and image under every modeled durability and marker report. On success the shared open yields the exact table, installed generation and selected byte count. The mixed trace can use this successful result after a fixed-checkpoint session or an interrupted checkpoint publication. [Marked control](../lean/Alvoki/Storage/Disk/MarkedOpenControl.lean) · [Legacy control](../lean/Alvoki/Storage/Disk/LegacyMarkedBootstrap.lean) · [Mixed trace](../lean/Alvoki/Storage/Disk/MarkedDatabaseTrace.lean)

## Exact native WAL calls and installed byte count

The native commit equation identifies the append of the encoded frame and its flush, the staged marker and its flush, the grouped WAL and marker sync, the marker rename and the directory sync. The new size marker is the one used by the model when appending that frame to the settled history. The emitted adapter C and native write benchmark binary match the baseline byte for byte. Successful marked open installs those selected WAL bytes as the live and sole crash copy, whether it repaired a tail or synced an aligned WAL. The installed byte count agrees with the writer decoded from that exact durable image. [Native write](../lean/Alvoki/Storage/Disk/DiskTable.lean) · [Modeled write](../lean/Alvoki/Storage/Disk/WalWritePublicationModel.lean) · [Installed WAL](../lean/Alvoki/Storage/Disk/MarkedOpenControl.lean)

## Ownership through open and close

The adapter and proof share the lock acquisition, failed recovery cleanup and close decisions. Successful open owns the canonical `LOCK` object, so a second cooperating opener cannot enter recovery for that object. Unlock failure takes precedence over the original recovery error. Close leaves the old phase on failure and preserves ownership under the local Linux unlock contract. Closed handles skip release, and an old open file description cannot release a new owner's lock. The proof assumes stable lock objects and successful acquisition by a fresh open file description. Generated `DiskTable` C and its native object matched. Paired reopen ratios ranged from 0.939× to 1.028× of baseline. [Lock proof](../lean/Alvoki/Storage/Disk/DiskLockLifecycle.lean) · [Measurements](../benchmarks/results/disk/shared-lock-lifecycle)

Disassembly of pinned Lean 4.36.0 shows that unlock obtains `fileno`, calls `flock(LOCK_UN)` once and reports that syscall's result. In Linux's built-in inode lock path, the unlock that removes the matching file-description lock returns success. The local contract applies to this path while the handle remains live. The general effects model also represents a release before a reported error. In that case, the preserved phase alone supplies no ownership guarantee. [Linux syscall dispatch](https://github.com/gregkh/linux/blob/v6.18.57/fs/locks.c#L2011-L2055) · [Linux inode lock update](https://github.com/gregkh/linux/blob/v6.18.57/fs/locks.c#L1028-L1072) · [Linux flock description](https://man7.org/linux/man-pages/man2/flock.2.html)

The native disk fixture traced with `strace -f -e trace=flock` observes exclusive nonblocking acquisition, `EAGAIN` for a second handle, successful unlock and reacquisition. This checks the pinned Linux call path and fixture behavior. The proof uses the separate local `flock` contract for an unlock error.

## Healthy reopen from each legacy retry image

Once the selected files are readable and the required durability operations succeed, either admitted marker observation completes through the shared open control. The resulting writer has the validated checkpoint plus its exact WAL suffix, a settled copy of the canonical WAL, the expected generation and byte count, and an empty pin registry. Comparing that recovered table to replay from empty requires the older checkpoint to represent its covered prefix. [Legacy retry completion](../lean/Alvoki/Storage/Disk/LegacyBootstrapRetry.lean)

## Healthy reopen after an uncertain marked WAL write

After the write reports an error, its actual publication report and the subsequent modeled reopen attempts determine the visible WAL and checkpoint. Once the selected reads and required durability calls succeed, the shared marked open returns the expected table, generation and byte count. The settled history contains every previously acknowledged frame, optionally followed by the exact frame submitted by the failed call. The selected checkpoint remains fixed across this transition. [Uncertain-write retry](../lean/Alvoki/Storage/Disk/MarkedWriteReopenProgress.lean)

## Run sync errors before checkpoint publication

A reported run write or sync error stops the modeled checkpoint before the run-directory barrier. When the proposed generation is unreachable, the old manifest choices and their referenced runs are unchanged. The unreferenced files from the attempted generation may contain new data. The native fixture successfully syncs the final new run before reporting an error. It observes the old manifest, retention floor and WAL, then checks the exact shorter run set after a successful retry. A syscall trace confirms the file syncs on the failed attempt and the directory barriers and rename on retry. [Preparation failure proof](../lean/Alvoki/Storage/Publication/CheckpointPublicationModel.lean) · [Native fixture](../lean/Alvoki/Checks/DiskTableChecks.lean)

## Recovery safety for obsolete run generation removal

After checkpoint publication settles a healthy manifest, a different generation is eligible if nobody holds its files. The model also checks every possible crash manifest before allowing a removal. Repeated partial deletion and power-loss choices preserve the exact run bytes the loader selects, the replay result for the same WAL and all protected run bindings. The proof treats an omitted obsolete binding as a file whose durability is no longer guaranteed. Native enumeration, unlink and durable space reclamation still need an executable collector and its specification. [Generation-removal safety](../lean/Alvoki/Storage/Disk/RunGenerationCollection.lean)

## Recovery progress at each admitted boundary

One theorem now covers healthy retry after empty bootstrap, legacy adoption, a settled marked open, an interrupted checkpoint or an uncertain WAL write. Each case supplies its actual selected reads and required operation reports. The theorem derives successful installation, the selected manifest, the settled WAL and its exact byte count without assuming a successful open result. [Recovery progress](../lean/Alvoki/Storage/Disk/RecoveryProgress.lean)

## Retained snapshots stay stable across disk maintenance and reopen

For any mixed database trace, active pins at the same sequence at the beginning and end return the same point and ordered range reads. The proof splits the canonical replay at the original history and shows each later write, including a tombstone, has a greater sequence and cannot affect those reads. The two pins may belong to different sessions. [Stable snapshot reads](../lean/Alvoki/Storage/Disk/MarkedDatabaseTrace.lean)

If the old pin's sequence is still at or above the final retention floor, the same trace guarantees `acquireAt` succeeds and the returned pin reads the original values and range. The committed clock can only grow with the retained history. [Reacquisition proof](../lean/Alvoki/Storage/Disk/MarkedDatabaseTrace.lean)

## Native lock release on owner death

A native fixture stops a write at the staged-marker sync command, confirms a competing open receives the live owner's lock error, and kills only the owner. A new process obtains the lock and recovers the exact acknowledged WAL and marker while the same sync child is still alive. The Linux syscall trace also observes the lock descriptor opened with `O_CLOEXEC`. The fixture concerns process death while a child is alive. The power-loss behavior of completed sync calls remains part of the filesystem contract. [Native process-death fixture](../scripts/check-disk-process-death.py)

## Concrete native checkpoint paths under the database lock

The native open equation names the resolved lock, manifest, marker and WAL paths and every ordered run callback. The path-indexed proof reconstructs the checkpoint reading observations from those same path reports under the lock. Only the decoded manifest's generation and in-range indices require run byte agreement. Given those successful reads and exact durable bytes, the shared loader returns the corresponding base table. The emitted `DiskTable` C and native object remain byte-identical. [Native open equation](../lean/Alvoki/Storage/Disk/DiskTable.lean) · [Locked checkpoint reads](../lean/Alvoki/Storage/Disk/LockedOpenFileReads.lean)

## Settled reopen and guarded session reads

A shared reopen from a settled marked database returns a ready writer with the exact loaded generation, selected WAL byte count and a fresh pin registry. Running that successful recovery through the shared lock lifecycle also gives the opener ownership. A guarded read through an active local pin returns canonical replay data and preserves lock ownership. A closed session reports its closed error, and a distinct live session rejects the old pin. The proof uses file reports for the owned directory and live-reference identity for session comparison. [Locked marked reads](../lean/Alvoki/Storage/Disk/LockedMarkedRead.lean)

Successful I/O reports at the acquired directory's exact manifest, selected run, marker and WAL paths now yield the read premises of the common recovery progress theorem. The proof derives the values of successful optional reads from the locked namespace observation, including absence. Unselected run paths have no success premise. [Recovery read composition](../lean/Alvoki/Storage/Disk/LockedRecoveryReads.lean)

## Delayed directory sync after a writer dies

A delayed directory sync settles the manifest and marker visible when it takes effect. The model retains the earlier WAL crash choices as a conservative set of possible outcomes. Given the same primitive reports, an extra barrier preserves the shared reopen's table, generation and byte count or its reported error. A successful reopen already settles the metadata. The native fixture kills a writer after the marker rename, reopens and closes in a successor process, and then lets the original sync child issue the real directory sync. The complete submitted frame and checkpoint files remain exact. [Delayed sync proof](../lean/Alvoki/Storage/Disk/MarkedWalReopenModel.lean) · [Native fixture](../scripts/check-disk-process-death.py)

## Legacy recovery can start a mixed database trace

When the existing checkpoint represents its covered prefix of the validated legacy WAL, the exact result of recovery is a ready mixed-trace state with fresh pins, preserved run bindings and that full canonical WAL history. This holds whether the first marker survived the earlier adoption attempt or needed to be published on retry. [Legacy trace entry](../lean/Alvoki/Storage/Disk/LegacyTraceEntry.lean)

## Exact recovery completion through the shared lock schedule

All five admitted recovery boundaries identify their concrete evaluator. Under the acquired lock, the evaluator's successful result supplies the exact installation and file image to the outer native open schedule. The returned table, generation, WAL byte count and committed count match the settled selected history and the handle owns the lock. The boundary's file reports refer to the same directory under the existing locked namespace contract. [Locked recovery completion](../lean/Alvoki/Storage/Disk/LockedRecoveryCompletion.lean)

## Proved integrity format and dual-format checkpoint reader

The v2 manifest stores the generation, floor, watermark and run count as before, followed by each run's length and FNV-1a-64 digest in manifest order. It checksums the metadata and adds 16 bytes per run to the 48-byte fixed size. The versioned reader preserves accepted v1 behavior and checks v2 integrity over the same ordered bytes it passes to the run parser. Lean verifies that changing any one payload byte changes its digest. Native `DiskTable.open` and checkpoint publication still use v1. A future v2 writer requires a deployed reader that understands both versions. Hashing introduces a linear scan of the run bytes unless it is fused with work the reader or writer already performs. [Integrity format](../lean/Alvoki/Storage/Disk/ManifestIntegrity.lean) · [Dual-format read](../lean/Alvoki/Storage/Disk/VersionedCheckpointRead.lean)

## Proved inventory and retryable unlink pass for obsolete runs

The filename recognizer accepts exactly the run names emitted by the writer. Given a finite directory listing and no-follow regular-file reports under the lock, selection covers every eligible listed name and protects the currently selected generation and any explicit hold. A failed unlink pass can leave the previous name durable or complete some removals before reporting an error. After a successful complete pass, the final directory barrier makes every eligible name durably absent, with all unselected run bindings preserved. The model assumes immutable run payloads synced before collection. The barrier runs even on an empty retry. The native engine has no collector entry point yet. [File inventory](../lean/Alvoki/Storage/Disk/RunFileInventory.lean) · [Finite unlink pass](../lean/Alvoki/Storage/Disk/RunUnlinkEffects.lean) · [Shared schedule](../lean/Alvoki/Storage/Disk/RunUnlinkSchedule.lean)

## Interrupted checkpoint and uncertain-write recovery preserve the mixed trace

Starting from a ready writer and a modeled failure of the shared checkpoint schedule, the actual chosen manifest and ordered run reads under the new directory lock determine the returned table and installation. Recovery keeps the original history and may select either checkpoint generation. The uncertain-write branch similarly derives the next writer after repair or aligned sync, with the previously acknowledged history and possibly the full submitted frame. Both proofs return a mixed-trace step and the next writer invariant from the prior state, failure and successful required observations. Native primitive effects remain explicit premises. [Locked checkpoint recovery](../lean/Alvoki/Storage/Disk/LockedInterruptedCheckpoint.lean) · [Locked write recovery](../lean/Alvoki/Storage/Disk/UncertainWriteTraceEntry.lean)

## Versioned checkpoints retain exact run and table lineage

The new read proof works with the bytes of the selected manifest in either on-disk format. Its file observations are restricted to the decoded generation and run indices. Given the trusted durable run map, it identifies the same ordered byte arrays used for both v2 integrity validation and structural decoding, as well as the returned table, generation and covered watermark. The next step is to establish this input invariant through versioned checkpoint publication and retry. [Versioned checkpoint lineage](../lean/Alvoki/Storage/Disk/VersionedCheckpointLineage.lean)

## Successful versioned checkpoint publication

The versioned plan uses the existing run write and sync steps, the run-directory barrier and the shared manifest replacement. For v1 it produces the same result as the existing evaluator at every cut. A fully executed v2 plan makes the exact ordered run array and the newly encoded integrity manifest durable. The complete-state proof verifies the manifest's run lengths and checksums and relates its watermark to the WAL. [Versioned publication](../lean/Alvoki/Storage/Disk/VersionedCheckpointPublication.lean)

The versioned cut proof covers every prefix of one publication attempt. Before the run-directory barrier, the published model is unchanged. After the barrier, the previously selectable manifests retain their exact ordered files and the new manifest can select only the complete proposed generation. The fresh generation test follows the raw selectable v1 and v2 manifests. Repeated v2 retries and their native reports remain open. [Versioned cut proof](../lean/Alvoki/Storage/Disk/VersionedCheckpointPublication.lean)

## Delayed file sync and WAL inode identity

An explicit event now admits a delayed file sync on the current WAL inode. It conservatively adds the live bytes to the crash choices and preserves the result of a successful shared reopen with the same reports. When repair has replaced the WAL, the inode-level model tracks the old and new bindings independently of their byte choices. A valid late effect on the old inode preserves replay before directory settlement and leaves the exact settled replacement unchanged afterward. The native process-death test holds the old descriptor open across successor repair, then syncs it and checks the new inode and exact WAL, marker and checkpoint bytes. [Live WAL recovery](../lean/Alvoki/Storage/Disk/MarkedWalReopenModel.lean) · [Replaced inode](../lean/Alvoki/Storage/Disk/ReplacedWalDescriptor.lean) · [Native test](../scripts/check-disk-process-death.py)

## Versioned publication retries and marked WAL replay

The versioned model interprets the shared checkpoint schedule's reports, including a failure after an effect. Repeated publication attempts, crash choices and manifest settlement preserve acceptance of every selectable v1 or v2 checkpoint for the same synced WAL. The actual dual-format reader obtains the ordered runs from the selected generation and validates the same bytes before returning the base table. With successful reads of the exact selected WAL and marker and a successful aligned sync, shared marked open replays the suffix above the selected watermark and produces the exact table, byte count and generation. It represents the canonical full WAL history and has fresh pins. Native versioned activation and the joint WAL/manifest retry composition remain separate steps. [Versioned retries](../lean/Alvoki/Storage/Disk/VersionedCheckpointRetry.lean) · [Marked replay](../lean/Alvoki/Storage/Disk/VersionedMarkedRecovery.lean)

## Shared native path and checkpoint reader dependencies

The canonical directory and run-name construction now sit below the native adapter. The adapter can share the verified pure run selection without a cyclic import. The raw WAL commit helper stays private behind the writer's readiness check. The ordered v1 checkpoint loader and its shared read loop also sit below the adapter, so the dual-format reader can use them. Native open and checkpoint still use v1. The checkpoint reader extraction produced the same normalized native instructions for the compared open, read and checkpoint routines. [Canonical paths](../lean/Alvoki/Storage/Disk/DiskPaths.lean) · [Shared checkpoint loader](../lean/Alvoki/Storage/Disk/CheckpointRead.lean)

The run path extraction changes the native call boundary. The initial paired runs indicated up to 3.1% higher median time for some cases. Across 48 subsequent paired observations per case on two CPUs, the pooled candidate-to-baseline ratios were 0.988 for writes and 0.972 for checkpoint reopen. Both bootstrap intervals included parity, and same-build control medians varied. The repeat supplies the raw measurements for checking any smaller effect. [Initial comparison](../benchmarks/results/disk/run-collection-paths/) · [Repeat and controls](../benchmarks/results/disk/run-collection-paths/repeat/)
