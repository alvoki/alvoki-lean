# Proof techniques and reuse in Alvoki

The [proof architecture](proof-architecture.md) starts from public guarantees and their evidence. This index starts from proof techniques that occur in more than one part of the implementation.

## How to structure a proof

Start with a claim about an executable entry point and the behavior its caller can observe. For crash
recovery, specify when the contract requires a successful open and when it allows an error. On
success, explain reads on the actual table returned by `DiskTable.open`. On error, account for any
effects and identify the reached state from which a retry starts. Preserve acknowledged writes in
order. An uncertain batch is absent or applied in full, subject to the allowed history order. For
example, when recovery selects a prefix, later batches cannot survive a gap.

Compose a representative end-to-end case in Lean early. Keep each unfinished connection as an
explicit premise and identify the filesystem assumption or preceding lemma that will supply it.
Then try a second case whose reached state differs in a way that could affect the next step.
Use both cases to decide which facts belong in the shared invariant before expanding the case
list. The milestone is complete when the composed theorem covers the promised outcomes and
derives its intermediate premises from the execution.

Prove one refinement at each boundary. Join the results by identifying the state or value that one
boundary produces and the next one consumes.

| Boundary | Obligation to prove once |
|---|---|
| Native primitive to production schedule | Interpret the actual callback at the reached heap. Account for the returned value and effects, or for the issued operation and effects at an interruption. A returned error may follow an effect. An interruption has no ordinary API return. |
| Reached storage state to recovery selection | Derive which manifest, runs and marker-bounded WAL recovery reads from one allowed filesystem outcome. Record the selected paths, inodes, bytes and replay watermark together. |
| Selected reads to the returned table | Use the proof of the actual reads, replay, repair and allocation to identify the returned table and next usable session. The same opened references and reached heap carry into the next call. |
| Session steps to the client contract | Compose the operation refinements in one induction from the supported initial state. Use the common replay and snapshot proofs for the resulting history. |

The end-to-end theorem crosses all four boundaries by composition. Each local proof sees the
implementation detail needed at its own boundary. For example, proving that the replay algorithm
returns the right rows for an input byte array still leaves an essential equality to prove. Those must
be the bytes read from the selected inode by the opener that returned the table. Reuse the existing
trace induction and bounded-read contracts as consumers of that evidence. [Reached execution and replay](../lean/Alvoki/Storage/Disk/NativeExecutionPrefix.lean) · [Exact prefix reads](../lean/Alvoki/Storage/Disk/ReadRecoveryPrefix.lean)

### Choose an invariant that can be carried forward

Define what has to remain true at a stable boundary and prove how each operation establishes,
preserves, or deliberately changes it. Give the next proof enough information to fix the identity of
its input. Keep an operation's immediate details local once they have discharged that obligation.
Use the smallest scope justified by recovery. For checkpoint recovery, that scope is the selected
manifest and the run and WAL paths it will read, with the root and lock tracked separately.

The two early checkpoint stops illustrate the distinction. A stopped run fsync can retain the
issuing descriptor at the stop. The first directory fsync issues after the temporary run descriptors
have closed. Both preserve the prior checkpoint selection. A rename error requires a different
selection proof because the chosen crash image can retain the old manifest even if the replacement
was visible. The consolidation target is one proof from selected reads to the exact returned table,
shared by all three paths. That proof must accept each allowed selection with its
own watermark and bytes. [Run fsync stop](../lean/Alvoki/Storage/Disk/Proofs/Checkpoint/NativeCheckpointRunFileStop.lean) · [First directory fsync stop](../lean/Alvoki/Storage/Disk/NativeStoppedRunDirectoryTableOpen.lean) · [Manifest rename error](../lean/Alvoki/Storage/Disk/Proofs/Checkpoint/NativeCheckpointManifestRenameTableOpen.lean)

Prove outcomes over the same production schedule and prefer induction over its actual sequence of
operations or retries. Put the distinction between completed return, pending call and interruption
where the schedule makes it. Compose a failed open and a later successful open through the state
between them. This lets a later proof reuse the same retry argument even when another interruption
or rejection appears. [Shared production schedule](../lean/Alvoki/Storage/Publication/DiskPublication.lean) · [Opened-session induction](../lean/Alvoki/Storage/Disk/NativeOpenedRestartSessions.lean)

When several executable paths perform the same check before I/O, extract that
decision in the production code and prove its effect once. Three WAL readers
use the same marker guard. Its failure leaves the entry state intact. On success
the reader receives the exact cutoff in frames. A proof about I/O costs can
then start at the directory listing, and a proof about a rejected marker can
stop before it. Preserve callback order and compare the native release path
when extracting a helper. [WAL cutoff and its contract](../lean/Alvoki/Storage/Disk/WalSegmentReadIO.lean#L93)

### Review the proof boundary

- Name the public outcome the change covers and the theorem that uses it. For a new case-specific
  report, identify both the primitive evidence that derives it and the theorem that uses it. Track
  missing connections as remaining proof work.
- Read the public theorem's premises. A local primitive receipt may say which bytes a read returned
  or what an fsync changed at the reached heap. An intermediate success result is a valid input to
  the next lemma once the preceding lemma proves it. When open returns successfully, the public refinement
  must derive the installed session and its replay from the execution.
- When extracting a shared lemma, try it on two different concrete callers. Look for a duplicated
  argument that disappears or an existing invariant that a new case can reuse directly. Keep
  differences that affect callers or recovery. For example, an identical EIO before or after a
  directory sync can admit different crash images. [Obsolete-run barrier errors](../lean/Alvoki/Storage/Disk/NativeObsoleteRunBarrierError.lean)
- When a new case repeats a downstream proof, check whether the existing lemma can consume
  the invariant established by both cases. Keep differences local to the step that needs them.
  Judge each new local lemma by the premise it discharges, the public outcome it adds, or the
  duplicated reasoning it removes.
- Track safety and progress independently. The safety theorem ranges over all admitted executions
  and crash outcomes, including returned errors and interruptions. Recovery completion can assume
  that required I/O succeeds and resources are available. Eventual reclamation can assume eligible
  data stays eligible and a later maintenance pass reaches an effective directory barrier.
  Name removal and release of allocated blocks need distinct evidence. [Recovery progress](../lean/Alvoki/Storage/Disk/CachedRecoveryProgress.lean) · [Reclamation contract](proof-roadmap.md#garbage-collection-contract)
- Check dependencies on the integrated theorem, including the kernel and axiom audit. Use native
  fixtures to test the adapter at the reported boundaries. Track the proof's scope by which
  executable outcomes it covers and which premises it discharges. Keep ghost histories and other
  proof data away from native execution. [Sequential checks](../scripts/check-sequential.sh) · [Performance requirements](proof-roadmap.md#performance-requirements-for-verified-paths)

## Existing proof techniques

| Technique | Start here | What it buys |
|---|---|---|
| Binary-search partitions | [Partition and search invariant](../lean/Proofs.lean#L6) · [Machine index refinement](../lean/OptProofs.lean#L37) | Lower and upper cuts identify a contiguous key interval. The packed v1 and v3 readers use this to connect index scans to filtering decoded rows. |
| Exact bytes and codec refinement | [Byte extensionality](../lean/ByteWords.lean#L46) · [v3 round trip](../lean/CompactionCodec.lean#L191) · [Fused v1 merge](../lean/RunMergeProofs.lean#L167) | Prove equality with the reference encoder by matching lengths and words. The resulting equality covers headers, order and payload bytes. |
| Ordered visibility | [Winner of a merge](../lean/CompactionModel.lean#L216) · [Retention](../lean/CompactionModel.lean#L402) · [Range congruence](../lean/Alvoki/Storage/Table/SequentialModel.lean#L123) | Compare the winning version for a key at a snapshot. Membership and key ordering then determine the exact visible range. |
| Representation refinement | [Memtable contract](../lean/Alvoki/Storage/Table/MemTableContract.lean#L18) · [Packed table refinement](../lean/Alvoki/Storage/Table/PackedTable.lean#L118) · [Successful snapshot write](../lean/Alvoki/Storage/Table/SnapshotTable.lean#L133) | Project each representation to a common ordered history. Prove operation results against it once, then use those results in client proofs. |
| Finite checks for all snapshots | [Purge check and snapshot boundaries](../lean/Alvoki/Storage/Table/SequentialPurge.lean#L47) | Between consecutive version boundaries, visibility is constant. The logical purge check therefore reduces a claim over all supported snapshots to finitely many checks. |
| Callback schedules and failure prefixes | [Publication schedule](../lean/Alvoki/Storage/Publication/DiskPublication.lean#L4) · [Reported prefixes](../lean/Alvoki/Storage/Publication/DiskPublicationModel.lean#L8) · [Manifest rename prefix](../lean/Alvoki/Storage/Disk/Checkpoint/Manifest/RenamePrefix.lean) · [Correlated crash images](../lean/Alvoki/Storage/Publication/DirectoryPublicationModel.lean#L42) | Account for completed effects and whether the failing action took effect. Keep outcomes for different names correlated through directory barriers and retries. |
| Lock ownership and reference lifetime | [Lock descriptions](../lean/Alvoki/Storage/Disk/LockDescriptionLifetime.lean#L6) · [Close and handoff](../lean/Alvoki/Storage/Disk/LockDescriptionLifetime.lean#L204) | Prove a common handoff for an exact reached file image. Explicit close and observed final reference drop expose the same image to the next cooperating lock acquisition. |
| Selected files and returned reads | [Selected run maps](../lean/Alvoki/Storage/Disk/Checkpoint/SelectedRuns.lean) · [Held directory observations](../lean/Alvoki/Storage/Disk/Proofs/Recovery/HeldDirectoryReadObservations.lean) · [Marked authorization](../lean/Alvoki/Storage/Disk/Proofs/Recovery/ListedDirectoryAuthorization.lean) · [Guarded snapshots](../lean/Alvoki/Storage/Disk/CachedRetrySnapshotReads.lean) | Agreement at the manifest's selected indices preserves the loaded checkpoint. Join those byte reads, listing and first barrier under a common observed directory, then carry the returned session into point and range refinement. |
| Recovery and trace induction | [Bounded checkpoint retry](../lean/Alvoki/Storage/Disk/CheckpointRetrySession.lean#L93) · [Writer trace](../lean/Alvoki/Storage/Disk/SegmentedDatabaseTrace.lean#L295) | Compose operation-specific effects, recovery outcomes and the invariant that each next step requires. This is the bridge from individual cuts to database histories. |
| Bounded acquisition | [WAL callback trace](../lean/Alvoki/Storage/Disk/Proofs/WAL/WalSegmentReadWork.lean) · [Checkpoint read sizes](../lean/Alvoki/Storage/Disk/IntegrityCheckpointSizedRead.lean) | Count requests in the actual read schedule and tie each admitted byte range to the selected marker or manifest. Compare the exact accepted input with the existing integrity and replay model. |

The filesystem results use the stated callback and crash assumptions. The [axiom audit](../lean/Alvoki/Checks/AxiomPolicy.lean) checks theorem dependencies. The [native fixtures](../scripts/check-sequential.sh) exercise the adapter's callback behavior and process-death cases.

## Where to reuse next

1. **Package successful retry outcomes.** [Held checkpoint installation](../lean/Alvoki/Storage/Disk/Checkpoint/Reopen/HeldInstallation.lean) connects retry lineage and exact file reads to the returned ready session. The prior-manifest and live-manifest proofs share it after establishing which manifest choices they admit. [Append retry installation](../lean/Alvoki/Storage/Disk/Proofs/Append/AppendRetrySession.lean) applies the pattern across full-chain and retained-WAL recovery, with each route keeping its own WAL invariant.
2. **Track WAL provenance alongside retained readiness.** The [mixed database trace](../lean/Alvoki/Storage/Disk/SegmentedDatabaseTrace.lean) and [single-writer trace](../lean/Alvoki/Storage/Disk/SegmentedWriterTrace.lean) now share the induction within each trace family. The full-chain guarantee is recovered from its explicitly propagated evidence.
3. **Use operation results as the proof boundary.** [PackedTable](../lean/Alvoki/Storage/Table/PackedTable.lean) specifies the successful restore, write, flush and compact results once. Row bounds, logical refinement and checkpoint proofs consume those results. The [range congruence lemma](../lean/Alvoki/Storage/Table/SequentialModel.lean) gives a similar boundary for interval-local read facts.
4. **Keep generic schedule facts below storage.** [DiskPublicationModel](../lean/Alvoki/Storage/Publication/DiskPublicationModel.lean#L155) currently combines generic state-machine prefix reasoning with a WAL replay specialization. Move the specialization to the WAL layer so the reusable prefix lemmas can have a narrow import boundary.
