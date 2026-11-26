# Native storage correctness argument

This assessment reviews the early checkpoint trace pilot at
`4a79765e992b9e034c2277cd7981a56b1611dd90` against the pre-pilot GitHub revision
`5527c03de2799698a16c6288dea2cabc8ed69cfe`. It covers the stock Lean sequential
Linux `DiskTable` with the segmented WAL, v2 manifest and v3 run files. The packed-block experiments and
Verus search have separate entry points and proof inventories. [Software architecture](../architecture.md#sequential-storage) · [Technical inventory](../verification-status.md)

## Current system guarantees

The fresh marked bootstrap establishes ready storage once the exact returned phase reference,
token and heap from `opensFromAdmission` identify the allocation endpoint. The observed keeper and marker barriers fix the empty
keeper and zero marker. The selected manifest is absent and the original directory and lock
have the captured identities. This uses the exact path and byte observations at the barrier,
including durability of the directory's own name in its parent. [Fresh opened storage](../../lean/Alvoki/Storage/Disk/NativeFreshOpenedSessions.lean)

### Client history

The claim is that every acknowledged write or batch is present in order and every recovered mutation comes
from a submission. Each uncertain batch is omitted or retained as one ordered group. The legal history
explains the reads that the client actually observed.

`FreshBootstrapOpenHeap.opensFromAdmission` derives the exact raw open result from fresh bootstrap
observations. The first table has the original lock and cache, a fresh phase and token, the zero marker,
and empty client ledgers. `FreshBootstrapOpenHeap.Returned` ties that initial position to the value
and heap returned by the observed open schedule. An already observed trace from that position uses
`Returned.refinesTrace` to derive the client history, submissions and reads directly from its events.
`InstalledClientReplay` includes a replay from empty, ordered batch retention, acknowledged and
submitted subsequences, and agreement with recorded reads and the ready table. [Raw fresh start](../../lean/Alvoki/Storage/Disk/NativeFreshTableOpen.lean) · [Composition from the empty ledger](../../lean/Alvoki/Storage/Disk/NativeFreshOpenedSessions.lean) · [Key-value refinement](../../lean/Alvoki/Storage/Disk/NativeExecutionTrace.lean) · [Client replay](../../lean/Alvoki/Storage/Disk/ClientReadTrace.lean)

The first-open theorem consumes raw admission, bootstrap and cache chronology, matching lock and
metadata, and allocation reports that preserve inode and cache state. It joins the raw returned table,
phase, cache and census. The later `FileImage` projection is supplied separately from the bootstrap
rotation view. A ready write trace still uses exact interpreted returns in the normalized `OpenWriteFiles`
view and local publication and custody evidence. [Per-call report premises](../../lean/Alvoki/Storage/Disk/NativeOpenReadyTrace.lean) · [Fresh allocation and views](../../lean/Alvoki/Storage/Disk/NativeFreshTableOpen.lean)

The raw append now projects one reached call on the installed active cache cell, preserving the
literal handle and diagnostic. `RawWalAppendCalls.projects` uses per-primitive observations and a
store law at the reached success or failure. Clearing or replacing the cell can release a stream,
so its projected result can change the files as well as the cache. The runtime law still has to
account for local and cached reference releases and their filesystem effects. The proof composes
the append result before marker publication. [Production cache schedules](../../lean/Alvoki/Storage/Disk/DiskTable.lean) · [Raw append projection](../../lean/Alvoki/Storage/Disk/NativeWalAppend.lean)
The append buffer and flush observations now give the exact old keeper bytes plus the submitted bytes
on the selected inode. The cache assignment preserves the flushed payload. These laws apply to a
clean cached handle or one opened on the existing keeper.

The raw staging callback follows the exclusive open, write, flush and pending-reference update.
A data failure carries the observed stream-release effects and the original error. A successful
flush fixes the marker payload on the newly created inode through the pending update. The WAL
schedule reaches its file barrier on the staging return. The barrier reads the active keeper
and attempts the remembered marker on the heap left by that keeper fsync, including an error.
Bootstrap and stopped checkpoint sync reuse the same selector and reference interpretation.
The regular-file effect changes durable byte choices only at the inode bound to the issued
descriptor. The grouped success proof derives the two routed fsyncs from the reached append and staged cache.
The visible append and marker payloads fix the two durable byte images through the ordinary syncs
and the pending-reference store. Success of the raw commit identifies the exact grouped return,
rename, cached directory load and final fsync. Rename keeps the synced staged inode and the final
directory fsync settles the keeper and canonical marker in each joint crash map. This uses
reported effect, binding and descriptor facts at each primitive. In each allowed joint crash map the keeper and canonical
marker name the exact visible inodes. On an acknowledged transition the physical WAL files combine
with one frame for the directory, lock, selected checkpoint and seals to establish the next ready
storage. The directory barrier settles its child names. The frame still covers the directory's
own binding. The remaining refinement must derive the normalized publication evidence and cache
custody from those same raw effects.
Both ordinary group errors already feed the same uncertain-write endpoint.
[Shared cache routing](../../lean/Alvoki/Storage/Disk/NativeRawSync.lean) · [Durable WAL publication](../../lean/Alvoki/Storage/Disk/NativeWalFileFsyncEffects.lean) · [Ready storage after an acknowledged write](../../lean/Alvoki/Storage/Disk/NativeReadyWriteStorage.lean) · [Pending write](../../lean/Alvoki/Storage/Disk/NativeGroupedPendingWrite.lean)

The shared single and batch dispatch can now run on one raw heap with the original phase cell,
metadata lookup and WAL callbacks. A prepared write that acknowledges must have passed the no-follow
guard on the observed metadata, set the poisoned phase, completed publication, and set ready at the
heap reached by the last barrier. Rejected metadata and uncertain publication preserve their exact
errors and heaps. The raw success projects to the classified dispatcher's exact returned phase,
sequence, cache and file image. The same publication projection serves the existing cache-erasure
proof and this raw interpreter. It uses the per-callback laws only on the actual reached steps,
including a returned error with its reached state. The same projection identifies the checked
request and its exact commit result. The acknowledgement proof consumes publication evidence for
that one request and keeps the prepared batch, sequence, installed phase and earlier reads together.
A frame across the ready-cell update carries the published bytes and jointly settled names to
that return. The remaining composition derives the publication evidence and descriptor custody
from the reached raw callbacks.

On the successful raw path, the prepared batch and published keeper and marker bytes now suffice
to construct the next retained writer. The same retained proof serves the reported path. The
original guard, commit and phase update frame the lock and cached directory independently of the
WAL descriptors. Their reached heap supplies the exact inventory and cache for the returned
opened position, with earlier reads and pins preserved. The commit return identifies the
append and stage results, the grouped sync, the canonical rename and the final fsync on the
original cached directory. A single frame proof follows the callbacks for both the authority
and protected footprint. The final rename and directory effects establish durable names in
one joint selection. The returned append, marker staging and grouped file sync supply the
exact keeper and marker payloads under local file and cache laws. The proof selects the
actual handles from the active and pending references, then derives the durable bytes of the
issued inodes. It independently carries the visible keeper bytes through the final namespace
and reference operations into the next opened position. The fresh-open theorem supplies the
same visible property for the empty keeper after the actual phase and token allocations.
The owner must still account for the pending reference contents, the clean cached hit and the
reported primitive effects. The common execution induction has to compose these write steps
with independent failures and recovery. A returned `commitUnknown` now identifies the failed
commit at that exact heap, with the original phase poisoned. The shared frame traversal carries
the exact descriptor authority and protected files through the failure. The uncertain WAL
outcome and later recovery still need to join that returned state.
[Raw uncertain return](../../lean/Alvoki/Storage/Disk/NativeRawUncertainWrite.lean) · [Raw write phase chronology](../../lean/Alvoki/Storage/Disk/NativeOpenWrite.lean) · [Raw return projection](../../lean/Alvoki/Storage/Disk/NativeRawWriteProjection.lean)

At a stopped staged-manifest fsync the returned prefix and pending-cache update identify the same
live descriptor. Its private inode effect leaves the previously selected checkpoint and WAL intact
in each joint crash map. Reboot carries the selected names and bytes and the exact census. The
normalized selected image is independent of the reached staging metadata. A surviving
`MANIFEST.next` contributes no extent probe or read to the marked WAL selector, at any listing
position. The selector filters parsed names from the one reported listing without another
directory call. A single frame fold carries the selected names and bytes across each finalized
read-only attempt into the reached aligned installer. The short run-read failure obtains the
crash child and its bytes from the actual admitted child and read frames. Admission and worker
effects still supply the local observations for installation. For a selected run read that
returns an ordinary error after a short chunk, the shared retry proof carries the selected names
and bytes through temporary, cache and lock disposal. It starts the aligned open from the reached
failure heap with the original callbacks.
[Staged manifest stop](../../lean/Alvoki/Storage/Disk/NativeCheckpointStopContinuation.lean) · [Selected run read retry](../../lean/Alvoki/Storage/Disk/NativeCheckpointOpenChronology.lean)

`NativeReachedExecutionPrefix.keyValueRefinement` adds whole-or-none uncertain events, ready replay when
the ending returns ready, and the existence of an allowed terminal history that agrees with prior reads.
`Returned.stopsAfterWrites` uses that terminal argument on a finite observed write trace from fresh
open. It derives the issued client instructions from the returned calls and consumes the source stop
on the reached heap of that same opened table. Deriving the write trace and its protected storage
directly from the raw production primitive chronology remains open. Duplicate client retries with
durable request identity require their own contract. [Terminal refinement](../../lean/Alvoki/Storage/Disk/NativeExecutionPrefix.lean) · [Fresh trace to checkpoint](../../lean/Alvoki/Storage/Disk/NativeFreshOpenedSessions.lean) · [Ordered batch selection](../../lean/Alvoki/Storage/Disk/SegmentedBatchDatabaseTrace.lean)

### Snapshot reads

`PackedTable.lookup_refines` and `PackedTable.range_refines` relate executable key and ordered half-open
range reads to the version model. The opened trace then follows the reached phase and actual issued
pin. The read records contain the original
snapshot and response, so their replay remains valid if a later operation advances the floor.
Supported cases include a denied foreign or inactive handle under the reported ownership comparison.
An accepted read of a missing or deleted key has an outer `some` and an inner `none`. The pilot closes
one direct post-crash acquire/read path across both early checkpoint fsync stops. Other executable
mutation and retry paths must supply their exact returned state to the same read refinement.
[Packed table refinement](../../lean/Alvoki/Storage/Table/PackedTable.lean) · [Client replay](../../lean/Alvoki/Storage/Disk/ClientReadTrace.lean) · [Foreign and inactive pin guards](../../lean/Alvoki/Storage/Disk/NativeOpenExternalPinRead.lean) · [Opened snapshot trace](../../lean/Alvoki/Storage/Disk/NativeOpenedSnapshotSessions.lean)

### Checkpoint publication

The prepared checkpoint represents the specified prefix of committed history. A crash selects one
manifest binding from an allowed namespace outcome. Its generation and stamped run descriptions
identify one set of exact durable bytes, and its watermark establishes where WAL replay starts.
Run-file syncs and the first directory sync preserve the prior selection. When manifest rename has
taken effect before the last directory barrier, a crash can select the old or the synchronized new
manifest. `CheckpointPowerCut.finalDirectoryPublication` shows that an effective final directory
barrier settles the new selection. These claims use the
reported file and directory effects, the selected inode bindings and the published run custody.
Proofs cover the reported cut families. Derivation from all reached raw schedules and interrupted
manifest preparation branches remains open. [Checkpoint protocol](../../lean/Alvoki/Storage/Publication/CheckpointPublicationModel.lean) · [Final directory cut](../../lean/Alvoki/Storage/Disk/CheckpointManifestDirectoryCut.lean) · [Manifest rename and selected read](../../lean/Alvoki/Storage/Disk/NativeCheckpointManifestRenameReboot.lean)

### Recovery and retry

`DiskTable.open_fileTargets` exposes the actual schedule for resolution, admission, the flat-WAL guard, marker
dispatch, replay, repair and allocations. Under a stable root and truthful read reports, the
admission and reader use the same lock, inode identities and durable bytes. The selected checkpoint
and WAL prefix establish the replay, and the installer connects it to the actual returned
`DiskTable`, references and reached heap. Failure and cleanup theorems carry the reported prior
effects and release outcomes into the next attempt. `RawFinalizedOpenAttempts` already composes
supported ordinary failures. The coverage work is to derive the reports for all reached admission,
read, repair, cleanup and reboot branches, including finite failures between a stop and the next
healthy open. [Native open schedule](../../lean/Alvoki/Storage/Disk/DiskTable.lean) · [Return classification](../../lean/Alvoki/Storage/Disk/NativeRawRecoveryReturn.lean) · [Aligned installation](../../lean/Alvoki/Storage/Disk/NativeAlignedCheckpointReopenEffects.lean) · [Finalized retries](../../lean/Alvoki/Storage/Disk/NativeFinalizedOpenRetries.lean)

### Reclamation

Under the selected checkpoint and lock, obsolete-run and covered-WAL eligibility preserve the paths
needed for recovery and the installed read state. The proof follows the reached effects of supported
deletion and sync calls. A successful reported matching obsolete-run collection removes an older,
unheld name durably at that reached return. `NativeExecutionTrace.reclaimsAtFirstCompletedObsoleteRunCollection`
states its exact eligibility, ordering and scheduling hypotheses.
Physical storage release after unlink additionally depends on the last live reference and on filesystem
allocation. The remaining obligations include full native retry coverage and a complete progress
argument for eligible data. [Run collection](../../lean/Alvoki/Storage/Disk/VersionedRunCollection.lean) · [WAL collection](../../lean/Alvoki/Storage/Disk/SegmentedCollectionStep.lean) · [Scheduled name removal](../../lean/Alvoki/Storage/Disk/NativeScheduledRunReclamation.lean)

### Progress and bounds

`CachedRetryInstalled.completesAfterCrashAndRetries` derives equivalent reinstall after a first
successful cached open, a specified allowed crash and finite bounded attempts without writes. It
requires a fresh admitted attempt with healthy primitive reports. Separate theorems count
selected read calls and decoder or replay work. The maintenance budget bounds bytes at names under
explicit extent, inventory and successful maintenance assumptions. Extending healthy completion to
every reachable supported case, allocator and descriptor bounds, and eventual storage release are
separate obligations. [Conditional recovery](../../lean/Alvoki/Storage/Disk/CachedRecoveryProgress.lean) · [Selected read work](../../lean/Alvoki/Storage/Disk/SelectedRecoveryChunkWork.lean) · [Named maintenance budget](../../lean/Alvoki/Storage/Disk/NamedMaintenanceBudget.lean)

## Refinement boundaries

Follow one write through a crash and reopen. Each row states what the next
layer needs to know. The links point to declarations at `283de70b`. The
[public claims](../proof-architecture.md#system-claims) describe semantic
obligations; a Lean theorem can discharge one obligation for several claims.

| Boundary | What must remain true, and why | Who establishes it → who uses it |
|---|---|---|
| Filesystem effects | For the paths an operation must preserve, names still bind the same inodes and their allowed contents agree. Each later crash map has one earlier witness for the **whole footprint**. Otherwise a proof could combine a manifest from one outcome with a run from another. [Scoped frame][frame] | Local effects of reads, removals and barriers → retry proofs, which compose or restrict the frame. The protocol chooses the footprint. |
| Storage authority | The held lock and directory handle refer to the captured objects. A single surviving namespace and its bytes determine the selected manifest, run files, WAL marker and replay range. A missing segment inside that range matters just as much as a present one. [Held authority][authority] · [Sampled replay][sample] · [WAL window][window] | Admission establishes custody. For covered publication stops, the crash-selection proof establishes the recoverable file set → the held reader checks and replays those files. |
| Installed session | The table returned by this `open` has the phase, token and cache allocated by this repair. Its active WAL bytes and directory descriptor agree with the storage at the return heap. This is what makes the next write safe on **that handle**. [Write entry][entry] | Successful repair and reference allocation → the next writer. A newly issued pin carries the returned token. The new handle starts with empty pins. |
| Client history | Each call extends the incoming history, submissions and observations with its own events. One replay accounts for acknowledged writes, whole uncertain batches and recorded reads. [Ledger suffix][ledger] · [Installed replay][replay] | Local operation refinements → the finite-call induction → write and snapshot guarantees. Collection also needs an eligibility proof for the removed files. Progress needs availability and scheduling assumptions. [Reclamation](#reclamation) · [Progress](#progress-and-bounds) |

**Where the chain closes.** On the covered aligned checkpoint path, the opener
derives the repair and installation from the same successful call. Given the
sampled reboot and the effects of the intervening failed opens, it establishes
the next write entry. A finite sequence of supported writes and snapshot calls
then extends the actual predecessor's ledger. [Checkpoint consumer][checkpoint] · [Finite induction][fold]

**Where it is still conditional.** A successful stat accounts for each later
WAL file selected for pruning. Completeness in the other direction is a
filesystem obligation. Internally, every reachable failure must still supply
its local effects through cleanup to the public return, and each interruption
must supply its reached state. If segments 4 and 8 both start beyond the marker, a retry can delete 4
and then fail at 8. The next open must see the surviving suffix while the
selected checkpoint and bounded WAL range remain intact. The global
induction must cover these outcomes from the actual source execution.
[Premise provenance](#premise-provenance) · [Open obligations](../proof-roadmap.md#completion-checklist-for-native-key-value-refinement)

[frame]: https://github.com/alvoki/alvoki-lean/blob/283de70b489be6efc8197ae25a5b525ddeb57b19/lean/Alvoki/Storage/Disk/NativeCheckpointFsyncEffects.lean#L18
[authority]: https://github.com/alvoki/alvoki-lean/blob/283de70b489be6efc8197ae25a5b525ddeb57b19/lean/Alvoki/Storage/Disk/NativeAlignedWriteRecovery.lean#L775
[sample]: https://github.com/alvoki/alvoki-lean/blob/283de70b489be6efc8197ae25a5b525ddeb57b19/lean/Alvoki/Storage/Disk/NativeCheckpointFinalManifest.lean#L524
[window]: https://github.com/alvoki/alvoki-lean/blob/283de70b489be6efc8197ae25a5b525ddeb57b19/lean/Alvoki/Storage/Disk/NativeRawUncertainWrite.lean#L123
[entry]: https://github.com/alvoki/alvoki-lean/blob/283de70b489be6efc8197ae25a5b525ddeb57b19/lean/Alvoki/Storage/Disk/NativeReadyWriteStorage.lean#L74
[ledger]: https://github.com/alvoki/alvoki-lean/blob/283de70b489be6efc8197ae25a5b525ddeb57b19/lean/Alvoki/Storage/Disk/NativeExecutionTrace.lean#L881
[replay]: https://github.com/alvoki/alvoki-lean/blob/283de70b489be6efc8197ae25a5b525ddeb57b19/lean/Alvoki/Storage/Disk/ClientReadTrace.lean#L344
[checkpoint]: https://github.com/alvoki/alvoki-lean/blob/283de70b489be6efc8197ae25a5b525ddeb57b19/lean/Alvoki/Storage/Disk/NativeCheckpointSampledTableOpen.lean#L228
[fold]: https://github.com/alvoki/alvoki-lean/blob/283de70b489be6efc8197ae25a5b525ddeb57b19/lean/Alvoki/Storage/Disk/NativeReadyCallRefinement.lean#L470

## Premise provenance

| Kind | What it supplies |
|---|---|
| Public API scope | An engine-owned dedicated directory and sequential use of each table. Callers follow the session and snapshot token contract. External mutation or non-cooperating lock users are outside this contract. |
| Filesystem and device | An already durable root and stable managed namespace, truthful listing through clean EOF, correct no-follow identities and extent and byte observations, append preservation of settled prefixes, and file and directory sync, rename and joint crash outcomes as specified. Process exit and power loss have different effects. |
| Native implementation | Lean compilation and runtime behavior, Linux FFI effects, real path and flock behavior, checked listing and descriptor operations. Completeness of the observed lock reference census matters to last-close, fork and exec behavior. |
| Internal and discharged | An executable guard establishes the phase or preparation result, a particular step preserves a world invariant, and an admitted reader plus actual effects establish its installation. Cite the producing theorem when passing such a fact to a consumer. |
| Internal and open | Justify each `Reports` producer from the ordered production input and effects. Establish admission coverage and scope for exact first and later returns, errors and stops. A local healthy dispatch report establishes a selected route only. |

For the same-directory rename of `WAL.next` onto the keeper, the crash
contract allows one prior managed-name map or that map with the whole rename
applied. In the latter case the canonical name binds the staged inode, its
bytes are the synced prefix, and the scratch name is absent in that same
map. A returned error can occur on either side of the live rename effect.
Atomic recovery of both names across power loss is a filesystem assumption.
The native fault tests observe live syscall effects and process reopens.
[Keeper rename contract and error proof](../../lean/Alvoki/Storage/Disk/NativeLongKeeperRenameError.lean)

Availability of a healthy attempt and sufficient resources belong to progress claims. The current
native assumptions and the recorded runtime limitations are in the roadmap. Fixture observations
support those assumptions on exercised Linux runs. [Filesystem contract](../proof-roadmap.md#filesystem-assumptions-and-detailed-proof-targets) · [Native bindings](../../lean/native)

## Specification review

- An acknowledged put batch followed by a reboot that drops one row and adds an unsubmitted row
  violates ordered batch retention. Check that the actual acknowledgement necessarily produces
  its event. A report consumer alone gives no contradiction if the observed path never admits a report.
- If the marker-selected WAL extent reaches ordinal 7 and the checkpoint watermark is 5, recovery
  needs ordinal 6 first. A valid checksum on frame 7 cannot make a physical gap valid. The allowed prefix is a durable WAL
  interval under one selection. A dropped uncertain batch in an earlier session can be followed
  by legal writes after restart. [Ordinal checking](../../lean/Alvoki/Storage/Disk/WriteAheadLog.lean)
- At a successful open, try to prove a successful lookup using another table or phase heap. The
  opened position must rule out that mismatch. A client-supplied foreign pin should instead reach
  its defined denial. For progress, test an admitted error with no ready installation and check
  that the theorem states the conditions under which a later attempt must succeed.

## Checkpoint pilot

The parent claims are [checkpoint publication](#checkpoint-publication), [recovery and retry](#recovery-and-retry)
and [snapshot reads](#snapshot-reads). Previously the early file cut reached an exact table while the
first directory cut had its own trace report. The latter reassembled an opened position. The pilot
preserves each cut's distinct primitive evidence and reuses the same ready witness after selection.

1. A run-file stop consumes the original pending cache entry and keeps the issuing descriptor live.
   The first directory stop uses the cached directory descriptor after run slots are closed.
   Both can end the finite execution without a checkpoint result or proceed through a reported reboot.
   [Raw issued-stop and reopen proof](../../lean/Alvoki/Storage/Disk/NativeOpenedEarlyCheckpointReport.lean) · [Terminal prefix](../../lean/Alvoki/Storage/Disk/NativeExecutionPrefix.lean)
2. The shared early proof takes one admitted survivor and chronological reader. The aligned
   installer returns the actual table and heap. The shared trace step uses that literal
   position with the issued stage, effect and previous manifest. There is no second constructed
   ready position. [Selected early reboot](../../lean/Alvoki/Storage/Disk/NativeQuietPowerLossTableOpen.lean) · [Logical trace](../../lean/Alvoki/Storage/Disk/NativeExecutionTrace.lean)
3. `NativeOpenedSessionTrace.stopsCheckpointEarlyAndReadsLatest` follows the public acquire and read
   on that returned table with its issued pin. Under the actual same-token comparison it derives
   the exact point or range result from replay and extends the existing read ledger.
   [Source and replay of the next read](../../lean/Alvoki/Storage/Disk/NativeOpenedSnapshotSessions.lean)

The challenging third case is a returned rename error after the rename effect. The reported
survivor can keep the old manifest and watermark or select the synchronized new manifest at the
committed history length. Both selections keep the acknowledged replay.
Its selected reads prove their own identities and still feed the same aligned installation theorem
and session induction. This constrains the shared contract to one particular selected reader and
chronology without forcing the previous manifest or watermark on callers. The explicit acquire/read
theorem above specializes the two early stops. [Exact manifest-rename reopen](../../lean/Alvoki/Storage/Disk/NativeCheckpointManifestRenameTableOpen.lean) · [Watermark proof](../../lean/Alvoki/Storage/Disk/NativeCheckpointWatermark.lean)

The first integration build surfaced two maintenance proofs that could no longer eliminate disjoint
events. The shared event tag depended on a match over opaque recovery evidence. A direct event
constructor carrying the issued step lets Lean distinguish event variants at the trace boundary.
The existing maintenance proofs elaborate with that representation and keep their statements.
[Trace event and ledger](../../lean/Alvoki/Storage/Disk/NativeExecutionTrace.lean) · [Maintenance bound](../../lean/Alvoki/Storage/Disk/NativeRotatedMaintenanceBound.lean)

## Evidence and checks

| Claim or route | Kernel and composition | Executable coverage | Remaining premises | Runtime evidence |
|---|---|---|---|---|
| Client history from fresh open | Fresh installation and finite replay compose for the supplied reports. Terminal replay uses the reached-prefix interface. | Exact interpreted `open`, then supported ready, restart and ending paths in their respective interfaces. | Total report derivation and a common raw start-to-terminal witness. | Sequential and batch fixtures. |
| Latest snapshot after an early checkpoint stop | One proof composes both cut types with a successful value or range that agrees with replay. | Issued run fsync or first directory fsync, reported reboot, returned table, acquire and read on its pin. | Allowed reboot and healthy aligned callback observations, same-token comparison and overall operational coverage. | Process exits before and after both fsyncs, then read and write. |
| Old or new manifest after a rename error | Two selected authorities use the shared aligned installer and enter finite sessions. | Actual returned rename error and a reported direct aligned reopen. | General derivation from reached primitives and retries for additional paths. | Returned errors before and after real rename. The old survivor after an effective rename is a modeled power-loss outcome. |
| Reclamation and resources | Preservation and named-disappearance proofs for covered collectors. Conditional work and byte bounds. | Reported eligible collection and selected recovery schedules. | Eventual scheduling, healthy completion across remaining paths, allocator and live-reference bounds. | Native barrier and collection fixtures, instrumented recovery workloads. |

The integration runs the repository's kernel and axiom checks, the native fault and process-death
fixtures, and reproduction. The targeted Linux process-exit checks for the two early fsyncs exercise
each before and after effect, compare the prior selected inode identities and bytes, and check a read
and a new write on the reopened table. Native tests exercise observed process outcomes. The
hard-crash choices, including an old survivor after effective rename, are quantified by the formal
filesystem reports. [Sequential checks](../../scripts/check-sequential.sh) · [Replay reproduction](../../scripts/reproduce.sh)

After building the import with the pinned Lean toolchain, query the actual elaborated declarations.

```sh
cd lean
lake build Alvoki.Storage.Disk.NativeOpenedSnapshotSessions
lake env lean --run Alvoki/Checks/ProofDependencies.lean \
  Alvoki.Storage.Disk.NativeOpenedSnapshotSessions \
  Alvoki.Storage.DiskSession.NativeOpenedSessionTrace.stopsCheckpointEarlyAndReadsLatest \
  Alvoki.Storage.DiskSession.NativeExecutionTrace.keyValueRefinement
```

Run the probe with trusted repository build artifacts because it loads the compiled module environment
and its initializers. It shows direct references in declaration types and proof bodies, alongside transitive
axioms. For example, `keyValueRefinement` uses `NativeExecutionTrace.ledgers`. The extracted pilot
chain follows the snapshot theorem through `NativeOpenedEarlyCheckpointReport.reaches`,
`RawQuietRestartEffects.reopensSelected` and its aligned adapter to
`RawAlignedCheckpointReopenEffects.installsAtReportedPosition`. Each edge is a direct reference.
A missing body is labeled in the output.
Follow declarations from the claim sections for further queries. The probe reports references in the
compiled Lean environment. Executable path coverage and premise provenance are reviewed against the
source and contract above. [Dependency probe](../../lean/Alvoki/Checks/ProofDependencies.lean)

The architecture review also probed the fresh-open theorem, the opened-session induction and
`NativeExecutionTrace.keyValueRefinement`. The first two declaration types reference
`NativeOpenedSessionTrace.Reports`. The fresh-open proof calls the session induction, and the
session induction uses `NativeOpenedSessionReport.reaches`, `.common` and the key-value
refinement. The latter uses `.ledgers`. All three have only `Classical.choice`, `Quot.sound`
and `propext` as transitive axioms. This locates the open premise at the execution boundary.

## Research applied here

FSCQ motivates a separate condition at an issued crash and an ordinary postcondition after a returned
call. Argosy's recovery refinement motivates passing the actual reached state into each attempted
recovery, including an interruption during recovery. In Alvoki that state must retain the selected
checkpoint and WAL identities until the exact next installer consumes them.
[FSCQ and Crash Hoare Logic](https://dspace.mit.edu/entities/publication/0aa2b42b-3078-4bd5-93d3-4bc406534381) · [Argosy and recovery refinement](https://doi.org/10.1145/3314221.3314585)

IronSpec motivates checking that the specification rejects counterexamples independently of the
implementation proof. In the pilot review, a Lean check admitted a one-row fragment of a two-row
uncertain batch under a sublist-only rule. It rejected the same fragment under
`DatabaseSubmissions.Retains`, and rejected replacing an acknowledged row with an unsubmitted row.
[Batch retention](../../lean/Alvoki/Storage/Disk/SegmentedBatchDatabaseTrace.lean) · [IronSpec](https://www.usenix.org/conference/osdi24/presentation/goldweber)

The shared marked installation now takes the descriptor inventory at the actual next open. A local
keeper projection links the visible name to the inode's current bytes through failed repairs and
cleanup. The protected checkpoint frame supplies the exact manifest and selected run payloads at
that same open. A final directory fsync error before effect can leave a replacement live while the
old inode can still survive a subsequent power loss. The live retry proof uses the reached name,
while the crash proof requires a separate correlated survivor observation. The installation still
uses reported healthy primitive callbacks. The fixed-source execution must derive those reports.
[Reached raw open](../../lean/Alvoki/Storage/Disk/NativeSelectedWriteReopen.lean)
· [Final fsync effects](../../lean/Alvoki/Storage/Disk/NativeLongKeeperFinalSyncObservation.lean)

## Why adding cases is expensive

The architecture review uses GitHub `main` at `e71b55afbb3a5bd963a0320affda01c986bf131a`.
The native storage sources match the pilot revision above. The following findings explain which
work is essential and which can be shared.

| Finding | Consequence | Evidence at the reviewed revision |
|---|---|---|
| The opened session trace joins ready positions. Its 15 action constructors are represented by 17 report constructors and 17 step constructors. Several actions bundle an interruption, a release or reboot, retries and a successful open. | A new combination needs a new high-level report, branch and matching proof. A prefix ending while recovery is still unavailable belongs to a different interface. | [Opened actions, steps and reports](../../lean/Alvoki/Storage/Disk/NativeOpenedRestartSessions.lean#L144) |
| The terminal interface separately represents requested endings, derived endings and observations. There are 36 ending and 36 observation constructors. `reachesPrefix` needs both successful-prefix reports and a terminal observation. | A cut that can end a trace and also allow a future open needs evidence at both interfaces. The terminal existential history does not quantify over each particular independently observed crash survivor. | [Endings](../../lean/Alvoki/Storage/Disk/NativeExecutionPrefix.lean#L68) · [Observations](../../lean/Alvoki/Storage/Disk/NativeExecutionPrefix.lean#L448) · [Prefix producer](../../lean/Alvoki/Storage/Disk/NativeExecutionPrefix.lean#L639) |
| Both fresh bootstrap and the opened-session induction accept `Reports`. Ready write and checkpoint observations also take source returns paired with specific operation reports. | The replay argument is already reusable. The direction still needed for coverage is from one independently observed execution to the facts required by that replay. | [Fresh raw open](../../lean/Alvoki/Storage/Disk/NativeFreshOpenedSessions.lean#L27) · [Per-call observations](../../lean/Alvoki/Storage/Disk/NativeOpenReadyTrace.lean) · [Report premise](../../lean/Alvoki/Storage/Disk/NativeOpenedRestartSessions.lean#L382) |
| Finalized read-only retries join at an exact heap, but each held failure can provide its own `recover` callback. The retry preservation result frames a projected file image and descriptor inode map. | Reuse exact heap adjacency and cleanup. To cover public `open`, fix the same source worker across attempts and relate its actual selected bindings and bytes. A repair error can change the image before cleanup. | [Finalized attempt](../../lean/Alvoki/Storage/Disk/NativeFinalizedOpenRetries.lean#L14) · [Retry preservation](../../lean/Alvoki/Storage/Disk/NativeFinalizedOpenRetries.lean#L211) · [Source dispatcher classification](../../lean/Alvoki/Storage/Disk/NativeRawRecoveryReturn.lean#L71) |

The checkpoint pilot is evidence that sharing a recovery endpoint pays off. A run-file fsync and a
first directory fsync reach different descriptor and cache states, yet both reuse the selected-file
installation proof. A manifest rename that returns an ordinary error after taking effect can use that same
installer with either watermark. The pilot still classifies the cut separately from the facts used
by its terminal and reopen consumers. Sharing one reached checkpoint outcome is the next structural
test. A proof about the descriptor on which fsync was issued or the name that became durable remains necessary.
[Early checkpoint report](../../lean/Alvoki/Storage/Disk/NativeOpenedEarlyCheckpointReport.lean) · [Shared installer](../../lean/Alvoki/Storage/Disk/NativeAlignedCheckpointReopenEffects.lean)

## Target execution argument

**Public theorem.** For every finite execution of the supported sequential `DiskTable` API starting
at a fresh managed directory, under the stated native and filesystem assumptions, derive a legal
client history for those same calls and outcomes. Every acknowledged group appears in order. An
unresolved submission can be omitted or retained whole according to the actual durable selection.
No rejected or unsubmitted mutation can appear. One replay explains each successful point and range
response at its issued pin and each returned ready table at its reached committed prefix. Guarded
denials, including use of an old pin on a new table, match the public result. Safety includes finite
executions ending before an API response or immediately after a rejected open. For each admitted
joint crash image the theorem applies to the trace that selects that image. Healthy completion,
maintenance progress and physical space bounds have separate conditions. [Client and format behavior](../specifications.md) · [Filesystem assumptions](../proof-roadmap.md#filesystem-assumptions-and-detailed-proof-targets)

Build the argument with the following boundaries.

1. **Observe one source execution.** Interpret the existing production schedules with primitive
   outcomes at the reached heap. A call returns a value or an ordinary error with its effects, or
   the prefix ends without an API response, either between primitives or within an issued primitive.
   The reached state carries the effects so far and the concrete target of any issued call.
   A process exit updates custody separately. A power loss
   chooses one joint survivor from the reached state. Derive exhaustiveness from the schedule and
   primitive contracts. Defining admission in terms of the existence of a high-level report would
   leave coverage circular. [Native API and schedule equalities](../../lean/Alvoki/Storage/Disk/DiskTable.lean)
2. **Preserve one invariant at adjacent states.** At the native layer carry the managed root, live
   descriptions and locks, and file bindings and bytes necessary for the next effect. Describe
   durability on objects, so a sync of a stale descriptor cannot settle a replacement at the same
   pathname. At the protocol layer require the checkpoint and marker-selected WAL at each allowed
   selection to represent the settled history and the allowed whole pending submission. Track the
   actual in-flight, poisoned or released state so the next step has the correct obligations.
   Expose a ready-table relation only after the installer succeeds, with its literal table, phase,
   cache and token. Identity, custody and crash correlation remain indexed where a later step uses
   them. [Descriptor and inode example](../../lean/Alvoki/Storage/Disk/ReplacedWalDescriptor.lean) · [Pending history](../../lean/Alvoki/Storage/Disk/PendingClientReplay.lean)
3. **Compose single steps.** Treat operation completion, interruption, exit, reboot and each open
   attempt as independently composable steps when their reached states match. Derive the exact
   returned open or error from the same worker, cleanup and installer across the sequence. Prove
   induction from durable empty state over that concrete chronology. Reuse the existing client
   replay and read results at ready points, and prove the between-session invariant carries prior
   observations and all allowed durable histories. A compound success scenario becomes a corollary
   of the same induction. [Ledger and replay](../../lean/Alvoki/Storage/Disk/NativeExecutionTrace.lean#L888) · [Snapshot refinement](../../lean/Alvoki/Storage/Disk/ClientReadTrace.lean)

The first observed acknowledgement can start from the fresh open's returned cache
and established storage. For the early checkpoint, terminal refinement can use a
ledger from those raw acknowledgements. The same reached source stop and its
protected storage also yield the chosen reboot observation. One bounded aligned
interpreter follows a finalized MANIFEST stat rejection and opens at its actual
cleanup heap with the same selected checkpoint and WAL bytes. This still takes
the local reboot projection and aligned callback receipts. The early checkpoint
pilot joins both stops through the recovered snapshot. The later publication
cuts still need the selected-file argument.
[Fresh acknowledgement](../../lean/Alvoki/Storage/Disk/NativeFreshOpenedSessions.lean)
· [Source checkpoint reopen](../../lean/Alvoki/Storage/Disk/NativeCheckpointSourceReopen.lean)
· [Early checkpoint pilot](../../lean/Alvoki/Storage/Disk/NativeFreshCheckpointReplay.lean)

Ordinary `IO.Error` and interruption must remain distinct even when they involve the same fsync.
The first and final directory sync can also use the same path and descriptor with different
publication consequences. Their stage must come from the reached continuation. Across an open
failure, an unlock error can replace the outward diagnostic, and a surviving lock alias can still
prevent admission. Those facts belong to the operation, release and admission proofs. The client
replay consumes the derived history and responses. Each retry inherits the allowed alternatives from
the exact reached files. A failed open can observe a marker that a later reboot is still allowed to
lose. Resolve an uncertain write once the authority settles, including a barrier that took effect
before an error, or a successful open exposes the recovered history. Subsequent retries must preserve
that decision. Until then the invariant carries the allowed alternatives and accounts for effects
that narrow them. The runtime, FFI and filesystem assumptions remain explicit at the source
boundary. The traces and invariants
can be verification-only. [Append and retry selections](../../lean/Alvoki/Storage/Disk/AppendRetrySession.lean)

For a failed storage call, prove the error at its return and the state
that the next restart sees. A read-only open failure frames the selected
files. A mutating failure supplies the updated bindings, durable choices
and lock custody. Both feed the same next-open proof, which starts with a
new session and reuses the files on disk. Require a separate proof case
only when an outcome changes those obligations or a public response.
Recovery progress is conditional on readable, valid selected files and
the required I/O succeeding. A permanent read failure can keep rejecting
open without returning an invented empty database.

One failed bounded repair can now extend the actual failed-call prefix on
the fixed marked opener. The bounded schedule composes local frames
through its callbacks, and shared admission and finalizers
carry the frame to the exact error heap. The keeper has its own live
binding and payload after replacement. The protected live and durable
files and the root's binding in its parent survive separately. The same
lemma accepts a WAL target selected after different operations, under
the supplied writer's manifest and protected footprint.
[Failed marked repair](../../lean/Alvoki/Storage/Disk/NativeLongKeeperFinalSyncObservation.lean)

After a successful replacement rename and a final sync error, the
actual returned heap has the selected live keeper and no later WAL
names. The next healthy open uses that image to derive the aligned
worker branch from its observed extent. The collection of local
read, sync and allocation effects then applies to that branch on
the same interpreter. The ready table carries the selected replay
and the physical entry used by later writes. Admission still depends
on the observed lock state.
[Ready writer from aligned retry](../../lean/Alvoki/Storage/Disk/NativeAlignedWriteRecovery.lean)

The late WAL publication proof derives the public `commitUnknown`
return from the actual prepared write and its failed commit callback.
The reported reboot samples that exact failure heap. The selected
history and ready replay follow through the same retry prefix, using
the original write request and public diagnostic in the ledger. The
source proof covers marker rename and final directory sync errors
with one selected-recovery continuation. Its write entry and the new
table's own pin carry an observed acknowledgement and snapshot into
the same ledger. The continuation also extends the checkpoint and
grouped-write ledgers.
[Late write and ready recovery](../../lean/Alvoki/Storage/Disk/NativeLateWriteRecovery.lean)

Read-only failures frame the keeper they enter with. A repair failure
can supply a replacement to the same prefix. Both carry the protected
files and parent settlement at each returned heap, so grouped recovery
can consume one prefix through the fixed interpreter.
[Retry frames](../../lean/Alvoki/Storage/Disk/NativeDurableWriteReboot.lean)

The raw longer-keeper proof uses the descriptor returned by the staging
acquisition. A direct create proceeds to write and flush, and a retry
first follows the no-follow check and guarded detach after `EEXIST`.
The frame composes the effects of the callbacks that ran, including any
reached error. The first write and flush after a collision follow the new
description. The Linux proof still needs the namespace and inode
effects of those callbacks to establish the selected physical footprint.
[Staging proof](../../lean/Alvoki/Storage/Disk/NativeLongKeeperSuffixStageHeap.lean)

For a completed staged-file fsync, the observed successful exclusive
create supplies the disjoint inode and empty contents. The reached
write and flush establish the bytes on that inode, and the pending
descriptor identifies the file fsync. Its local effect makes those
bytes durable and frames all protected files and the root in its parent.
The rename keeps the same inode and its durable bytes while moving its
visible binding. A final directory-fsync error carries that binding and
payload under either effect. Only the effective branch settles the new
keeper name in every crash map. The actual cached directory load and
reported fsync supply the bounded repair error. Cleanup carries the
renamed inode and its durable bytes to the exact fixed opener's error
heap. The resulting selected retry prefix supplies the next healthy
aligned open. Connecting its ready ledger to the complete mixed
execution remains open.
[Staged keeper storage](../../lean/Alvoki/Storage/Disk/NativeLongKeeperStorage.lean)

The ordinary `commitUnknown` result supplies the actual prepared group and one reached
publication outcome. The grouped failure producer follows both literal fsyncs and preserves
the old marker and keeper prefix. After a successful file group, the local rename and
root-sync effects determine the allowed marker selections on the reached heap. Before an
effective directory barrier, the visible marker may already have changed while an older
binding remains admissible on reboot. Once the directory effect settles the rename, a
reported fsync error is compatible with a definite new marker. These results derive a
bounded repair target from one chosen map and its selected manifest, marker and keeper
bytes. The post-group payload observations and native effect laws remain explicit. The
grouped file-sync error now supplies its target directly to the recovery worker. The marker
rename and final directory sync errors use the same joint sampling and repair fold. Each
local late-publication proof supplies its exact commit return and reached payloads.

The public uncertain write's exact returned error and heap now classify the literal
publication stage for the custody and grouped-error proofs. A grouped error reaches the
old target through the observed joint reboot. Selected durable files and the live keeper
can use the same failed-call fold with their own local frames. The aligned branch uses the
exact selected successful open to establish its physical writer entry. At that writer the
old-target ledger joins the next observed nonempty acknowledged write and snapshot. The
new write requires its own primitive effect laws, and the snapshot requires the live-token
comparison. These lemmas supply the individual transitions for a combined execution.
[Source classification](../../lean/Alvoki/Storage/Disk/NativeRawUncertainWrite.lean)
· [Aligned writer](../../lean/Alvoki/Storage/Disk/NativeAlignedWriteRecovery.lean)
· [Write and snapshot](../../lean/Alvoki/Storage/Disk/NativePublishedWriteSnapshot.lean)

At the first runs-directory fsync, each successful run write and file
sync has its own reached heap and inode effect. Folding these frames over
the source-derived prefix preserves the previous selection. The directory
stop uses the cached root descriptor. Its scoped crash-map contract
distinguishes durable child names from the root name in the parent.
The physical result can feed a stopped ledger or an admitted reboot.
[Runs-directory stop](../../lean/Alvoki/Storage/Disk/NativeCheckpointStopContinuation.lean)

The integrated early checkpoint pilot starts with the justified fresh returned
table and its settled storage. One confirmed nonempty write provides the exact
heap and cache for the interpreted checkpoint call. The derived stop supplies
both a terminal ledger and the physical bytes from which a single admitted
reboot is chosen. One fixed opener returns the MANIFEST lookup diagnostic and
then the aligned table. The acquired token and snapshot on that exact table
extend the original writer's ledger and agree with WAL replay. The theorem uses
local primitive observations, a selected reboot and a successful aligned repair.
The two early stops differ in their physical frames and share the rest of the
argument.
[Fresh checkpoint replay](../../lean/Alvoki/Storage/Disk/NativeFreshCheckpointReplay.lean)

The quiet checkpoint continuation uses one fixed marked interpreter for
the MANIFEST lookup rejection and the subsequent aligned open. The error
comes from that interpreter's cache-disposal and lock finalizers. The retry
starts at the exact cleanup heap. Its two marked workers agree at the
held entry because the same measured keeper is aligned and needs no
staging. The allocated cache and reference constructor identify the
returned table and heap. The chosen reboot and each call's primitive
effects are explicit.
[Fixed source reopen](../../lean/Alvoki/Storage/Disk/NativeCheckpointSourceReopen.lean)

The final checkpoint proof carries the same sampled durable files and
parent-directory settlement through the actual framed failed opens to the
healthy aligned reader. Its selected manifest and WAL layout determine the
files the reopened writer must protect. The descriptor census, actual
syncs and newly allocated phase and token establish the write entry on
the returned table and cache. A subsequent observed nonempty write on
that handle appends exactly its acknowledged batch. The following snapshot
agrees with replay of the preceding history and that batch. The proof uses
scoped reset, failed-open, repair and write effects.
[Checkpoint reboot, next write and snapshot](../../lean/Alvoki/Storage/Disk/NativeCheckpointSampledTableOpen.lean)

The fresh bootstrap return supplies the empty origin for this continuation.
The existing opened-session trace supplies the prefix on its exact table.
The current cache identifies the starting checkpoint heap, and the source
schedule reaches the stop during the final directory fsync.
The recovery extends that prefix ledger with the next confirmed write and
snapshot. Constructing the prefix and its recovery extensions for raw mixed
calls remains an obligation of the integrated execution theorem.
[Fresh final checkpoint pilot](../../lean/Alvoki/Storage/Disk/NativeFreshFinalCheckpoint.lean)

The source checkpoint stop has one terminal case for every reached stage.
The source call and poisoned phase identify the stop, and the existing
client ledger supplies its logical replay. The early recovery proof carries
the earlier physical storage separately, and later recovery uses the
sampled manifest and each file it selects.
[Terminal checkpoint stop](../../lean/Alvoki/Storage/Disk/NativeEarlyCheckpointTerminal.lean)

The late source prefix identifies each new run write and its returned
file fsync on the same remembered descriptor. The file effects give
singleton durable bytes at the written inodes. At the returned first
directory barrier, the scoped child-name effect settles the new run
bindings. The actual staged MANIFEST fsync also uses the descriptor
remembered by its own write. These settled files can be sampled by the
final manifest selection on the same source prefix.
[New run durability](../../lean/Alvoki/Storage/Disk/NativeCheckpointRunDurability.lean)

At the final manifest-directory stop, the source order determines the
preceding successful replacement of MANIFEST. The returned prefix exposes
its entry and return heaps and the cache used to resolve the directory of the
stopped fsync. A returned rename error follows the ordinary error channel.
The final selection proof uses this receipt for the correlated manifest
and protected file bindings.
[Manifest-directory source order](../../lean/Alvoki/Storage/Disk/NativeOpenCheckpointScheduleStop.lean)

At the first run fsync, the completed prefix contains the run write. The
literal write determines the heap before sync and frames the selected files.
Pending-cache removal and the stopped fsync provide a second frame. Both
consume the same storage observation and compose with the phase-update
frame. Longer prefixes can use the returned-step fold with the same sync
frame. A storage fact at the stop can feed terminal refinement and the
selected reboot independently.
[Checkpoint stop frames](../../lean/Alvoki/Storage/Disk/NativeCheckpointStopContinuation.lean)

A held MANIFEST lookup error and its actual cleanup supply a singleton failed-call
trace and the precise frames required by the grouped retry pilot. A later admission
still needs its own lock-vacancy observation. The fresh installer exposes the cache
references and builds the first write entry from the reached descriptor census and
settled empty files. A successful write supplies the prepared batch and byte bound
directly from its source result. These transitions provide the inputs for a proof
that composes the initial open, writes and subsequent recovery.
[Exact MANIFEST retry](../../lean/Alvoki/Storage/Disk/NativeCheckpointOpenChronology.lean)
· [Fresh writer](../../lean/Alvoki/Storage/Disk/NativeFreshOpenedSessions.lean)

The grouped retry pilot composes these steps at their exact reached heaps. It requires
a nonempty sequence of literal failed opens and derives the next batch and byte bound
from the fixed successful write. It uses the same physical observation throughout.
It begins at a ready writer with one admitted durable reset and local primitive
effects, including frames for the failed calls. The MANIFEST lookup failure proof
can derive those frames from the actual admission, lookup, cache disposal, unlock
and release. Fresh initialization, checkpoint stops and full dispatch coverage remain
open in the broader execution proof.
[Grouped retry and snapshot](../../lean/Alvoki/Storage/Disk/NativeGroupedWriteSnapshot.lean)

The selected batch target supplies the same repair plan after a reported reboot or live retry.
The reboot bridge uses one joint map and the bytes sampled at its actual heap. In the grouped
file-sync error branch this map admits the old marker and a keeper that may include an
unacknowledged suffix. The protected frame retains the root, lock, selected runs and seals.
After selection the marker joins that frame, while a separate observation tracks any replacement
of the writable keeper. The healthy opener uses its actual reached descriptor census and matches
the root and lock handles and the selected marker, seals, keeper, manifest and runs to the
observed namespace. The shared return appends one uncertain submission and keeps earlier
snapshot observations for either selected history. The bridge still takes local primitive effects
for the failed and healthy opens, with a vacant lock at the healthy entry.
[Observed reboot](../../lean/Alvoki/Storage/Disk/NativeRawWriteReboot.lean)
· [Selected retry return](../../lean/Alvoki/Storage/Disk/NativeSelectedWriteReopen.lean)

For the grouped file-sync failure, the original ready phase supplies the prepared write. The
actual guard, poison assignment, append, marker stage and failed group determine the literal
`commitUnknown` return. Local frames carry the selected checkpoint across those reached
heaps. One observed reboot supplies the old marker, and the fixed interpreter consumes that
selection across the failed opens and successful installation. The replay ledger for the
returned table retains the previous history and snapshot reads and records the uncertain
submission with zero retained writes. The proof assumes the reported native callback effects,
the joint Linux crash choice and the observations of the individual open attempts.
[Grouped write and recovery](../../lean/Alvoki/Storage/Disk/NativeGroupedWriteRecovery.lean)
· [Replay ledger](../../lean/Alvoki/Storage/Disk/NativeSourceLedger.lean)

The late-publication composition requires retry observations only for the target admitted
by the rebooted manifest and marker. That pair fixes the repair target uniquely among admitted
batch targets. The shared ledger derives the old-or-whole history for the exact source return.
A successful marked installer exposes its own phase and token allocations. The same frame
used by bootstrap preserves the repair output through those allocations, including the
visible keeper bytes needed by the next append. The aligned path without pruning derives physical readiness at the exact returned writer
from the cached directory and keeper fsyncs and the allocation frames. The longer-keeper
path derives readiness before allocation from the staged-file fsync, the rename of that
inode and the final directory fsync. These local steps assume scoped effects of the reached
callbacks, durable protected files, a durable marker and settlement of the root name in
its parent. The aligned retry consumes the durable selected footprint, matches the actual
root and lock, and frames the exact keeper through its bounded read and cache updates.
The one-link stat and a link census at that heap rule out protected names aliasing the
keeper. The successful open supplies the same physical entry consumed by the next
acknowledged write. Aligned pruning and replacement through a fresh exclusive stage
supply that entry through the same allocation proof. The retained-file reindexing,
root and lock identity, and directory-barrier frames are shared. Pruning proves
absence at its repair heap. Replacement follows the new inode through the literal
stage, fsync and rename. The recovery ledger is proved at the same position used by
the next write. An acknowledged write produces the entry again on the same cache
references. The local callback laws and their composition across the full execution
remain explicit, including the guarded staging-collision route.
[Pruned returned writer](../../lean/Alvoki/Storage/Disk/NativePrunedMarkedReady.lean)
· [Replacement returned writer](../../lean/Alvoki/Storage/Disk/NativeLongMarkedReady.lean)
· [Recovery ledger](../../lean/Alvoki/Storage/Disk/NativeSourceLedger.lean)
[Late publication recovery](../../lean/Alvoki/Storage/Disk/NativeLateWriteRecovery.lean)
· [Ready allocations](../../lean/Alvoki/Storage/Disk/NativeOpenReadyStorage.lean)
· [Aligned returned writer](../../lean/Alvoki/Storage/Disk/NativeAlignedMarkedReady.lean)
· [Long keeper repair](../../lean/Alvoki/Storage/Disk/NativeLongKeeperStorage.lean)

The scoped reboot law records agreement with the sampled bindings and singleton durable
bytes for selected regular files. The root's name in the parent remains independently
settled. The failed-call induction can carry the immutable physical footprint alongside
the live keeper, which may change during a repair. For the reopened writer, equal
manifest and run payloads and the retained seal map transport the durable files to
the new ledger. The root and lock are tied to the actual reopened descriptors.
[Durable reboot and retries](../../lean/Alvoki/Storage/Disk/NativeDurableWriteReboot.lean)
· [Reopened footprint](../../lean/Alvoki/Storage/Disk/NativeRetainedOpenStorage.lean)

The actual lock, flock, directory open and cache reference allocation receipts carry a
scoped frame through admission. The same helper serves the successful prefix and the
existing failed-open cleanup proofs. The held manifest, chunk reads, ordered releases,
marker and selected seal reads share one generic frame proof. The checked listing carries
that frame through its actual stream open, iteration and close. These proofs connect the
admission and worker to the exact entry of the keeper read. The aligned return proof now
carries the durable files, names used for alias exclusion, and the live keeper separately
through that prefix and the exact keeper open, chunk reads and pending insertion. Local
physical effects are supplied at the primitive calls. The initial live keeper observation
and the repair barriers remain separate.
[Open admission frames](../../lean/Alvoki/Storage/Disk/NativeOpenAdmissionStorage.lean)
· [Marked scan frames](../../lean/Alvoki/Storage/Disk/NativeMarkedScanFrame.lean)

The pruned aligned path derives readiness at the actual repair heap from the reached
ordered unlinks, directory and keeper fsyncs, and protected file frames. It derives
absence of the removed suffix names in each crash map at that heap. Carrying absence
through allocation also requires frames on those suffix paths. All repair branches
share one transport of readiness through the actual reference allocations.
[Pruned keeper repair](../../lean/Alvoki/Storage/Disk/NativePrunedKeeperStorage.lean)

A returned append or marker-staging error uses the same prior-marker selector as a
grouped file-sync error. Only the append and any reached staging callbacks contribute to
the error heap. Local effect laws preserve the canonical marker and protected names
and bytes. The keeper may grow, and each admitted durable byte choice still extends its
previous committed prefix. Sampling one observed reboot derives the old history, an exact
failed-call sequence and the successful table with the uncertain submission retained as zero
writes. An interrupted callback that has yet to return is a separate case.
[Early write recovery](../../lean/Alvoki/Storage/Disk/NativeEarlyWriteRecovery.lean)

A marked repair that fails after changing files supplies its reached image through the same
worker and finalizers as the read-only error path. The local stage-sync and final-directory
errors share the ordered successful prefix they actually executed. A repair may leave the
original keeper with a durable scratch file or replace it with the trimmed keeper before EIO.
The retry fold retains the selected target and unchanged file footprint while the next reader
plan uses the last returned keeper and later names. The kernel argument tracks reported
Linux effects and distinguishes a returned error from whether its syscall took effect.

One held marked interpreter now fixes primitive callbacks before admission and passes the actual
new cache references to the worker. A successful worker result or a finalized worker error
establishes an exact return of that same call. The selected write retry fold is indexed by those exact failure returns. Read-only and repair observations contribute local facts at the same endpoints through one append rule.
The healthy installation uses the identical callback bundle and the precise cache from its own
admission. The worker result remains a local obligation of its read and repair evidence. The
main execution must derive the individual reports from the primitive schedules to replace the
legacy compound reports.
[Fixed marked interpreter](../../lean/Alvoki/Storage/Disk/NativeMarkedOpenInterpreter.lean)

## Migration test

Keep the codecs, ordered replay, snapshot and retention proofs, publication laws, bounded reads,
and the exact installer. Keep the current scenarios as regression evidence during the migration.
Replace the high-level scenario inputs where the new source argument covers them, then remove
redundant wrappers once their consumers and guarantees have moved. A wholesale rewrite would
re-prove local facts that the proposed induction needs in either design.

Give each operation a proof about the components it observes or modifies. Carry independent
history, ownership and file-selection facts by their frame conditions. When testing the boundary,
vary a checkpoint outcome while keeping recovery fixed, then vary a recovery outcome while
keeping the checkpoint fixed. Both changes should use the same composition rule. Require each
migration to identify the existing consumers it replaces and the scenario-specific code it retires.

Start with the two early fsync stops. Derive one reached outcome from the full checkpoint schedule
and use it both to end a finite prefix and to continue through a reboot. Carry the same survivor
through one failed open and then, in an extension of that exact prefix, through a successful open
and a point or range read on its returned table. Derive the issued prefix and source heap once,
without an independently supplied successful prefix for a second interpreter. Check that an
ordinary earlier EIO and a later directory sync on the same descriptor do not inhabit the early
stop. Then try the effective manifest rename with either survivor and a failed repair that has
already changed the image. These cases test both the shared boundary and the information it keeps.

The next test is a successful acknowledged batch followed by an uncertain one. Show that the same
induction can end after a failed open or continue with the actual returned table. Reject a half
retained batch, invented write, mixed manifest/run image, stale pin and a successful lock acquisition
while an alias still owns the lock. New operation outcomes should require local refinement lemmas
and yield the same global theorem. If a case requires another copy of the session or terminal
argument, inspect which state or invariant the interface is missing before widening coverage.
The [active roadmap](../proof-roadmap.md#completion-checklist-for-native-key-value-refinement)
defines the acceptance checks and tracks work that remains.
