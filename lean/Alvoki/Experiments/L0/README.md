# Experimental L0 composition

This slice runs serialized put, delete, get, explicit flush and recovery
with either the component interpreter or the Linux adapters. It starts
with a durably initialized empty WAL and manifest. The WAL prefix is
retained.

`Native.withOpen root` owns the root for a sequential callback. The root
contains three separate, durably named directories: `wal` contains a
previously initialized segmented WAL, `manifest` contains an initialized
manifest blob, and `tables` starts empty. The wrapper holds a root lock
through recovery and the callback. A table descriptor stays within one
table operation. A failed mutating call invalidates the session, and an
escaped handle is offline after the callback returns. Use a new
`withOpen` to recover. [Native adapter](Native.lean)

The [client contract](Client.lean) observes a map from keys to values. A
successful write applies one mutation. If its outcome is uncertain, close the
session before issuing another write. Successful recovery may observe the
last confirmed map or that map with the one uncertain mutation applied. A
flush changes only the representation, even when its publication is uncertain.

## Executable schedule

[Basic](Basic.lean) uses a `Std.TreeMap UInt64 Mutation` for the last mutation
per key. One WAL batch holds either an eight-byte delete key or a sixteen-byte
put key and value. The codec round trip and batch budget are checked in
[Proofs](Proofs.lean). The absolute WAL tail is checked before append to
keep every admitted write representable by a manifest watermark. In this
slice the guard computes the tail from the scanned view, which is linear
in the retained batches. Native wiring can maintain a checked session tail
using the WAL's acknowledged append position.

Flush creates one durable sorted, unique table, prepends its ID to the
manifest, and clears the memtable after publication returns successfully.
Recovery reopens the manifest and the WAL, checks the referenced tables,
and replays the retained suffix strictly after the watermark. Only a miss
falls through to older tables. A tombstone stops the search and a backend
read error propagates. The caller serializes all operations, discards a
session after a mutating error, and reopens before proceeding.

## Verification boundary

[ComponentContract](ComponentContract.lean) projects adapter state to a
selected WAL view, typed manifest and immutable table bindings.
The operation proofs consume only the callback outcomes and their frames.
An append changes only the WAL, a publication changes only the manifest,
and table creation returns a fresh ID and preserves older bindings.
Read and reopen callbacks may change private state while preserving the
selected image. [Component proofs](ComponentProofs.lean) discharge these
laws for the concrete [interpreter](Model.lean). The LSM proofs use the
freshness guarantee without making assumptions about ID allocation.

[RecoveryChoices](RecoveryChoices.lean) works directly with public WAL and
DurableBlob steps. A failed reopen preserves the possible values. A
successful reopen narrows them to the returned value, even if the other
component or a later table open then fails. Closing and retrying the
already-opened component preserves that singleton. During recovery
attempts the LSM issues no mutations, and the table catalog is framed.
`Retry.afterAppend` and `Retry.afterPublish` isolate the one possibly
uncertain component. `Retry.preservesDurability` carries the invariant
from the initial choices to every pair still admissible after partial
recovery. For a given trace, a pair selected by successful recovery can
therefore stand for the earlier unresolved choices. The interpreter
represents such a pair by selecting it at the cut. Native recovery opens
the manifest, attaches the WAL and checks the tables before exposing a
session. A failure consumes the phase cell and closes the attached WAL.
The public-step argument leaves physical crash modeling to the components.

[ReadErrors](ReadErrors.lean) proves that the shared schedule propagates a
required lookup or table-open error with its reached state. The lookup
stops instead of returning an older value. Failed recovery returns no
session. The default interpreter supplies healthy catalog reads; the
regression injects errors through the same table callbacks.

[Refinement](Refinement.lean) relates three views of the database:

- The manifest watermark `F` lies between the WAL base `b` and tail `t`.
- The durable newest-first runs represent the last mutation for each key
  through `F`, including tombstones.
- The memtable represents the latest mutations in `(F, t]`. Replay skips
  `F - b` batches from the retained WAL.

An old manifest replays the still-retained flush input. A new manifest
finds that input in its new table. The two paths yield the same logical
state. The invariant and recovery proof allow a nonzero WAL base. The
executable interpreter starts at zero and has no release operation.

## Composing the native observations

[Trace](Trace.lean) proves client refinement for arbitrary finite executions
from the laws of the reached operations. The interpreter projects to that
trace and separately proves healthy recovery. [Lifecycle](Lifecycle.lean)
proves the transitions of the phase cell used by the native wrapper:
attachment keeps the session private, only a phase owning a WAL can publish
a session, mutation hides it, and cleanup first consumes the handle and
installs the offline phase.

[ScheduleSteps](ScheduleSteps.lean) takes the result of each reached
operation directly to an `Execution.Run` step. The model uses these same
lemmas. [NativeBridge](NativeBridge.lean) derives the operation laws from
component observations. [WalRecovery](WalRecovery.lean) consumes
`publicOpenModel_refines` and the ready-phase scan on the exact installed
session. The public mutation consumes the registration and WAL result in
[NativeMutation](NativeMutation.lean).
[ManifestComposition](ManifestComposition.lean) derives the typed result and
selected manifest directly from the DurableBlob primitive interpreter.
`RecoveryChoices` discharges uncertain effects from the public steps.

The native wrapper and the lifecycle proofs run the same `Cell.withSession`
and `Cell.update` schedules, and get uses the same online guard as its
proof. [LifecycleRefinement](LifecycleRefinement.lean) uses one reached
result for both the phase transition and the generic client trace step.
The native callback record gives component actions no access to the L0
phase cell. The shared interpreter proves phase preservation for write,
flush and get, and derives the recovered WAL attachment on success.
Recovery failure skips the client callback,
moves the cell offline before attempting WAL close, and attempts unlock even
if close fails. Cleanup preserves the original error. Successful recovery
publishes the session with the WAL acquired by that attempt. The table check
and lookup use the same stat and scoped opening schedule. Both pass the
catalog ID to the checked SSTable reader. For the descriptor acquired by
that schedule and serving the exact built bytes,
[TableProofs](TableProofs.lean) derives successful open and typed lookup
from `open_built_table`. Open checks the table ID, footer and root index.
Leaf and data packets are checked on demand.

[TableAllocation](TableAllocation.lean) probes for a free ID and syncs the
parent directory after the builder returns. The creation law now consumes
`buildFileWith_refines` on the reported writer run. It derives the image and
synced inode used to justify the prepared artifact. The directory report
preserves that inode and publishes its name. The L0 row cursor proof
explains the exact encoded suffix and EOF.
[DurableCatalog](DurableCatalog.lean) relates logical rows to their table
ID, durable name, inode, bytes and proven image. The creation proof
produces the new binding, and the catalog insertion lemma retains the
older bindings. Lookup consumes that invariant and the scoped descriptor's inode
selection and read effects. It carries the catalog forward across each
successful miss using the read's namespace frame. The public result
supplies the invariant on success and on a read error. Write, flush and
recovery also return the reached invariant under their local namespace
frames. The caller supplies the invariant at the reached entry state.
`RecoveryEffects` supplies the manifest, WAL reopen and table-check laws.
`FlushEffects` supplies the WAL scan, table creation and manifest publication
laws. The component write model additionally interprets append. `table_open_published_inode` checks the typed producer-to-reader
handoff with `buildFileWith_open_represents`. Checked open validates metadata.
Row validation occurs on demand.

Native check and lookup call the shared `nativeTableAt` adapter.
`nativeTableAt_afterStat` unfolds the executable scope. It propagates
the reached open error, or passes the exact handle from `Handle.mk`
to `nativeTableAction` and forwards its result. No separate action or
scope result is needed. The SSTable producer supplies the typed result
from the immutable image on that inode. [NativeRead](NativeRead.lean) derives the result from the actual stat,
open and scoped read operations. Its frame preserves the represented
manifest and catalog and permits background WAL writeback.
`nativeTableAt_reached` distinguishes stat failure, rejected metadata,
acquisition failure and the outcome of the action on an acquired handle.
For the concrete check and lookup, the descriptor is held in the local
SSTable source and reader. The check discards the opened table. Lookup
decodes to a value or tombstone. Errors carry strings or an IO error.
The reader has no application-state write or user-supplied continuation.
This confines the descriptor on both return branches provided the native
read primitives do not retain the borrowed reference.

The runtime boundary is last-reference release before control returns to
the caller's next operation, for a successfully constructed local handle
with no escaping alias. It frames the protected storage and other owned
resources. Failed construction is a separate boundary. Lean 4.36 on
Linux can leak a raw file descriptor on failed `fdopen`, before a Lean
handle exists. The runtime premise for that error path must exclude this
case or supply its cleanup. See [filesystem assumptions](../../../../docs/design/filesystem-assumptions.md#lean-runtime-resource-pitfall).

The lifecycle proof keeps the namespace on the storage carrier. Changing
phase for publication or cleanup leaves the catalog projection unchanged.
The empty initialization witness starts the client trace, and the lifecycle
consumes the reached catalog postconditions of write, flush, recover and
get. On a returned WAL open error it carries the WAL producer's root and
child release facts for the same disk left by recovery. Healthy recovery derives the typed manifest open and settled image from
healthy blob read, directory open and directory sync reports. It then uses
the WAL progress theorem and the reached table catalog. Each required check takes its inode
and image from that catalog and derives callback success from local
healthy stat, open and read reports.

Bootstrap, WAL release, orphan collection, snapshots, concurrency,
compaction and automatic flush are separate work.

Run `bash scripts/check-experimental-l0.sh` for the interpreter proofs
and regressions. Run `bash scripts/check-native-l0.sh` for the native
fixture, kernel checks and axiom audit. The native fixture rotates the
WAL, flushes multiple tables, checks persistent tombstones and WAL-suffix
replay, retries a failed table open, and checks that a required read
error never returns an older value.

## Producer boundary for native components

These are the producer boundaries in terms of the existing public states
and events. Each premise about a call means a report of the actual
native call, at its reached handle or binding, under that component's
primitive filesystem assumptions. The component owns that interpretation.

| Component operation | Minimal result used by L0 |
| --- | --- |
| WAL `openExisting` and `scan` | `Step offline (.opened view) (.online view)` for the acquired handle and its scanned view. A scan of a ready handle observes that same view. A failed reopen exposes no ready handle and preserves the admissible choices. |
| WAL `append batch` | `Step (.online prior) (.ack (.append batch)) (.online next)` on success. An uncertain append yields the existing offline step with that one pending request. Later reopen supplies its selected view. L0 discards the position in the append reply. |
| DurableBlob `reopen` | `Step offline (.opened bytes) (.ready bytes)` for the exact returned and durably settled bytes. A failed reopen exposes no value and preserves the admissible choices. |
| DurableBlob `publish bytes` | `Step (.ready old) (.published bytes) (.ready bytes)` on success, or the existing uncertain step for those same proposed bytes. Later reopen supplies the selected bytes. |

The WAL recovery interpretation retains the exact public open result,
including the ready store, active child identity and reached disk. A scan
after open uses that phase directly. A reported open failure retains the
recoverable disk, closed phase and the producer's root and child release
facts. A reported append failure keeps exactly the pending encoded change. Recovery
chooses the surviving view on its actual WAL acquisition. A later failure
after that acquisition retains the choice for the next public open.
A lost reply after a successful append retains the extended view on both opens.
If a component opened successfully and a later L0 callback failed, record
the successful component open followed by stop. A scan failure after a
successful WAL open follows this rule too. The integrated callback interpretation executes the typed manifest
schedule over DurableBlob's Linux primitive reports. `CallbackEvidence.recoveryEffects` and
`CallbackEvidence.flushEffects` derive their manifest fields from that execution. Reopen preserves the live
binding on either outcome, including a sync error after the barrier.
Publication success installs the proposal. A returned error can retain
the old live binding or expose the proposal. The reached image is kept
on both paths, including its survivors for later recovery.
[ManifestRecovery](ManifestRecovery.lean) instantiates the manifest
interpretation with that complete image and unchanged WAL and catalog
projections. A process exit keeps the reached image. Power loss selects a
survivor. Both permitted manifest choices are durable against the same
retained WAL and table catalog by `flushPublicationChoices`. A failed open
keeps recovery admissible. A successful open pins its version for another
open, including across another restart.
[RestartRefinement](RestartRefinement.lean) derives both logical choices
from the reached scan and table creation, takes publication reports from
the same manifest interpretation and uses the existing L0 recovery and
client trace after restart. Both boot states use its image installer, which
supplies the WAL and catalog projections. The reopen reports are read
from those reached states. The flush observation records a delivered
success, a reported error, a lost reply or a process interruption.
Delivered success emits `flushed`. Each uncertain observation emits
`flushUncertain` and clears the visible session. Manifest reopen, WAL reopen and table checks
frame the durable catalog through each recovery attempt. Connecting the
reached Linux state to the primitive reports and namespace frames
remains open. The adapter still owes the initial reached catalog witness,
the local creation frames and the correspondence between the restarted
model carrier and the reached filesystem.
The probe frames visibility, the build leaves visibility untouched and
the directory barrier changes only the allocated binding. These local
effects yield exact insertion in the shared schedule. The native adapter
still owes those local effects and the namespace frames.
The filesystem supplies the survivor and the effects of failed barriers.
The client or runtime supplies reply delivery and process interruption
observations.

## Public read dispatch

[WithOpenReads](WithOpenReads.lean) proves a client trace for the concrete
`Native.withOpen` with any finite list of public gets. The caller supplies
a represented initialized root and its prior trace. Root acquisition
establishes ownership of the newly allocated phase reference. Concrete
recovery supplies the installed session, its attached WAL, the settled
manifest and the checked catalog. Publication swaps the owned reference
to online before calling the reader. The first `onlineGet` consumes that
world directly. A failed recovery takes cleanup without invoking the
callback.

Each get emits a client event on success and returns its reached world
on either outcome. The finite-list callback catches every reported
error. `readMany_length` verifies one reply per key and
`readEvents_eq_zip` identifies successful replies in order.
`caughtSizeError_thenHit` specializes this to an actual size error after
descriptor acquisition, its scope exit, and a subsequent successful
public lookup. The final phase swap, WAL close and root unlock consume
the state left by the callback. A cleanup error retains the observed
read trace. `Execution.Run.refines` gives the final `Client.Allows`
and representation witness.

The scoped SSTable proof frames each stat, open, size and bounded pread
and checks the byte image selected by the acquired inode. Both closed
table operations return data without a descriptor. The local runtime
contract observes last-reference disposal at the actual labelled scope
exit, including on a reported read error. The root lock has a separate
scope and unwraps its actual unlock result. Failed `fdopen` before Lean
constructs a handle remains outside the last-reference contract.

[HealthyReads.withOpen](HealthyReads.lean) derives a successful public
scope on an initialized empty root from reports at the reached primitive
calls. Two public misses, WAL close, root unlock and the client trace all
refer to the same evaluation. A manifest metadata error has its own
pre-callback witness in [NativeRecoverAt](NativeRecoverAt.lean).

Against the pre-handoff PR #5 head `5b2e9d30`, 26 of the original 34 L0
Lean files are byte-identical (2,678 lines, including executable and
proof code). The model, codecs, execution relation, catalog and manifest
proofs continue to serve their existing consumers.

The earlier product-carrier get and finite-list scope proofs have been
removed. The abstract flush/restart theorem still interprets a lookup on
its model carrier through `RestartLookup.get`, which invokes the same
scoped native table proof. Healthy model recovery retains its table
check interpreter.

## Remaining premises

| Premise | Owner and producer | Consumer |
| --- | --- | --- |
| Table stat, open, size and bounded pread | Local filesystem contracts bind the successful acquisition to the selected name and inode and preserve the protected resources on both outcomes. Successful reads yield bytes from that inode. Healthy progress additionally requires successful primitives | `NativeRead.tableAction`, `onlineGet` and `checkTables_healthy` |
| Last-reference disposal and unlock | Runtime releases a successfully constructed private handle at its labelled scope return. The filesystem supplies the actual unlock result. Cleanup preserves the observed trace through child close and unlock failures | `NativeRead.Call.Balanced.released`, `NativeReadRelease.root_released`, `WithOpenReads.withOpen` |
| Phase-reference dispatch | Owned reference reads and swaps return the represented phase and preserve the protected footprint. Recovery produces the handle consumed during publication and cleanup | `NativeRead.publishOnline`, `onlineGet` |
| Durable catalog insertion and preservation of unrelated physical bindings | Filesystem create, file sync and directory sync effects. L0 must represent the reached writer and prove local table, manifest and WAL namespace frames | `TableCreationEvidence.catalogInserted`, `catalogAfter` and the lifecycle postconditions |
| Healthy recovery state and primitive reports | The filesystem supplies healthy manifest and table primitives. The manifest interpreter derives the typed open, and `scopedCheck` yields the table callback result. The returned state carries the installed L0 session, physical catalog, stable manifest image and exact ready WAL child, including the original successful WAL open result on the reached disk. L0 still supplies the catalog and manifest frames across WAL open and the manifest/WAL frames across table checks. The model recovery check interpreter retains its product-carrier frames. The native read scope consumes the actual manifest, WAL, table and phase producers | `Lifecycle.recovery_progress` |
| Restart selection, reply delivery and loss | Filesystem survivor choice and runtime/client observations. L0 must connect the resulting image and observations to the interpreter for arbitrary permitted prefixes, including allocation, table creation and the interval before manifest publication. Before a table enters the selected catalog, `retainRecoverySelection` derives the recovery precondition from the unchanged selection and the old inode bindings. After durable creation, `flushPublicationChoices` supplies both selections. Concrete cut coverage remains open | `recoverReachedFlush` and `Execution.Run.flushObserved` |
| Repeated public reads on actual native states | The root-binding, storage and runtime primitive laws establish the state consumed by the next operation. Public mutation uses the recovered child and returns a physical input to both opens. Native flush still needs a producer on the reached state | `WithOpenReads.withOpen` and `Execution.Run.refines` |
| Ready view, recoverability after restart and segmented append | WAL producers for append, rotation, CONTROL and uncertainty selection | `AppendIO.LocalIO.append`, `NativeMutationScope.mutationThenReadTwice` |

## Reuse across append, close and recovery

| Scope | Producer and guarantee | Reuse |
| --- | --- | --- |
| Single-file WAL | `ConcreteRecovery` binds descriptors to file roles and the active cursor. `ConcreteAppend` interprets data and marker writes. `ConcreteCreate` installs a fresh rotating child. | The active and successor branches share the bounded child write proof. A successful successor carries its physical fresh bytes and live directory name before CONTROL can select it. |
| Segmented WAL | `RuntimeStoreOpen` and `RuntimeChild` produce the selected registration. `AppendIO.LocalIO` in `AppendRuntime` composes admission, child IO, CONTROL and slot transfer with PR #26’s append model. | A successful write returns the updated ready authority. Error cleanup receives the actual slot, including the empty slot after detachment. Known and pending opens use the same acquisition worker. |
| L0 | `NativeMutationScope.mutationThenReadTwice` supplies the position guard, change encoding, table/manifest frames, phase publication, delivery and close. `PendingReadScope.twice` passes each reached world into the next public open. | Both reopens consume the existing scoped read and cleanup proof. A reported error keeps the exact issued request. A successful write followed by a lost reply and an acknowledged write share one physical outcome. |

External assumptions describe Linux file and directory effects, handle
and reference ownership, descriptor disposal, and preservation of the
caller’s manifest and table resources by WAL primitives. Root unlock and
last-reference release are separate observations. A failed `fdopen` on
Lean 4.36 can leak a raw descriptor before a Lean handle exists.

## Process interruption checks

The Linux native fixture cuts the child process after the table directory
sync and before manifest publication, or immediately after manifest rename
and before its directory sync. In each case two successful reopens check
the watermark, acknowledged values and tombstones. After the table cut,
a retry also checks that allocation skips and preserves the orphan. The
fixture exercises process exit and release of the root lock. The kernel
retains its filesystem cache, so the rename case expects the new manifest.
