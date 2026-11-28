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
session. The separate model receipt remains only for append.
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
frames. The caller supplies the invariant at the reached entry state. Recovery and mutation use
`ComponentEffects` and have no dependency on a lookup law. `table_open_published_inode` checks the typed producer-to-reader
handoff with `buildFileWith_open_represents`. Checked open validates metadata.
Row validation occurs on demand.

Native check and lookup call the shared `nativeTableAt` adapter.
`nativeTableAt_afterStat` unfolds the executable scope. It propagates
the reached open error, or passes the exact handle from `Handle.mk`
to `nativeTableAction` and forwards its result. No separate action or
scope result is needed. The SSTable producer supplies the typed result
from the immutable image on that inode. The reached result is now computed
by [NativeTableReads](NativeTableReads.lean) from one evaluation of the
native scope. On its product carrier only the IO world is advanced, so
the table namespace and logical projection are structurally unchanged.
The runtime closes the descriptor when its last reference drops. Check and lookup return only
unit or a mutation observation.

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
facts. The open interpretation takes the WAL view as already selected at
the restart boundary. Connecting uncertain native append and later restart
to that selected input remains open. Arbitrary ready states still need a
cached-view invariant, in particular after native append. Close after an uncertain
operation preserves the pending request via the existing offline stop step.
If a component opened successfully and a later L0 callback failed, record
the successful component open followed by stop. A scan failure after a
successful WAL open follows this rule too. The integrated callback interpretation executes the typed manifest
schedule over DurableBlob's Linux primitive reports. `CallbackEvidence.effects`
derives its manifest fields from that execution. Reopen preserves the live
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
the scoped read-result correspondence and the local creation frames.
The probe frames visibility, the build leaves visibility untouched and
the directory barrier changes only the allocated binding. These local
effects yield exact insertion in the shared schedule. The native adapter
still owes those local effects and the namespace frames.
The filesystem supplies the survivor and the effects of failed barriers.
The client or runtime supplies reply delivery and process interruption
observations.

## Public read dispatch

`Native.get` runs the phase check and table lookup in the same `ExceptT`
dispatch, `Cell.get`. `Native.get_afterPhaseRead` identifies the continuation
and its exact entry world from the primitive phase read. The interpreted schedule uses that dispatch as
well. `Lifecycle.getScope_refines` composes a successful interpreted
recovery, any finite list of gets that catches each reported error, and
the shared outer cleanup. The induction adds a client event only for a
successful get and threads the catalog through each result. Cleanup
preserves the resulting trace even when the enclosing call reports an
error. The remaining bridge must relate the actual phase reference and
primitive calls to the reached carrier for this dispatch. The theorem
currently consumes the interpreted lookup effects and cleanup frames.
The online read theorems take only the table-read interpretation.
They need no append, creation, manifest or WAL law.

The remaining native correspondence has two distinct boundaries.

- The phase reference and file handles are opaque runtime objects.
  A caller-side invariant must relate the owned reference to its online
  phase, and the acquired descriptor to the inode named in the durable
  catalog. The world token sequences operations and has no Lean projection
  for that ownership or for the live filesystem. The product read carrier
  preserves its mathematical projections by construction. Preservation of
  the corresponding physical state must follow from primitive effects.
- The current lookup proof uses `HealthySource` even for safety.
  `Image.open_represents` consumes `Source.Serves`, whose equalities
  require all bounded reads to succeed. A successful lookup only
  constrains the calls on its executed path. For example, it may read one
  leaf successfully while an unrelated leaf would report EIO.

The direct route is to compare the actual checked-open and lookup
schedule with the healthy image interpreter at each reached primitive.
A successful size or positional read must return the expected size or
slice for the acquired inode. An error keeps the reached state and
terminates that branch. Both outcomes must frame the phase reference,
namespace, WAL authority and manifest image. This would reuse the
existing healthy image theorem for the computed value and the existing
error propagation for failure. If the generic reader proofs cannot
express that comparison compactly, the smaller structural alternative
is to expose the existing reader's size and positional-read calls
directly to the caller's interpreter. The executable schedule should
remain shared. Instrumenting a second lookup or assuming a whole-callback
result equality would leave the same correspondence gap.

## Remaining premises

| Premise | Owner and producer | Consumer |
| --- | --- | --- |
| Stat, acquisition of the inode selected by the protected name, and bounded reads during its immutable lifetime | The primitive boundary must justify reads actually executed and propagate their failures. The current lookup proof still requests a healthy source after success. Deriving safety from the executed reads remains open. Healthy progress can require all bounded reads to succeed | `TableNamespace.scopedLookup` and `scopedCheck` |
| Descriptor drop and outer lock release | Runtime last-reference behavior and unlock effects. L0 must prove release on the reached ownership state. The shared schedule preserves an already-observed client trace through cleanup, assuming the close and unlock storage frames | `Lifecycle.recovery_offline` and `Lifecycle.scope_refines` |
| Concrete dispatch uses the native read interpreter on its reached carrier | L0 native callback setup. The interpreter itself computes the lookup result and keeps the reported world, so an independent result equality is gone | `NativeTableReads.Interpretation.get` |
| Durable catalog insertion and preservation of unrelated physical bindings | Filesystem create, file sync and directory sync effects. L0 must represent the reached writer and prove local table, manifest and WAL namespace frames | `TableCreationEvidence.catalogInserted`, `catalogAfter` and the lifecycle postconditions |
| Healthy recovery state and primitive reports | The filesystem supplies healthy manifest and table primitives. The manifest interpreter derives the typed open, and `scopedCheck` yields the table callback result. The returned state carries the installed L0 session, physical catalog, stable manifest image and exact ready WAL child, including the original successful WAL open result on the reached disk. L0 still supplies the catalog and manifest frames across WAL open and the manifest/WAL frames across table checks. The product read interpreter supplies mathematical projection frames; instantiating it in the callbacks also requires connecting actual Linux primitive effects and namespace ownership to those projections | `Lifecycle.recovery_progress` |
| Restart selection, reply delivery and loss | Filesystem survivor choice and runtime/client observations. L0 must connect the resulting image and observations to the interpreter for arbitrary permitted prefixes, including allocation, table creation and the interval before manifest publication. Before a table enters the selected catalog, `retainRecoverySelection` derives the recovery precondition from the unchanged selection and the old inode bindings. After durable creation, `flushPublicationChoices` supplies both selections. Concrete cut coverage remains open | `recoverReachedFlush` and `Execution.Run.flushObserved` |
| Repeated public operation steps on actual native states | A durably initialized empty root may be a caller premise. L0 still must derive the callback trace from one integrated reached-state interpretation and compose it with the outer scope | `Execution.Run.refines` |
| Ready view, recoverability after restart and segmented append | WAL producers for append, rotation, CONTROL and uncertainty selection | `WalRecovery.Interpretation` and the append law |

## Process interruption checks

The Linux native fixture cuts the child process after the table directory
sync and before manifest publication, or immediately after manifest rename
and before its directory sync. In each case two successful reopens check
the watermark, acknowledged values and tombstones. After the table cut,
a retry also checks that allocation skips and preserves the orphan. The
fixture exercises process exit and release of the root lock. The kernel
retains its filesystem cache, so the rename case expects the new manifest.
