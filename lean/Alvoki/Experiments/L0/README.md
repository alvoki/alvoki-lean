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

See the [native refinement review inventory](../../../../docs/design/l0-native-review.md) for the integrated producer graph, cut cases, and remaining primitive contracts.

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

The model uses the abstract operation laws to extend its client trace.
The native path reads the actual manifest bytes, opens the segmented WAL
and checks each table before it publishes the recovered session. The same
phase reference, WAL registration and physical catalog reach the public
operation. Both paths use `Execution.Run.refines` for client acceptance.
[Model schedule](ScheduleSteps.lean) · [Native recovery](NativeRecoverAt.lean) ·
[Public reads and cleanup](WithOpenReads.lean)

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
frames. The interpreter obtains its component laws from `RecoveryEffects`
and `FlushEffects`. Native table creation binds the builder's returned
file to its inode, bytes and directory entry. A subsequent checked open
consumes that durable binding. [Native creation](NativeTableCreate.lean) ·
[Producer-to-reader proof](TableProofs.lean)

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

The owned phase read and swap contracts preserve the represented manifest
and table bindings, and permit WAL writeback. On a WAL open error the
recovery proof retains the reachable recoverable disk and release facts.
Healthy recovery first reads and settles the manifest, then opens the WAL
and checks every table in the selected version. [Recovery](NativeRecoverAt.lean) ·
[Healthy acquisition](HealthyReads.lean)

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

The segmented WAL open produces the actual active child, session, cursor
and disk. A scan observes that session. A reported append error retains the
issued batch as the one uncertain request. A successful append followed
by a lost reply retains the extended history on both reopens.
[WAL recovery](NativeRecoverSelected.lean) · [Two reopens](NativeMutationReopens.lean)

Table creation produces both live and durable catalog bindings. Manifest
publication stages the encoded proposal, syncs it, renames it and syncs the
directory. The native restart proof consumes the surviving manifest, WAL
disk and table namespace at the reboot world. An old manifest replays the
retained WAL. A new manifest references the durably named table carrying
the same mutations. A failed reopen preserves the remaining choices.
[Publication](NativeManifestPublish.lean) · [Boot catalog](NativeFlushBoot.lean) ·
[Recovered lookup](NativeFlushRestart.lean)

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

## Reuse and external primitive contracts

At the initial read handoff, 26 of the 34 L0 Lean files at `5b2e9d30`
were byte-identical (2,678 lines). After integrating mutation and flush
and retiring the old bridge, 18 of those files remain byte-identical
(1,401 lines). Thirteen have edits and three were retired. These counts
include the executable and tests. The component model, codecs, client
contract and trace refinement remain independently checkable.

The removed native bridge required a selected WAL projection, a manifest
image installer, whole table creation and table check callbacks, and
unqualified frames across those callbacks. The model retains its general
component laws and state transitions. Native recovery now produces the
input to native operations at the world where each primitive returns.

| Local external contract | How the native proof consumes it |
| --- | --- |
| Root and phase reference ownership | The acquisition and publication rules read and swap the owned reference. The returned registration identifies the WAL used by the next operation. |
| Filesystem reads and handle disposal | The selected name and inode determine bytes at stat, open, size and bounded pread. Last-reference disposal occurs at the reached scope exit for a successfully constructed handle. Root unlock supplies its own observed result. |
| WAL file actions | Open, append, sync, rotation and CONTROL publication update the reached child and disk. On success the installed active authority is available for another operation on the same handle. On failure the error path closes whichever child remains in the slot. |
| Immutable table creation | Allocation, bounded writes, file sync and directory sync establish the live and durable bindings. Disjoint namespace entries and covered inode bytes are framed. |
| Publication and restart | File and directory effects determine the live binding and permitted durable survivors of the affected prefix. Reboot restores the selected WAL and durable table bindings. The client observes reply delivery or loss. |

The capacity-one example exercises two public mutations on one handle.
The put writes the existing child, the delete publishes a successor, and
the get observes its tombstone. Cleanup closes the successor registration.
[Sequence proof](MutationSequence.lean) · [Initialization and client trace](MutationSequenceRoot.lean)

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

## Mutation interruption boundary

The [public WAL cut](InterruptedWorker.lean) starts from the acquired
mutation callback. Phase and mutex observations before the first child
write preserve the known view. An interruption inside a child or CONTROL
operation admits the survivors of the exact batch. After successful
worker return, the extended view is settled even if installation of the
next phase or delivery of the reply gets interrupted. The [cleanup
cut](MutationExitCut.lean) follows the actual phase swaps, child close,
WAL close and root unlock. Each case supplies `Retry` and the existing
two public read scopes on the rebooted world.

The filesystem supplies the local byte, directory and survivor effects.
For the WAL worker, each completed primitive preserves the represented
table bindings and the stable manifest up to the last issued syscall.
The crash contract at that syscall supplies the surviving WAL disk and
the table and manifest projections at reboot. Volatile-operation frames
assume exclusive ownership of the root and isolation of its protected
files.

## Process interruption checks

For append, the fixture stops the process immediately after data fsync
and immediately after marker fsync on both the existing and rotating
segment. Under boundary policy the two reopens return the old value in
the first case and the mutation in the second. Additional cases stop at
CONTROL rename, lose the reply after scope exit, or inject a segment
fsync error before and after CONTROL publication. Each process test
retains the kernel cache. Power-loss outcomes are checked by the proof.

The Linux native fixture cuts the child process after the table directory
sync and before manifest publication, or immediately after manifest rename
and before its directory sync. In each case two successful reopens check
the watermark, acknowledged values and tombstones. After the table cut,
a retry also checks that allocation skips and preserves the orphan. The
fixture exercises process exit and release of the root lock. The kernel
retains its filesystem cache, so the rename case expects the new manifest.
