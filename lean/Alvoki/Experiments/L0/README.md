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
component observations. WAL receipts identify the modeled sessions.
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

The native boundary still supplies correspondence from IO to the shared
writer and reader schedules, including allocation, cursor effects, the
reached file and directory barriers, path-to-inode selection and immutability
during the read scope. `fstat` and `pread` report effects on that description.
The scope holds the descriptor until the reader returns, and closes it on
success or error. WAL and manifest namespace frames stay separate from
the table directory.

Bootstrap, WAL release, orphan collection, snapshots, concurrency,
compaction and automatic flush are separate work.

Run `bash scripts/check-experimental-l0.sh` for the interpreter proofs
and regressions. Run `bash scripts/check-native-l0.sh` for the native
fixture, kernel checks and axiom audit. The native fixture rotates the
WAL, flushes multiple tables, checks persistent tombstones and WAL-suffix
replay, retries a failed table open, and checks that a required read
error never returns an older value.

## Producer boundary for native components

These are proposed producer signatures in terms of the existing public
states and events. Each premise about a call means a report of the actual
native call, at its reached handle or binding, under that component's
primitive filesystem assumptions. The component owns that interpretation.

| Component operation | Minimal result used by L0 |
| --- | --- |
| WAL `openExisting` and `scan` | `Step offline (.opened view) (.online view)` for the acquired handle and its scanned view. A scan of a ready handle observes that same view. A failed reopen exposes no ready handle and preserves the admissible choices. |
| WAL `append batch` | `Step (.online prior) (.ack (.append batch)) (.online next)` on success. An uncertain append yields the existing offline step with that one pending request. Later reopen supplies its selected view. L0 discards the position in the append reply. |
| DurableBlob `reopen` | `Step offline (.opened bytes) (.ready bytes)` for the exact returned and durably settled bytes. A failed reopen exposes no value and preserves the admissible choices. |
| DurableBlob `publish bytes` | `Step (.ready old) (.published bytes) (.ready bytes)` on success, or the existing uncertain step for those same proposed bytes. Later reopen supplies the selected bytes. |

The producer starts from the initialized component trace and identifies the
same returned WAL handle on scan and append. Close after an uncertain
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

The interpretation needs the active image projection, installation of the
reached image and frames for the WAL and table namespaces. The reports
describe reached primitive outcomes, including whether a failed sync took
effect. Relating the actual Linux IO and filesystem state to those reports
and namespace frames remains the runtime boundary. The native segmented
WAL and SSTable producer handoffs are separate obligations.

## Process interruption checks

The Linux native fixture cuts the child process after the table directory
sync and before manifest publication, or immediately after manifest rename
and before its directory sync. In each case two successful reopens check
the watermark, acknowledged values and tombstones. After the table cut,
a retry also checks that allocation skips and preserves the orphan. The
fixture exercises process exit and release of the root lock. The kernel
retains its filesystem cache, so the rename case expects the new manifest.
