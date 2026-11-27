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
component observations. WAL and manifest receipts identify the actual
modeled sessions or byte traces and use their public refinement theorems
for the returned values. `RecoveryChoices` discharges uncertain effects
from the public steps.

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
and lookup use the same stat and scoped opening schedule. For the
descriptor acquired by that schedule and serving
the exact built bytes, [TableProofs](TableProofs.lean) derives both successful
open and typed lookup from `open_built_table`. The check validates the footer
and index extent. Row validation occurs on demand.

[TableAllocation](TableAllocation.lean) is the native create schedule. Its
proofs show that probing picks a free ID and that a returned ID implies that
the builder received the original rows and that the directory barrier
succeeded after the synced build. The native row supplier shares
`nextTableRow` with the supplier proof, which proves the exact encoded stream
and EOF. The path-indexed creation proof uses that stream and the reached
build and directory effects to name the durable builder image.
`tableOpenAt` constructs the check witness at that same ID-derived path
and uses the descriptor acquired by the scoped read.

The remaining IO premises are local: stat reports the occupied name,
exclusive creation preserves unrelated names, the file and directory
barriers establish the bindings, and the acquired descriptor serves the
bound bytes. Native WAL and blob syscall observations must match their
existing component models. Turning all of those Linux primitive
observations into component receipts is still a refinement obligation. The runtime supplies reference-cell, error,
lock and descriptor effects under stable, exclusive ownership. The Lean
proofs do not interpret Linux syscalls.

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
successful WAL open follows this rule too. L0 supplies isolation frames
between component namespaces, including on cleanup. Manifest decoding,
L0 phase custody, and table directory isolation stay in L0. Native-to-model correspondence for WAL and DurableBlob is separate
component work. The interim receipt adapters can be replaced by these
producer results when available.

## Process interruption follow-up

Add a subprocess cut after durable table creation and before manifest
publication. Reopen twice and check that the old watermark remains usable,
the orphan is skipped by allocation, and committed writes and tombstones
are recovered from the retained WAL. Add a second cut after manifest rename
and before directory sync. Reopen twice and check the watermark chosen by
the first successful reopen and the logical database. These cases exercise
process death and lock and descriptor release. They do not simulate power
loss or discard filesystem cache.
