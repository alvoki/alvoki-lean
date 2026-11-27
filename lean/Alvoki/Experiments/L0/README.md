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

[NativeBridge](NativeBridge.lean) derives the operation laws for a reported
execution of the same schedule. Its append receipt names the existing
segmented WAL execution and its exact reached sessions. The publication
receipt uses the DurableBlob trace and its typed manifest refinement.
`RecoveryChoices` discharges uncertain effects from the public steps.
Successful table creation records the exact builder image under the
new durable name and frames all other names. The read receipt serves
that image through the opened descriptor. `open_built_table` and
`TypedTable.represents_of_bytes` yield the lookup using the proved
big-endian key and tagged mutation codecs. The bridge derives
`ComponentLaws` and feeds `Execution.Run.refines` through
`ObservedRun.refines`.

[NativeSchedule](NativeSchedule.lean) proves that correspondence for each
complete L0 schedule follows from correspondence for the individual
callbacks in the record constructed by `Native.withOpen` and the runtime
rules for bind, success and error. Given a runtime observation relation
that reports the reached results faithfully, `NativeRun.refines` takes
observations of those concrete callback records to the generic client
trace. It uses the wrapper's serialized phase discipline and frame on
cleanup. The remaining premises are at the IO boundary:

- The WAL and blob primitives realize their modeled file effects, including
  the effects that may precede an error. Successful reads/reopens report
  the corresponding reached WAL view or decoded manifest. An open failure
  frames the selection, even if private recovery progress changed.
- Under stable, exclusive ownership, the WAL, manifest and table names
  occupy disjoint namespaces. Creating a table uses an unused name,
  `buildFileSynced` makes its complete builder output durable, and a
  successful directory sync preserves the new name and the existing
  bindings. A failed attempt may leave an orphan, which allocation skips.
- The opened table descriptor serves the bytes bound to that name until the
  operation returns. Linux lock and handle primitives and the runtime
  implement the stated custody and cleanup behavior. The tests exercise
  the IO adapter. The Lean proof does not interpret Linux syscalls.

Bootstrap, WAL release, orphan collection, snapshots, concurrency,
compaction and automatic flush are separate work.

Run `bash scripts/check-experimental-l0.sh` for the interpreter proofs
and regressions. Run `bash scripts/check-native-l0.sh` for the native
fixture, kernel checks and axiom audit. The native fixture rotates the
WAL, flushes multiple tables, checks persistent tombstones and WAL-suffix
replay, retries a failed table open, and checks that a required read
error never returns an older value.
