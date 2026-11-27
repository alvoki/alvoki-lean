# Experimental L0 composition

This slice runs serialized put, delete, get, explicit flush and recovery against
a deterministic component interpreter with fault choices. It starts with a
durably initialized empty WAL and manifest. The WAL prefix is retained.

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
represents such a pair by selecting it at the cut. The concrete adapter
must establish the phase discipline and the corresponding projection from
its component traces, including closing any handles after a failed attempt.
The argument uses the public steps and leaves physical crash modeling to
the components.

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

`Model.Run.refines` proves the public client contract for arbitrary finite
modeled traces of the shared schedule. These include interrupted writes,
flushes, recovery attempts and lost replies after a completed operation.
`Model.Run.healthy_open` shows that each reachable offline image can
reopen once both reopen callbacks succeed. [Execution proof](Execution.lean)

The proof applies to this interpreter. For the next slice, a native table
adapter must make the exact built bytes and fresh name durable before
returning an ID, preserve all existing bindings on error, and give the
point observations specified by the rows on healthy open/read. This
requires syncing through the descriptor that built the table, then syncing
its directory, under exclusive ownership and the filesystem durability
assumptions. File IDs must avoid retained orphans, and the adapter must
own its handles. An order-preserving key codec and tagged mutation bytes
can bridge to the opaque SSTable API. No SSTable offsets or file format
appear in the L0 schedule or proof. [SSTable contract](../SSTable/README.md)

A subsequent WAL-release step may discard through `F` only after the
manifest covering it is durable. Bootstrap, native wiring, orphan
collection, snapshots, concurrency, compaction and automatic flush are
separate work.

Run `bash scripts/check-experimental-l0.sh` for kernel checks, the axiom
audit and a regression that follows both manifest selections, checks
tombstone masking, and retries recovery.
