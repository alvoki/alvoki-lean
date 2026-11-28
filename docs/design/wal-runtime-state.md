# WAL runtime state and streaming recovery

Design for review. The WAL implementation inspected here is
[`a375c871`](https://github.com/alvoki/alvoki-lean/commit/a375c871879e51558be60661d86f73b9cbaa904c).
The L0 model on that revision has the same consumer shape as the native
candidate inspected at
[`79194035`](https://github.com/alvoki/alvoki-lean/tree/791940352e0068a9e303236c8b50b22d638fa139/lean/Alvoki/Experiments/L0).
The present proposal is to remove the retained history from both native
WAL handles and keep the existing history contracts as specification.
Expose a metadata observation for positions and a checked recovery fold
for replay. The storage format, barrier schedules and active L0 work are
outside this proposal's implementation scope.

## Where the history comes from

Single-file recovery reads the file to a byte list, produces
`Decoded {batches, cursor}` and installs `batches` as `Phase.active.entries`.
Append runs using the cursor and descriptors, then extends `entries` to
make the next cached `scan` return the right sequence. `Opened.recovered`
also carries that decoded value across the open schedule for producers and
fixtures. These are two carriers of the same result. [Single-file
schedule](../../lean/Alvoki/Experiments/WAL/SingleFile.lean)

Segmented reopen opens and scans each selected child, concatenates sealed
batches into an array, adds the active child's list, and drops the released
prefix. The result becomes `Session.view`. The active single-file child has
its own entries in addition to the segmented view. Segment-wide history
feeds the cached scan and currently serves as the source for append and
discard bounds. Shared model/native schedules use these executable values
directly in refinement statements, so removing the carriers requires
changing the producer interface. [Segmented protocol](../../lean/Alvoki/Experiments/WAL/Segmented/Protocol.lean)
· [Native store](../../lean/Alvoki/Experiments/WAL/Segmented/Native.lean)

## Runtime field inventory

### Single-file WAL

| Runtime field or temporary | Operations that consume it | Proposed lifetime |
| --- | --- | --- |
| `Handle.policy` | Selects validation, repair and marker protocol in recovery; append decides whether to publish a marker. | Keep the policy for the installed handle. Read and check the stamp at open. |
| `Handle.state` and shared mutex | Serialize append, scan and close for aliases; govern active, poisoned and closed behavior. | Keep phase and serialization. Keep the current poison-before-attempt and close behavior. Single-file close on an already closed alias reports an error. |
| `Phase.active.lock`, `Phase.poisoned.lock` | Establish exclusive ownership through open and mutations; unlock on close or owning-scope error. | Keep the same acquired lock in the corresponding owning phase. |
| `AppendFiles.writer` | Append, flush and sync through the same file description; released on loss of active custody. | Keep the installed append writer. |
| `AppendFiles.markers` | In `boundary`, read/select and settle markers in recovery; append rewinds, overwrites and syncs one slot; resources follow active phase custody. | Keep two slots for `boundary` and none for `logOnly`. Marker contents can be discarded after selecting/validating the recovery cursor. |
| `Cursor.endPos`, `Cursor.nextSeq` | Byte extent for frame/marker updates and repair; local sequence bound, sequence encoding and marker parity. The acknowledged extent also bounds future read-only scans. | Keep both. Variable-length frames make byte extent independent of the sequence count. Local committed count is `nextSeq - 1` in an installed state. |
| `Phase.active.entries` and `Opened.recovered.batches` | Cached scan, child recovery handoff, exact-value tests and producer statements. | Use an ordered recovery fold plus proof witnesses. No batch list in the installed native handle. |
| `OpenFiles.stamp`, `reader`, recovery directory descriptor and `Opened` descriptor copies | Read/check stamp and data; repair on the reached reader; sync stamp and directory before installation; describe acquired descriptors in proofs. | Recovery resources stay scoped. Return only the roles needed online. A read path needs an inode-bound readable source, either a retained read descriptor or a scoped reacquisition under the same root/lock premises. The append writer remains a write/barrier resource. |

Single-file has no rotation or discard operation. Its full native history
is already bounded by the local sequence limit of 255 frames, at up to
52 encoded bytes per frame. Removing it primarily changes the producer
boundary and avoids per-child lists during segmented recovery. A bounded
per-child buffer can be an intermediate implementation while validating
the parser correspondence on byte reads. The final recovery interface
still returns metadata and the consumer result.

### Segmented WAL

| Runtime field or temporary | Operations that consume it | Proposed lifetime |
| --- | --- | --- |
| `Handle.state`, mutex; `Phase.ready`, `poisoned`, `closed` | Serialize operations, authorize access, retain custody on errors, reject use after close. | Keep. Segmented close swaps to closed and is repeatable. Attempt root unlock even after child-close error and preserve the first error. |
| `Store.root`, `Store.lock`, `Store.directory` | Resolve child and CONTROL names; exclusive root ownership; barriers on the held directory description; release on close/error. | Keep canonical root and original resources. Path or descriptor substitution needs its own proof. |
| `Store.active : Option (Nat × child)` | Dispatch append to the registered child for the exact ID; remove-before-close, transfer on create/reopen/rotation, and clean up after failure. | Keep presence, ID and exact child custody, including during poisoned transitions. Ready registration equals `Control.active`. The registration ID also guards the handoff and should not be removed simply because ready state agrees. |
| `Control.policy`, `capacity`, `active` | Choose the child protocol, check sealed and active counts, choose successor and map segment/local count to absolute position; persist via CONTROL. | Keep the selected CONTROL metadata. Capacity is fixed and positive within the existing bounds. |
| `Control.discarded` | Durable logical base, monotone discard guard, retention/collection limit and replay filter. | Keep. The first selected child may contain a released prefix. `firstNeeded = min active (discarded / capacity)`; retain the active child even when its whole history was released. |
| `Session.activeCount` | Rotation threshold, position and exhaustion guard; recovered from validated child count. | Keep the cheap count at the segmented boundary with an agreement proof to the active child's cursor. Reading the child cursor under its lock instead would be a separate trade-off. |
| `Session.view.base`, `view.batches` | Duplicate durable base, history-backed tail/guards, observes ordered retained batches. | Use `Control.discarded` for base and `Session.tailPosition` for tail. Keep ordered batches in the abstract view and offer on-demand observation. |
| `readSealed` array, active scan result, root listing, scoped CONTROL/child descriptors | Accumulation/validation, cleanup and transfer during reopen; directory enumeration for collection. | Eliminate global payload accumulation. Keep validation/counting and scoped resources. The current root listing still uses transient memory proportional to directory entries. Replacing it requires separate enumeration and removal/error semantics. |

### Absolute tail

`Session.tailPosition = active * capacity + activeCount` is already the
public append reply. The append guard and discard checks still use
`view.tail` or `view.base`. Under `Installed`, the derived tail equals
`view.base + view.batches.length` and `discarded = view.base`. All sealed
intervals are full. Earlier IDs still count toward the absolute
coordinate after collection. Discard never renumbers. An empty
successor immediately after rotation publication has the old full
segment's tail. Its first ACK advances exactly once. Keep `Nat`
arithmetic in the first candidate. Apply the current exhaustion bound
before namespace or child effects, with the existing payload-size check
first and the native poison transition in its current place. A future
machine-word implementation must prove pre-conversion bounds for the
product and sum. CONTROL decoding bounds `active` and `discarded`
individually, so decoding arbitrary input alone gives no such product
bound. Preserve the existing distinction between installed/reachable
histories and validation of malformed files. [Position
proofs](../../lean/Alvoki/Experiments/WAL/Segmented/Proofs/Append.lean)
· [CONTROL codec](../../lean/Alvoki/Experiments/WAL/Segmented/ControlCodec.lean)

## Proposed schedules

Append uses only the submitted payload, the active cursor and resources.
For the segmented case, check payload size and the derived tail, then
roll over only when the current child is full. Keep the close,
successor preparation, root barrier, CONTROL publication, write and
registration order. Derive the reply from the successful compact
session. Discard compares its request with the derived tail and durable
base. A forward discard publishes CONTROL before it removes retired
children and syncs the directory. A request at or below base is a
no-op. An out-of-range request still fails. An error in a mutation
preserves the existing poison and custody rules. Close needs the phase,
registered child (if any) and root lock. Neither operation needs to
visit historical payloads.

### Recovery and streaming replay

1. Add a single-file checked fold that takes a private accumulator and a
   pure step over a verified batch. The scanner obtains the selected
   extent, parses in order with a byte offset and next sequence, and
   returns the verified count/cursor and accumulator only on success.
   Use exact reads or explicit short/error outcomes. Keep header/trailer
   checksums, generation, sequence and length checks, and the existing
   `logOnly` final-torn-frame rule with its remaining-length condition.
   In `boundary`, read and compare both marker slots with full size
   checks, including oversized slots. Validate the marker-selected
   prefix and exact sequence; preserve suffix truncation when required.
   Keep both marker-settling barriers before truncation, the data sync
   and subsequent stamp/directory sync. Define the accumulator as
   provisional until the whole enclosing recovery succeeds. A general
   side-effecting user callback would need a weaker delivery contract
   and is not needed here.
2. Segmented recovery preserves CONTROL selection and the first root
   barrier. Visit selected sealed IDs in order with one scoped child at
   a time, retaining the existing child validation and opening/settling
   schedule. Require exactly `capacity` batches per sealed child.
   Validate `activeCount ≤ capacity` and `discarded ≤ tail` on the
   reached active child. Compute each absolute position from segment ID
   and local sequence. Suppress delivery at or below `discarded` while
   still validating the selected child. Carry only the consumer state,
   counters and scoped resources across children. Run collection and
   its barrier. Transfer the exact active child and publish the ready
   phase and accumulator only on overall success. The success relation
   should recover a permitted specification view from the reached disk.
   The returned bounds equal that view's base and tail. The returned
   accumulator equals the ordered fold of that view from the supplied
   seed. Each online compact phase then frames that same view until the
   next acknowledged change or explicit restart.
3. Keep failure continuations on the reached disk and resources.
   A late checksum/read, marker, child-close, collection, sync or
   installation failure may follow a partially evaluated fold. Discard
   that private result and preserve the operation's primary error.
   Reuse the existing scope rules for sealed child release, active
   child transfer/release and root unlock. Test compound errors where
   incremental reads can expose a different first failure than the old
   whole-file read. Specify the required precedence before changing
   it. An optimization which skips a recovery barrier or avoids
   validating a selected but flushed frame needs a separate review.

### L0 boundary

Replace the online `scan` uses in `write` and `flush` with a metadata
observation `{base, tail}` on the same ready phase, or just the typed tail
projection at their call sites. Keep the L0 exhaustion check before
submitting a mutation and deriving the manifest watermark from that
same ready WAL. The acknowledged tail can be threaded from append if
the same proof of agreement is supplied, without caching it in two
places by default.

L0 currently reopens the manifest, reopens and scans the WAL, validates
the watermark range, decodes the suffix into a second list, checks the
tables and installs `replay changes`. The proposed recovery reads the
manifest first and gives its watermark to the WAL fold. It builds a
private memtable by decoding and inserting batches strictly above that
watermark, preserving order, overwrites and tombstones. Keep the first
L0 decode failure in the private accumulator and continue WAL validation.
After WAL success, attach the reached handle for cleanup, check
`base ≤ watermark ≤ tail`, then report a deferred decode error if any.
Check the required tables before publishing the online session. This
keeps WAL errors ahead of L0 decode errors and preserves the present
watermark/decode/table ordering and custody. Validate WAL frames even
when L0 suppresses their replay. The memtable still depends on distinct
unflushed keys; the WAL supplies no additional complete payload
sequence. The current L0 flush publishes a watermark but does not call
WAL discard. Changing retention policy is a separate decision.
[Model consumers](../../lean/Alvoki/Experiments/L0/Basic.lean)
· [Native lifecycle at the reviewed pin](https://github.com/alvoki/alvoki-lean/blob/791940352e0068a9e303236c8b50b22d638fa139/lean/Alvoki/Experiments/L0/Lifecycle.lean)

### Scan and the public contract

Preserve ordered, exact retained-batch observations, stable absolute
positions, ACK durability, prefix release, the single uncertain
submission, and retry selection across failed and repeated opens. The
successful scan event must still equal the online abstract history.
A materializing `scan` wrapper can collect a read-only fold on demand for
tests, diagnostics and the existing benchmark oracle. The metadata API
should stay cheap and avoid file reads.

Read under the existing ownership/serialization assumptions. Walk
selected sealed children and read the active child only through its
installed extent; check identity, frame validity and the expected
counts and released prefix. For single-file use the cursor's end and
sequence. For segmented scan, retain the actual active child and
CONTROL selection. For sealed files use the observed policy-selected
extent and the full-segment count without entering the repair schedule.
Include descriptor binding and exact read results in the filesystem
relation. The history guarantee still relies on the filesystem model's
prefix preservation and stable ownership. Avoid calling mutating recovery as scan: scan must
neither choose another survivor nor repair, publish, collect or sync
the directory. A scoped read path must preserve the lock/phase, disk
and custody on both outcomes. A consumer must not reenter the handle
under the lock; use a private fold or a separately specified snapshot.

The old ready-phase scan is a cache projection and carries a stronger
read-free success property than an on-disk scan. The present abstract
trace has a successful scan event and no scan-I/O-error event. Keep
that correctness statement for successful observations. To adopt a
fallible on-demand scan, audit external callers and specify its
frame-preserving read error and healthy-progress premises explicitly.
If the old native API must still guarantee unconditional success for
a ready handle across reported read errors, a disk-only implementation
cannot supply that guarantee. This is a review decision, not an
implicit weakening. Operations that only need positions and L0's
recovery handoff can migrate without depending on that choice.
[Single-file contract](../../lean/Alvoki/Experiments/WAL/Contract.lean)
· [Segmented contract](../../lean/Alvoki/Experiments/WAL/Segmented/Contract.lean)

## Refinement and Astra handoff

| Existing reached producer or consumer | Proposed proof obligation |
| --- | --- |
| Single-file `recoverWith`, `installWith`, `scan_opened`, `append_refines`; segmented `Child.Settled` and `Child.Installed` | Relate the compact active phase, cursor and acquired descriptor roles to the selected ghost history in `Prop`. Prove incremental validation gives the same decoded cursor and fold as the old spec on each policy and yields the same permitted survivor and reached repair facts. Make append's success supply the extended ghost relation and its error supply the old/sole-pending choice and actual custody. |
| Segmented `Installed`, `AppendReady`, `publicNativeAppend_refines` and `publicNativeAppend_position` | Keep the CONTROL/disk and exact registered-child premises. Relate the compact state to `historyView`, prove the base and tail equalities, and derive guard/ACK/discard equivalence. Frame the lifecycle and both in-place and rotation paths. The proof relation carries history without serializing it or computing it on append. |
| `publicOpenModel_refines`, `reopensWithAppendAuthority`, `publicAppendRecovery` and `publicNativeAppend_reportedClose` | Return the exact phase/child, reached disk and cleanup outcomes. Replace equality to a stored view with an existential selected ghost view and a fold-result equation over it. Prove failure, lost ACK and failed-open-then-two-good-opens over the same actual survivor. Keep reported-effect versus no-effect branches and power-loss/writeback premises. |
| Candidate `L0.WalProducerHandoff.{reopenAuthority,retry,reportedWrite}`, `L0.WalRecovery`, `L0.NativeBridge` and component refinement | Feed the new reached WAL producer to the lifecycle. Replace `scanAfterReopen` and ready scan equalities in write/flush with fold correspondence and a position-frame theorem as appropriate. Derive memtable agreement with the same abstract suffix and keep ready-child authority and namespace frames for subsequent write, flush and get. Consume actual reports rather than adding a caller-supplied history, ready view or cleanup frame. |

Use a projection/forward simulation between the existing schedules and a
compact executable schedule. Keep the abstract contracts and existing
model proofs as an oracle during migration. Prove the frame and accumulator
relation at the exact reached cursor/disk after each primitive, including
partial recovery and errored publication. Use `Prop`-valued relations
and erased proof fields for history facts. A `List` stored as a field in
a runtime `Type` is executable even when introduced for a proof.

Review independently of Astra's active L0 integration. Suggested order
is compact metadata equivalence, single-file fold correspondence and
custody, segmented composition and restart, then a joint L0 candidate
from the accepted producer pin. Keep the existing benchmark branch and
raw cohorts intact. On a later candidate compare the same append,
rotation and recovery workloads under both policies. State which
recovery path uses a no-op/counting, materializing or L0 consumer and
check that any list oracle stays outside the throughput timing. Measure
absolute position scaling, peak RSS and allocations; also measure the
new explicit scan workload and L0 watermark/replay separately. A warm
on-disk scan has different cache effects from the old projection.

## Validation for review

The small Lean design check proves installed metadata equals the abstract
base/tail, an empty successor preserves tail, and a position-filtered
left fold agrees with the existing drop-and-fold operation. The last
lemma works for any pure step, including an `Except` accumulator for L0
decode. Parser correspondence and native filesystem refinement remain
separate proof obligations. The check uses the repository axiom policy.
[Lean design check](../../lean/Alvoki/Checks/Tests/WalRuntimeState.lean)

```sh
cd lean
lake build Alvoki.Checks.Audit.AxiomPolicy Alvoki.Experiments.WAL.Segmented.Proofs.Invariant
mkdir -p .lake/build/lib/lean/Alvoki/Checks/Tests
lake env lean -o .lake/build/lib/lean/Alvoki/Checks/Tests/WalRuntimeState.olean \
  Alvoki/Checks/Tests/WalRuntimeState.lean
lake env leanchecker Alvoki.Checks.Tests.WalRuntimeState
```

Before adopting a runtime implementation, exercise both policies under
reported read/sync/close errors and successful effects with lost replies.
Include an empty successor, segment boundary, discard inside a child
and through the tail, late bad frame or collection failure, and two
successful reopens after a failed one. For L0 include watermark at
both bounds and outside the range, an invalid unflushed mutation
followed by WAL failure, and a tombstone followed by a put after
restart. Check the reached handle and resources as well as contents.
[Existing fault contract and fixtures](wal-recovery.md)
