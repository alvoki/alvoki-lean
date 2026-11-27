# Experimental segmented WAL

This isolated experiment adds fixed-capacity segment rotation and prefix release to the
existing [single-file WAL](../README.md). It does not change the production DiskTable
format or API. The caller supplies an empty, durably named root directory on one
filesystem and owns it exclusively for the lifetime of the handle.

`Native.create dir policy capacity` creates a WAL with 1–255 batches per segment.
`Native.openExisting dir` opens one. `append`, `discardThrough`, `scan`, and `close`
operate on the returned handle. A successful append returns its one-based absolute position,
which can be passed directly to discardThrough even after rotation or earlier release. Recovery materializes the retained history in memory, and each
append updates the cached session view. This experimental API is not a bounded-memory
WAL reader. Positions are absolute: batches start at one and
`scan` returns the last discarded position `base` plus the retained batches. Release
through a position at or below the current base is a no-op; release past the tail
fails. The native control format limits the active segment ID and discarded position
to unsigned 64-bit values; attempts to publish larger values fail. Close and reopen after an operation error, because its effects may have
occurred before the error. The handle is poisoned until then.

The shared [protocol](Protocol.lean) prepares and durably names an empty successor
before publishing it as active. Control publication stages and syncs a new record,
renames it, then syncs the root. Release publishes the new base before removing
whole retired segments. The active segment is never removed, and a partially retained
segment stays. Recovery reads and stabilizes control, reopens the selected segment
range, skips released batches and retries collection. Each child uses the selected
single-file policy and its existing framing and recovery schedule. The native adapter
holds a root lock, validates control and child names, and refuses unexpected files
rather than deleting them. It assumes other processes respect that lock and the root
binding is not replaced while open.

### Who owns the commit boundary?

| Scope | Durable record | Recovery uses it to |
| --- | --- | --- |
| Whole WAL | `CONTROL` | Select the contiguous range of segment IDs and the first retained position. Rotation and release publish a new control record. |
| One segment, boundary policy | `segment-N/commit.0` and `commit.1` | Select the committed end offset and last sequence number in that file. Each acknowledged append syncs its data and then its marker. |
| One segment, log-only policy | Framed `segment` file | Recover the prefix admitted by the single-file scanner and its fault model. |

The marker format in the [single-file protocol](../Recovery.lean) uses local positions.
Both segment 0 and segment 1 can have a valid marker for local batch 1. Moving the two
files to the root would make those records ambiguous. A WAL-wide pair is a possible
different design: bind each generation to a segment ID and committed end, establish the
sealed prefix before publishing a successor, and specify which frontier recovery can
select after a crash during rotation or release. This saves two files per
additional segment. It still requires a marker barrier when acknowledging a marked append.

Run `bash scripts/check-segmented-wal.sh` from the repository root on Linux with the
pinned Lean toolchain and a C compiler. Set `TMPDIR=/dev/shm` when working space is
limited. The check builds the shared protocol and native adapter, runs the
[deterministic simulation](Tests.lean), [physical-model regressions](ModelTests.lean)
and [Linux fixtures](NativeTests.lean), and
kernel-checks and audits the listed proof modules. The simulation runs the real
segmented schedules against a model of live and durable names, control, and per-child
batch histories. Its independent client oracle tracks acknowledgments, uncertain
appends or releases, and pins the history and base after successful recovery. It cuts
rotation, publication, collection and retries before and after effects, including
process exit and power loss. Its child model abstracts batch-level outcomes; it is not
a second execution of the single-file byte scanner. The native fixtures exercise
actual files and locks; neither they nor the simulator demonstrate device power-loss
behavior.

[Execution proofs](Proofs/Execution.lean) show that every modeled finite trace
starting with a successfully returned create satisfies the client contract
(`Run.refines`), and that a healthy open can complete from every reachable offline
state (`Run.healthy_open`). They also establish retention of acknowledged batches
until release, and persistence of an acknowledged release. The proof composes the
actual segmented schedules with modeled namespace and child operations; the
[layout](Proofs/Layout.lean), [child](Proofs/Child.lean),
[publication](Proofs/Publication.lean), and [reopen](Proofs/Reopen.lean) modules
own its intermediate obligations. Rotation consumes a settled sealed history and an
installed empty successor. An uncertain append produces a recoverable child with one
pending batch; successful reopen selects a permitted history and installs the child
for the next append. The [child predicates](Proofs/SegmentRecovery.lean) and their
operation proofs own the local cursor, marker and durability details.

### Namespace assumptions

Only IDs from `firstNeeded` through `active` may supply history. An interrupted
prepare can leave an incomplete unpublished successor; the next prepare clears known
child files before reusing that ID. An interrupted collection can leave a partially
removed retired directory; reopen retries its removal. Unexpected names, links or
file types can make cleanup fail. A selected incomplete segment makes open fail.
The model treats successful prepare as a fully initialized child and successful
remove as an unlink. The native adapter must confine intermediate effects to the
unselected object. The [artifact frame rule](Proofs/Artifacts.lean) allows arbitrary
modeled child bytes and either name binding independently while offline, provided
neither visible nor durable control selects the ID. Likewise a partial `CONTROL.next` may survive a failed stage;
only a fully written and synced stage may be renamed over `CONTROL`. The
[codec proof](Proofs/ControlCodec.lean) establishes canonical decoding and roundtrip
within the native read bound. Mapping the stage, sync and rename syscalls to that
typed control publication remains an adapter assumption.

The trace models child calls using the single-file effects interpreter, including
source-level failures and prefix tears. It also admits full-length tears with an intact
header and same-length payload: log-only mode requires the damaged checksum to be
detectable, while boundary mode can discard an unpublished suffix. Scheduled child
callbacks admit independent whole-file writeback before each reached primitive; offline
traces can also write back one child file. Arbitrary sector-level persistence, a
checksum-valid substituted record in log-only mode, and independent root-directory
background writeback outside the modeled namespace outcomes remain outside this proof. The model starts at a successfully completed create: it does not
establish native creation or locking. Mapping native syscalls, descriptors and directory
syncs to the modeled effects, filesystem durability, exclusive ownership and the
compiler/runtime remain assumptions. Segment recycling and checkpoints of application
state are outside this experiment.
