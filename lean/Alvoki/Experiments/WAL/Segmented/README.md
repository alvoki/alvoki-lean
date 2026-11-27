# Experimental segmented WAL

This component adds fixed-capacity segment rotation and prefix release to the
[single-file WAL](../README.md). The caller supplies an empty, durably named root directory on one
filesystem and owns it exclusively for the lifetime of the handle.

`Native.create dir policy capacity` creates a WAL with 1–255 batches per segment.
`Native.openExisting dir` opens one. `append`, `discardThrough`, `scan`, and `close`
operate on the returned handle. A successful append returns its one-based absolute position,
which can be passed to `discardThrough` after rotation or earlier release. The public
contract caps absolute positions at UInt64.max. At that tail, append rejects before
rotation or child writes, so recovery cannot select the rejected batch. Recovery
materializes the retained history in memory, and each
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

## Verification

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

## Proof boundary

[Execution proofs](Proofs/Execution.lean) show that every modeled finite trace
starting with a successfully returned create satisfies the client contract
(`Run.refines`), and that a healthy open can complete from every reachable offline
state (`Run.healthy_open`). They also establish retention of acknowledged batches
until release, and persistence of an acknowledged release. The proof composes the
actual segmented schedules with modeled namespace and child operations; the
[layout](Proofs/Layout.lean), [child](Proofs/Child.lean),
[publication](Proofs/Publication.lean), and [reopen](Proofs/Reopen.lean) modules
own its intermediate obligations. The [child contracts](Proofs/SegmentRecovery.lean) express what the next operation needs:

| Contract | Established by | Consumed by |
| --- | --- | --- |
| `Child.Installed` | Fresh preparation, successful append or successful reopen places the cursor after the settled batches. | Append extends that history. Rotation installs an empty successor. |
| `Child.Settled` | An installed child already has this property when rotation seals it. | Reopen reads the full sealed history after a restart. |
| `Child.Recoverable` | An uncertain append leaves at most its issued batch pending. An interrupted reopen preserves the retry guarantee. | Successful reopen installs one permitted history for subsequent calls. |

The [layout and frame proofs](Proofs/Invariant.lean) still refer to concrete child
images, equality of untouched selected files and the active cursor. They also use the
32-byte payload and 255-batch limits. The [effects model](Proofs/Model.lean) still
names individual files for writeback and constrains admissible tears. Replacing the
single-file format may require revisiting these internal obligations. The LSM can
reason about absolute positions and the retained suffix using the [client contract](Contract.lean).

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

## Native refinement follow-up

The public single-file recovery schedule supplies the child
`Recoverable` and `Installed` facts and the cached scan result from local
primitive effects. Native segmented recovery still needs to bind that
child to the root session that `openExisting` and `scan` expose to L0.
The single-file append producer composes with that child recovery result
on its stored writer and marker descriptions. Native rotation and CONTROL
publication remain segmented responsibilities.
[Single-file premise audit](../Proofs/README.md#public-native-recovery)

For CONTROL, consider reusing DurableBlob's write, sync, rename and
directory-barrier semantics with the existing control codec and the
original writer used by PR #5. Check that the CONTROL projection of
the WAL disk model admits DurableBlob's publication outcomes and that
the root barrier also settles the successor's directory entry.
Keep segment creation, prefix release and collection under the
existing WAL invariants. Coordinate the adapter change with the L0
branch when taking up that work.

[Native reopen proofs](Proofs/NativeReopen.lean) compose the single-file
producer with the shared root operations. The root directory descriptor
selects both directory barriers. A barrier that takes effect settles the
CONTROL binding and child directory names together, including on a reported
failure. Root enumeration decodes only canonical segment IDs. Reclamation
addresses entries beneath the selected directory and changes its projected
root binding only at rmdir. Prefix unlinks affect private artifacts of a
retired segment. The existing collection proof keeps every selected name.

The root interpreter takes local effects for CONTROL reads, enumeration,
directory sync, inspection, unlink and rmdir. It assumes stable bindings
under the cooperating root lock. Successful enumeration covers the visible
canonical bindings, and an absent metadata result means the canonical name
is absent. Child inspection uses complete relative basenames and singly
linked regular files. Unlink on a retired child can affect those inodes
and its directory; rmdir controls the root binding independently.
The public install schedule acquires one store and passes it to both
phase installation and failure cleanup. The acquisition proof follows the
same resolved root through directory open, lock lookup and store allocation.
Its primitive premises are canonical path resolution, descriptor-to-inode
binding and lock acquisition on that description. The binding interpreter
retains the acquired descriptor identities in the ready phase. A reported
acquisition error leaves the disk recoverable.

The native sealed reader releases each child after scanning it. The active
child is carried through scan, validation and collection by the shared
`reopenWith` schedule. A reported error in that scope closes the acquired
child before the outer store cleanup unlocks the root. On success, the
schedule returns the session and that same child. The native installer
writes the child into the ready store, where append takes its writer
authority. Root unlock follows child close even when close reports an error.

### Public open contract for the append consumer

For a recoverable disk and a root acquired under the primitive assumptions
above, the interpreted public open must establish one postcondition on the
same reached disk and resources:

- On return, the public phase contains the acquired store and the installed
  `Session`. Both CONTROL and the held directory descriptor bind to the
  same root as the lock. The store owns the child returned at
  `segmentPath root session.control.active`. That exact child's phase and
  the reached segment image provide the writer and marker authority used
  by the next append. The installed history and cursor agree with the
  session, and public scan returns its view.
- On a reported error, the exact reached disk remains recoverable for
  the same request. The attempt retains no published phase or owned child
  or root lock. Cleanup consumes the child actually reached, including
  one opened before a scan or collection error. Release still attempts
  root unlock after a child close error. A process interruption uses the
  process-stop premises for acquired resources.
- Healthy primitive and runtime effects, with a representable CONTROL
  binding, reach the successful case. Bootstrap and publication must
  eventually supply representability.

The value-only model uses the same `reopenWith` executable schedule and
erases the active payload. Its existing layout proof still supplies disk
safety and healthy progress. The obsolete reopen dispatcher, active-cell
simulation and value-only public install interpretation have been removed.
`withActiveChild_reached` verifies that reported errors close the exact
acquired child at the reached state. `nativeAppendAfterTransfer` consumes
the returned child phase and its reached image using the existing
single-file append proof. The native fixtures cover successful reopen
and append, failure after active open, and root unlock after a reported
child close error.

The remaining proof must carry the scoped child value through the disk
layout proof and bind its returned identity to the ready store under the
runtime reference and unlock assumptions. Rotation still prepares a
successor in the store; when refining it, transfer the new child as an
explicit value through publication and installation.

The DurableBlob publication schedule can carry the staged CONTROL writer
through its fsync, rename, and root barrier. Its directory effect must be
framed with the WAL root's child bindings. Before CONTROL can select a new
segment, that segment and its name need their own durability argument.
Reclamation must respect both admissible CONTROL choices until the barrier.
The native CONTROL adapter uses the writer custody from PR #5: the stage
writer is consumed by its own fsync and cleared on cleanup. The recovery
composition theorem covers a reported discard error, another reported open
error, and two successful opens with the same view. It uses the shared
root publication model and interpreted native reopen effects. Linking the
actual CONTROL publication to that model remains open.

## Roadmap

**Minimal LSM integration.** Record the absolute WAL position covered by a durable
LSM checkpoint. Replay the retained batches after that position. Before releasing
through position `k`, make checkpoint publication durable so every checkpoint
recovery could still select covers at least `k`. Otherwise a crash could pair an
older checkpoint with a WAL whose required prefix has already been released. After an uncertain append or release,
reopen and use the recovered view. A bounded prototype can use today's scan and
payload limits. For larger inputs, provide streaming recovery and ordered iteration
with bounded memory, preserving the same suffix and positions. Align the limits of
append replies, checkpoints and persistent release metadata so every acknowledged
position can be represented throughout its lifetime. Define exhaustion before accepting
a batch, or widen the format.

**Independent WAL improvements.**

- Rotate by bytes and widen the batch and sequence fields. Byte-based rotation
  needs a durable way to derive each segment's first absolute position; the current
  calculation assumes every sealed segment has the same number of batches.
- For recycling, bind frames and recovery metadata to the intended segment generation
  and reject stale generations, including old frames with valid checksums. Revisit a
  [WAL-wide commit boundary](#who-owns-the-commit-boundary) independently of recycling.
- Extend the [physical model and native adapter guarantees](#namespace-assumptions)
  when a concrete target filesystem or failure trace needs a stronger claim, for
  example independent directory writeback. Check that the trace is admitted and
  that the same client guarantee follows under the stated assumptions.
- Compare group commit and buffering against the existing path with reproducible
  throughput and acknowledgement-latency measurements. Record batch sizes,
  concurrency, sync policy and storage setup. Every acknowledged batch must still
  survive recovery until released.
