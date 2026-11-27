# Single-file WAL proofs

Start with the [batch-level client contract](../Contract.lean). It defines the
histories a writer may observe. [`Run.refines`](Execution.lean) checks that every
modeled trace of the [single-file WAL](../README.md) obeys it.
`Run.healthy_open` establishes that recovery can return once the faults stop.
The [policy comparison](Policy.lean) shows when equal-length substitution escapes both modes, which suffix each mode
adopts and how an intact marker detects a missing published suffix.

An open writer holds a settled history. An abandoned writer can leave two
possible histories, distinguished by the last outstanding batch.
[Append](DirtyAppend.lean) and the [torn-write proof](TornAppend.lean) establish this recovery invariant.
Independent writeback of a file preserves it, and
[recovery](DirtyRetry.lean) preserves it at every interruption point.
A successful open gives the next writer a settled history again.

For a background writeback, the important physical question is whether it happens before
or after a truncate. The [append proof](AppendWriteback.lean) absorbs writeback into the
corresponding data or marker barrier. The [reopen proof](ReopenWriteback.lean) moves
writebacks to either side of the existing recovery proof while preserving its exact result
and file images. [Trace composition](ScheduledExecution.lean) then reuses the client contract.

The result is conditional on the modeled crash outcomes and experimental
limits. The [design's proof summary](../../../../../docs/design/wal-recovery.md#what-the-single-file-proof-establishes)
states those assumptions and what remains outside the theorem. Run
`bash scripts/check-wal-recovery-slice.sh` from the repository root for the
slice's kernel and axiom checks, simulations and Linux fixtures.

## Native recovery worker

`SingleFile.install` calls the shared `recoverWith` worker after opening the
segment and the policy's marker files. Recovery reads and repairs the
segment through one read/write description and syncs that same description.
The append stream retains its own data barrier. Explicit-length
`ftruncate` replaces the extra prefix read and cursor-based truncate.

[`SingleFile.recover_eq`](NativeRecovery.lean) connects the worker's
descriptor-level interpretation to the existing recovery model. It checks
the start-of-file reads, the marker pair selected by slot, the repair length,
and the sync of the repaired data description through the shared code.
[`Child.Recoverable.nativeRecovery`](../Segmented/Proofs/SegmentRecovery.lean)
uses that result to preserve the retry invariant at the reached image and
supply the installed cursor and history on success. This composition is
generic over the admitted input state, policy and primitive reports.

| Boundary | Premise owner |
| --- | --- |
| Read from start | The runtime rewinds and returns the whole file as exact bytes, or raises a read error. The read leaves the projected file image alone. |
| Truncate at a length | The descriptor refers to the data file. The native wrapper issues `ftruncate` for the selected prefix length. The filesystem supplies whether an error precedes or follows the file change. The supported lengths fit Linux x86-64 `off_t`. |
| Sync | The runtime issues fsync on the supplied description. The filesystem supplies whether the sync effect happened. The existing recovery schedule orders both marker barriers and the data repair. |
| Acquisition and lifetime | The worker assumes the already held data and marker descriptions come from the locked directory. The proof connecting native acquisition, post-recovery policy and directory barriers, cleanup, and the actual returned handle remains open. |
| Background persistence | The worker proof uses `Persistence.Effects`. Coupling independent writeback in a native run to the existing scheduled recovery theorem remains open. |

The single-file check kernel-checks and audits the worker proof and runs
the native recovery and partial-write fixtures. The segmented check
audits the consumer composition. The fixtures exercise Linux error and
recovery paths. The refinement is relative to the primitive effects above.
