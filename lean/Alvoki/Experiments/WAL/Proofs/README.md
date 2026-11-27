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
