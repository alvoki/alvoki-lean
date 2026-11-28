# Current handoff

**Current direction.** Alvoki is being simplified around independent Lean storage components. DurableBlob, Manifest, immutable SSTable, and segmented WAL retain their contracts, models, proofs, and selected native fixtures. L0 integration and native WAL refinement remain active follow-up work. The retired `DiskTable` engine was a separate implementation and is no longer the baseline for those components.

**Single-file WAL.** Public native recovery settles and installs the selected
history (#8). The append producer uses the same installed writer and marker
roles, preserves the sole submitted batch as the retry choice after an
uncertain result, and composes with the existing segmented child contract.
[Native proofs and premises](../lean/Alvoki/Experiments/WAL/Proofs/README.md)

**Segmented WAL recovery.** The public open proof connects the installed active
child to the single-file append producer on the reached disk. The reported
failure case proves scoped child release and root unlock while preserving the
primary error and recoverable disk. The native CONTROL interpretation supplies the existing publication cuts,
including the joint CONTROL and child-name root barrier. Its discard
continuation preserves the permitted view through a failed publication,
a failed reopen, and two successful opens. The append candidate composes native child creation, CONTROL publication,
and both append paths. Its public postcondition carries the ready session
and the child authority at the exact reached disk. The create and reopen
producers establish that authority, and successful append returns it.
The recovery continuation selects and pins a view from the reached disk;
bounded admissible views supply CONTROL representability. The candidate
still needs integration review.
[Segmented WAL guide](../lean/Alvoki/Experiments/WAL/Segmented/README.md)
· [WAL fault assumptions](design/wal-recovery.md)

**Compact WAL experiment.** Native handles carry cursors, CONTROL metadata
and ownership. The read-only fold composes ordered child reads, and the
scoped L0 replay fixture validates deferred decoding with the agreed error
priority. The next proof premise is native correspondence for the bounded
read and compact open producers before joint L0 integration.
[Checkpoints, migration and measurements](design/wal-compact-implementation.md)

**Verification baseline.** The integrated recovery candidate for #8 passed
`bash scripts/reproduce.sh` on the repository after the legacy-engine
cleanup. The command checks the kernel and axioms, modeled fault schedules,
and selected native fixtures. [Checks](../lean/Alvoki/Checks/README.md)
