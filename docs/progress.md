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
a failed reopen, and two successful opens. Native rotation and append
still need to preserve and return the exact successor child authority.
The native append schedule now carries that successor through a scoped
continuation. Non-rotating append consumes the recovered child phase and
produces the acknowledged session or the recoverable reached image.
Complete the producer for fresh child creation and connect it to the
rotation proof and subsequent recovery. Bootstrap and mutations must
supply CONTROL representability.
[Segmented WAL guide](../lean/Alvoki/Experiments/WAL/Segmented/README.md)
· [WAL fault assumptions](design/wal-recovery.md)

**Verification baseline.** The integrated recovery candidate for #8 passed
`bash scripts/reproduce.sh` on the repository after the legacy-engine
cleanup. The command checks the kernel and axioms, modeled fault schedules,
and selected native fixtures. [Checks](../lean/Alvoki/Checks/README.md)
