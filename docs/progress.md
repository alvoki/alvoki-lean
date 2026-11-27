# Current handoff

**Current direction.** Alvoki is being simplified around independent Lean storage components. DurableBlob, Manifest, immutable SSTable, and segmented WAL retain their contracts, models, proofs, and selected native fixtures. L0 integration and native WAL refinement remain active follow-up work. The retired `DiskTable` engine was a separate implementation and is no longer the baseline for those components.

**Single-file WAL.** Public native recovery settles and installs the selected
history (#8). The append producer uses the same installed writer and marker
roles, preserves the sole submitted batch as the retry choice after an
uncertain result, and composes with the existing segmented child contract.
[Native proofs and premises](../lean/Alvoki/Experiments/WAL/Proofs/README.md)

**Next open obligation.** Connect segmented root recovery, CONTROL
publication, and rotation to the actual Linux operations. Preserve the
reached state after a sync that may have taken effect, and show that
repeated successful opens select the same view. The filesystem supplies
the effect of a failed sync. [Segmented WAL guide](../lean/Alvoki/Experiments/WAL/Segmented/README.md)
· [WAL fault assumptions](design/wal-recovery.md)

**Verification baseline.** The integrated recovery candidate for #8 passed
`bash scripts/reproduce.sh` on the repository after the legacy-engine
cleanup. The command checks the kernel and axioms, modeled fault schedules,
and selected native fixtures. [Checks](../lean/Alvoki/Checks/README.md)
