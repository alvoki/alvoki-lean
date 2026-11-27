# Alvoki Lean modules

The retained implementation is under [Experiments](Experiments/README.md): DurableBlob, Manifest, immutable SSTable, and WAL components. Shared byte primitives live in [Codec](Codec/Block.lean); [Kernel](Kernel/BlockContracts.lean) contains contracts used by the SSTable proofs. [Checks/Audit](Checks/Audit/README.md) contains the axiom policy and dependency probe.

Run the component checks with [`scripts/reproduce.sh`](../../scripts/reproduce.sh).
