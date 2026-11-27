# Lean source

The current implementation is under [Alvoki/Experiments](Alvoki/Experiments). It contains independent contracts, executable models and native adapters for durable blobs, manifests, immutable SSTables, and a segmented WAL. [Shared codec primitives](Alvoki/Codec/Block.lean) and [block proof contracts](Alvoki/Kernel/BlockContracts.lean) are imported by the SSTable component and are kept outside its implementation.

The principal verification entry points are the component scripts under [`../scripts`](../scripts): `check-experimental-manifest.sh`, `check-wal-recovery-slice.sh`, `check-segmented-wal.sh`, and the SSTable checks. They run focused kernel, axiom, model, and native checks. `lakefile.lean` describes the shared component libraries; `lake build` builds the retained component roots.

| Location | Purpose |
|---|---|
| [Alvoki/Experiments](Alvoki/Experiments/README.md) | Component implementations and their guides. |
| [Alvoki/Codec](Alvoki/Codec) and [Alvoki/Kernel](Alvoki/Kernel) | Shared byte encoding and proved block contracts. |
| [Alvoki/Checks/Audit](Alvoki/Checks/Audit) | Axiom policy and proof dependency audit support. |
| [native](native/README.md) | Linux sync, checked directory listing, and SSTable C bindings. |

The project-level [reproduction guide](../README.md#build-and-verify) lists the pinned toolchain setup and current checks.
