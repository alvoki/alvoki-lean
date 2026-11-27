# Alvoki documentation

Start with the question you have about the sequential Linux engine.

| Question | First read | Follow through |
|---|---|---|
| How do I run it? | [Getting started](getting-started.md) | [Source and build targets](../lean/README.md) |
| When does a write become visible and durable? | [Storage architecture](architecture.md#sequential-storage) | [Format and client contracts](specifications.md) |
| What does a read on a reopened table mean? | [Six system claims](proof-architecture.md#system-claims) | [From file bindings to installed session and history](proofs/native-storage.md#refinement-boundaries) · [Point lookup in the code](../lean/Alvoki/Storage/Table/README.md) |
| Which executions have been verified? | [Verification status](verification-status.md) | [Which premises come from Linux?](proofs/native-storage.md#premise-provenance) |
| Which proof should I work on next? | [Current handoff](progress.md) | [Open proof milestones](proof-roadmap.md#completion-checklist-for-native-key-value-refinement) · [Reusable proof techniques](proof-index.md) |

For engine features and priorities, see the [development roadmap](roadmap.md). For performance methodology and measurements, see [benchmarks](benchmarks.md) and the [Lean performance guide](high-performance-lean.md).
