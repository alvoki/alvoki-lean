# Roadmap

The stock correctness command, validated v1 run API, standalone byte proofs, and shared refinement model for the per-record merge and branching direct scan are in place. [Architecture](architecture.md) · [Verification status](verification-status.md)

1. Finish the full-block codec round trip and prove the adaptive span emitter, the bounded-window emitter, and checked replay against the same union model.
2. Measure representative compaction traces and evaluate a standard Lean write primitive against the byte contract. Specify tombstones and snapshot visibility before implementing compaction.
3. Model persistence with explicit filesystem assumptions, then add WAL, manifests, recovery, and fault injection.
4. Evaluate MVCC, concurrency, and transaction semantics after a sequential LSM model stabilizes.
5. Study object storage and reactive materialization once the local engine supports repeatable correctness and performance experiments.
