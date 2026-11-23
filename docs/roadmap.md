# Roadmap

The stock correctness command, validated v1 run API, standalone byte proofs, and shared refinement model for the per-record merge and branching direct scan are in place. [Architecture](architecture.md) · [Verification status](verification-status.md)

The v1 round trips, the adaptive and bounded-window emitter refinements, and checked streaming replay are complete. Versioned workload proxies now exercise compaction and snapshot visibility and compare a fixed-width copy candidate against the stock builder. [Fast-path refinement](fast-path-refinement.md) · [Compaction experiment](compaction.md)

The [proof roadmap](proof-roadmap.md) specifies the theorem targets behind these milestones, starting with snapshot preservation and the v3 codec.

1. Connect the versioned compaction implementation to the retention and snapshot model. Measure traces from a sequential multi-run compaction prototype and add coverage for older runs and output reuse.
2. Evaluate a standard Lean write specialization across full compaction pipelines. Use trace evidence to choose the fixed-width or scoped-fill contract and show which paths benefit.
3. Model persistence with explicit filesystem assumptions, then add WAL, manifests, recovery, and fault injection.
4. Evaluate MVCC, concurrency, and transaction semantics after a sequential LSM model stabilizes.
5. Study object storage and reactive materialization once the local engine supports repeatable correctness and performance experiments.
