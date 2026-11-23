# Roadmap

1. Establish a single stock Lean correctness command covering the current proof targets and exact-output fixtures.
2. Extract one validated version-1 run API and finish the codec and parser refinement. Keep the byte builder and its generic proofs independent of the merge experiments.
3. Prove a stock materialized merge and direct fold against the same right-biased union model. Measure representative key distributions and evaluate a standard Lean write primitive against the byte contract. Specify tombstones and snapshot visibility before implementing compaction.
4. Model persistence with explicit filesystem assumptions, then add WAL, manifests, recovery, and fault injection.
5. Evaluate MVCC, concurrency, and transaction semantics after a sequential LSM model stabilizes.
6. Study object storage and reactive materialization once the local engine supports repeatable correctness and performance experiments.

The [repository review](repository-review.md#recommended-order-of-work) gives completion checks for the first steps. The [performance guide](high-performance-lean.md) records the code-generation evidence and stock alternatives for packed reads and writes.
