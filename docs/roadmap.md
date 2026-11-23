# Roadmap

1. Finish the version 1 codec and parser refinement. Isolate native word loads and stores, fixed-width index arithmetic, search specialization, and packed or streaming decode in separate measurements.
2. Add sorted-run merge and specify tombstone and snapshot visibility before implementing compaction.
3. Model persistence with explicit filesystem assumptions, then add WAL, manifests, recovery, and fault injection.
4. Evaluate MVCC, concurrency, and transaction semantics after a sequential LSM model stabilizes.
5. Study object storage and reactive materialization once the local engine supports repeatable correctness and performance experiments.

Reusable candidates from the first experiment include a little-endian word API for Lean's packed bytes with bounds and read/write lemmas, and a regression benchmark for unboxing and specialization in a binary search over primitive packed data. Confirm the current Lean Std, CSLib, Mathlib and Reservoir APIs before pursuing an upstream implementation.
