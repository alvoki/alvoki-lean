# Component benchmark guide

The historical benchmark suites for the retired DiskTable engine and fixed-width PackedRun implementation have been removed. Measure a component when a concrete implementation choice needs performance evidence; keep its workload, toolchain, platform, raw trials, and reproduction command beside that component's code or PR.

Do not compare a new component against measurements from the old engine unless the workload and interface are demonstrably equivalent. Model correctness, native fixture coverage, native refinement, and runtime performance are separate evidence.

## Measurement practices that remain useful

- Use release builds, deterministic inputs, and the same observable work on both sides of a comparison. State whether timing includes opening, validation, allocation, sync, lookup, or output checking; use an independent oracle for correctness.
- Pin and record the Lean toolchain, compiler, platform, CPU affinity, cache condition, warm-up, and timed boundary. Save raw trial rows. Prefer interleaved paired runs and a same-build A/A control when differences are small; report the cohort and spread, not only the fastest run.
- Measure the end-to-end component path as well as isolated phases. A faster encoder or replay loop may lose after validation, allocation, sync, or setup is included. Do not compare historical cohorts whose workloads or durability protocols differ.
- For Lean byte-processing loops, borrow immutable input where possible and avoid materializing per-row objects when the consumer can fold a stream. Validate extents at the boundary, carry the proved bound through the loop, and keep machine-sized offsets within that bound. These are hypotheses to measure on the real consumer.
- `ByteArray` capacity hints and private fields do not prove unique ownership. Copy-on-write checks, bounds checks, generic calls, and byte-at-a-time emission can remain in generated code. Inspect generated C and target assembly for the measured release build; simple loops may vectorize while manual unrolling may not.
- Prefer a bulk copy or pre-sized output only when the full workload benefits. Allocation, zero-initialization, an exact-size prepass, branching, and write amplification can outweigh fewer calls. Keep a simpler control and at least one workload with a different key/order distribution.
