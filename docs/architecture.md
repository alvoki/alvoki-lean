# Repository architecture

Alvoki studies a small storage unit end to end. It loads immutable little-endian bytes, validates length and key order, searches or scans the packed data, and optionally merges two runs into a new version-1 block. A logical record sequence provides the reference behavior for proofs and fixture oracles. The repository contains multiple executable implementations built during the experiments. [Format and behavior](specifications.md) · [Verification status](verification-status.md)

## Lean paths

| Path | What it does | Dependencies |
|---|---|---|
| [`Block`](../lean/Block.lean) and [`Main`](../lean/Main.lean) | Original packed parser, point and range access, and encode/decode comparisons. The default Lake executable uses this path. | `Std`. [`Proofs`](../lean/Proofs.lean) checks lower bound, lookup, ranges and word codec properties. |
| [`Optimizations`](../lean/Optimizations.lean) and [`OptMain`](../lean/OptMain.lean) | Machine-index view over v1 or v2, packed search and scan, and owned-record codec comparisons. | `Block` for the original operations and model. [`OptProofs`](../lean/OptProofs.lean) connects the optimized reader and search to the original code. |
| [`PackedRun`](../lean/PackedRun.lean) | Validated v1 runs, simple materialized merge, and bulk payload copies for disjoint inputs. | `Optimizations` for the packed view. [`Packed`](../lean/Packed.lean) adds packed ownership and an experimental C encoder. |
| [`ScopedBytes`](../lean/ScopedBytes.lean) | Independent append-only builder with slice bounds, exact source bytes and prefix contracts. | `Std`. The larger [`ScopedBytesProofs`](../lean/ScopedBytesProofs.lean) module currently also imports the replay stack for integration proofs. |
| [`NativeTune`](../lean/NativeTune.lean) | Scalar and compiler-vectorized scans, span strategies, and packed transforms. | `PackedRun`. |
| [`MergePhases`](../lean/MergePhases.lean) | Online selection, trace replay, emission variants, and replay refinement. | `NativeTune` and `ScopedBytes`. The trace checker covers opcodes and cursor bounds. Fixtures supply the merge decisions. |
| [`FusedMerge`](../lean/FusedMerge.lean) | Bounded-window merge into a packed destination and direct merged checksum scans. | `NativeTune` and `ScopedBytes`. |

The ordinary build uses the standard Lean runtime. [`lean/native`](../lean/native) and [`lean/runtime-experiment`](../lean/runtime-experiment) contain separate C and link-time experiments, including fixed-width copies and whole-loop scoped fill. Those experiments target the pinned generated-code ABI. [Lake build targets](../lean/lakefile.toml) · [Scoped runtime contract](scoped-builder.md#contract-and-checks)

## Comparisons and evidence

- [Rust](../rust) holds the original borrowed-block implementation and focused packed controls with scalar, SIMD and scoped-output comparisons. [Verus](../verus/search.rs) checks a separate search core over logical sorted keys.
- [Fixtures](../fixtures/generate.py) build the little-endian binary data independently. The Python oracles use bisection, dictionaries, and fixed-width checksum arithmetic. [Benchmark drivers](../benchmarks) run the executables on shared inputs, verify outputs, and record raw trial time and process peak memory where measured.
- [Scripts](../scripts) build the individual release targets and run the corresponding fixtures or proof checks. [Reproduction commands](../README.md#reproduce-on-linux-x86-64) link each experiment report and its data.

[Performance technique guide](high-performance-lean.md) · [Repository review and proposed boundaries](repository-review.md)
