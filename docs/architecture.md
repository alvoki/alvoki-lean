# Repository architecture

Alvoki studies a small storage unit end to end. It loads immutable little-endian bytes, validates length and key order, searches or scans the packed data, and optionally merges two runs into a new version-1 block. A logical record sequence provides the reference behavior for proofs and fixture oracles. The repository contains multiple executable implementations built during the experiments. [Format and behavior](specifications.md) · [Verification status](verification-status.md)

## Lean paths

| Path | What it does | Dependencies |
|---|---|---|
| [`Block`](../lean/Block.lean) and [`Main`](../lean/Main.lean) | Original packed parser, point and range access, and encode/decode comparisons. The baseline Lake executable uses this path. | `Std`. [`Proofs`](../lean/Proofs.lean) checks lower bound, lookup, ranges and word codec properties. |
| [`PackedView`](../lean/PackedView.lean) | Machine-index view, checked record access and packed search and scan. The parser checks v1 interleaved or experimental v2 columnar data. | `Block` for the original word decoder. [`PackedViewProofs`](../lean/PackedViewProofs.lean) connects parser acceptance and native indexing to the logical record layout. The standalone [optimization driver](../lean/OptMain.lean) also exercises experimental owned-record codecs. |
| [`PackedRun`](../lean/PackedRun.lean) | The validated v1 API and stock per-record materialized merge. Lake builds it by default alongside the baseline executable. | [`MergeModel`](../lean/MergeModel.lean) specifies the right-biased union over logical rows and their bytes. [`Packed`](../lean/Packed.lean) adds packed ownership and an experimental C encoder. |
| [`ScopedBytes`](../lean/ScopedBytes.lean) | Independent append-only builder with slice bounds, exact source bytes and prefix contracts. | `Std`. [`ScopedBytesProofs`](../lean/ScopedBytesProofs.lean) checks the generic byte operations against this module. |
| [`NativeTune`](../lean/NativeTune.lean) | Scalar and compiler-vectorized scans, span strategies, and packed transforms. | `PackedRun`. |
| [`MergePhases`](../lean/MergePhases.lean) | Online selection, checked trace replay and emission variants. The trace checker checks keys as well as cursor consumption. | `NativeTune` and `ScopedBytes`. [`ReplayProofs`](../lean/ReplayProofs.lean) audits the streaming and prepared replay proofs. |
| [`FusedMerge`](../lean/FusedMerge.lean) | Bounded-window merge into a packed destination and direct merged checksum scans. | `PackedRun` and `ScopedBytes`. [`MergeProofs`](../lean/MergeProofs.lean) audits the per-record merge and branching direct scan against the same union. |

The ordinary build uses the standard Lean runtime. [`lean/native`](../lean/native) and [`lean/runtime-experiment`](../lean/runtime-experiment) contain separate C and link-time experiments, including fixed-width copies and whole-loop scoped fill. Those experiments target the pinned generated-code ABI. [Lake build targets](../lean/lakefile.toml) · [Scoped runtime contract](scoped-builder.md#contract-and-checks)

## Comparisons and evidence

- [Rust](../rust) holds the original borrowed-block implementation and focused packed controls with scalar, SIMD and scoped-output comparisons. [Verus](../verus/search.rs) checks a separate search core over logical sorted keys.
- The Python fixture generator builds the little-endian binary data independently. Drivers share generation, oracles, subprocess and reporting helpers. The timed operations stay in each individual release executable. [Fixtures](../fixtures/generate.py) · [Shared benchmark support](../benchmarks/support.py)
- One stock correctness command runs the Lean and Rust fixtures and proof audits. The runtime option exercises the separate prototypes. [Correctness command](../scripts/check.sh) · [Reproduction commands](../README.md#reproduce-on-linux-x86-64)

[Performance technique guide](high-performance-lean.md) · [Repository review and proposed boundaries](repository-review.md)
