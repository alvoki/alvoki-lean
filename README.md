# Alvoki

Alvoki explores formally verified storage primitives in native Lean 4. The experiments cover packed lookup, scans, encoding, and right-biased merge of immutable sorted key–value runs. Lean and Verus proofs cover the search core, and Lean also checks byte-level contracts for packed readers and builders.

- [Performance guide for Lean reads, writes, merge, and code generation](docs/high-performance-lean.md)
- [Repository review and architectural priorities](docs/repository-review.md)
- [Binary format and behavior](docs/specifications.md)
- [Current module and benchmark map](docs/architecture.md)
- [VM measurements and code generation findings](docs/benchmarks.md)
- [Proof coverage and assumptions](docs/verification-status.md)
- [Proof roadmap from binary codecs to storage guarantees](docs/proof-roadmap.md)
- [Roadmap](docs/roadmap.md) and [handoff](docs/progress.md)

## Stock Lean API

Import `PackedRun` and use `Alvoki.Packed.parseRun` to validate a version-1 block. The returned run supports checked record access, lookup, and half-open range checksums. `Alvoki.Packed.merge` produces the version-1 right-biased union, and `Alvoki.Packed.scanMerged` folds it directly. Import `SpanMerge` for the proved span writer or `BlockCodec` for the round-trip-checked v1 encoder and decoder. [Implementation and proof boundaries](docs/verification-status.md)

## Reproduce on Linux x86-64

Run from the repository root with Bash, curl, tar, unzip, sha256sum, and Python 3 available. The bootstrap script installs pinned tools in `../work/toolchains`. Set `ALVOKI_TOOLCHAINS` and pass the same directory to bootstrap to use a different location.

```sh
bash scripts/bootstrap.sh
bash scripts/check.sh
bash scripts/check.sh --runtime
bash scripts/reproduce.sh --out /tmp/alvoki-trials.csv
python3 benchmarks/summarize.py /tmp/alvoki-trials.csv
bash scripts/environment.sh
```

The stock check runs the baseline, latest Lean and Verus proof audits, and exact-output fixtures. GitHub Actions runs the same command. The runtime option runs the opt-in C and linkage experiment fixtures. Benchmark drivers require Python assertions to be enabled. [Correctness workflow](.github/workflows/correctness.yml)

The default reproduction builds the baseline Lean and Rust executables, checks the original Lean theorems and their axioms, runs Verus, and compares both baseline Lean variants and Rust with the Python reference. The `--out` flag additionally benchmarks all three configurations. Use `--sizes 1000 --trials 3` for a shorter run. The sections below give the build, proof, and fixture commands for the later experiments.

## Optimization experiments

```sh
bash scripts/optimize.sh --out /tmp/alvoki-opt-trials.csv --trials 9
python3 benchmarks/optimize.py --summarize /tmp/alvoki-opt-trials.csv
```

The suite compares the existing implementations with native Lean specializations and a layout-matched Rust control. See the [optimization report](docs/optimizations.md).

## Packed ownership, merge, and bulk writes

```sh
bash scripts/packed.sh --out /tmp/alvoki-packed.csv
python3 benchmarks/packed.py --summarize /tmp/alvoki-packed.csv
```

The script builds a separate experiment binary with optional C-backed modes. See the [experiment results and C interface contract](docs/packed-experiments.md).

## Native SIMD and merge spans

```sh
bash scripts/native.sh --out /tmp/alvoki-native.csv
python3 benchmarks/native.py --summarize /tmp/alvoki-native.csv
```

This suite compares a compiler-vectorized native Lean scan, Rust scalar and SIMD controls, and native merge and encoding variants. [SIMD results and assembly evidence](docs/native-experiments.md) · [Single-record emission and packed updates](docs/emission-experiments.md)

## Merge selection and output replay

```sh
bash scripts/merge-phases.sh --out /tmp/alvoki-merge-phases.csv
python3 benchmarks/merge_phases.py --summarize /tmp/alvoki-merge-phases.csv
```

[Phase timings and next experiments](docs/merge-phases.md)

## Fixed-width copy specialization

```sh
bash scripts/fixed-copy.sh --out /tmp/alvoki-fixed-copy.csv
python3 benchmarks/fixed_copy.py --summarize /tmp/alvoki-fixed-copy.csv
```

[Copy-width sweep and packed-pipeline results](docs/fixed-copy.md)

## Scoped output builder

```sh
bash scripts/scoped-builder.sh --out /tmp/alvoki-scoped-builder.csv
python3 benchmarks/scoped_builder.py --summarize /tmp/alvoki-scoped-builder.csv
```

[Scoped builder results, Rust controls, and trust assumptions](docs/scoped-builder.md)

## Proved builder on stock Lean

```sh
bash scripts/stock-builder.sh --out /tmp/alvoki-stock-builder.csv
python3 benchmarks/stock_builder.py --summarize /tmp/alvoki-stock-builder.csv
```

[Byte-level contracts, stock benchmarks, and open optimization work](docs/stock-builder.md)

## Fused span emission and direct scans

```sh
bash scripts/fused-merge.sh --out /tmp/alvoki-fused-merge.csv
python3 benchmarks/fused_merge.py --summarize /tmp/alvoki-fused-merge.csv
```

[Stock Lean timings, peak memory, and correctness checks](docs/fused-merge.md)

## Versioned compaction experiment

Compare stock Lean and Rust compaction over versioned runs with tombstones and an oldest retained snapshot. The optional fixed-copy build measures the existing native specialization on the same workload.

```sh
bash scripts/compaction.sh --fixed-copy --out /tmp/alvoki-compaction.csv
python3 benchmarks/compaction.py --summarize /tmp/alvoki-compaction.csv
```

[Compaction semantics and results](docs/compaction.md)
