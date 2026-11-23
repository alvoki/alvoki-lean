# Alvoki

Alvoki explores formally verified storage primitives in native Lean 4. The experiments cover packed lookup, scans, encoding, and right-biased merge of immutable sorted key–value runs. Lean and Verus proofs cover the search core, and Lean also checks byte-level contracts for packed readers and builders.

- [Performance guide for Lean reads, writes, merge, and code generation](docs/high-performance-lean.md)
- [Repository review and architectural priorities](docs/repository-review.md)
- [Binary format and behavior](docs/specifications.md)
- [Current module and benchmark map](docs/architecture.md)
- [VM measurements and code generation findings](docs/benchmarks.md)
- [Proof coverage and assumptions](docs/verification-status.md)
- [Roadmap](docs/roadmap.md) and [handoff](docs/progress.md)

## Reproduce on Linux x86-64

Run from the repository root with Bash, curl, unzip, and Python 3 available. The bootstrap script installs pinned tools in `../work/toolchains`. Set `ALVOKI_TOOLCHAINS` and pass the same directory to bootstrap to use a different location.

```sh
bash scripts/bootstrap.sh
bash scripts/reproduce.sh
bash scripts/reproduce.sh --out /tmp/alvoki-trials.csv
python3 benchmarks/summarize.py /tmp/alvoki-trials.csv
bash scripts/environment.sh
```

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
