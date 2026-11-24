# Alvoki

Alvoki is a sequential storage engine in native Lean 4 with versioned packed runs, snapshot reads, a write-ahead log, and atomic checkpoints. Lean proofs connect its executable operations and modeled recovery to a logical database. Separate Lean and Rust experiments compare packed reads, merge, and byte-oriented writers. Verus verifies a sorted-key search core.

- [Engine API and I/O protocol](docs/architecture.md#sequential-storage)
- [Binary formats and visibility](docs/specifications.md)
- [Proof coverage and assumptions](docs/verification-status.md)
- [Roadmap](docs/roadmap.md), [proof roadmap](docs/proof-roadmap.md), and [progress](docs/progress.md)
- [Performance guide](docs/high-performance-lean.md) and [benchmarks](docs/benchmarks.md)

## Stock Lean API

Import `PackedRun` and use `Alvoki.Packed.parseRun` to validate a version-1 block. The returned run supports checked record access, lookup, and half-open range checksums. `Alvoki.Packed.merge` produces the version-1 right-biased union, and `Alvoki.Packed.scanMerged` folds it directly. Import `SpanMerge` for the proved span writer or `BlockCodec` for the round-trip-checked v1 encoder and decoder. [Implementation and proof boundaries](docs/verification-status.md)

Import `Alvoki.Storage.Table.PackedTable` for a sequential snapshot table over packed v3 runs. Import `Alvoki.Storage.Disk.DiskTable` for the Linux adapter with a write-ahead log, checkpoints, and reopen. The adapter uses an existing dedicated directory. A snapshot handle belongs to its open session. Run `bash scripts/check-sequential.sh` from the root to build and exercise both APIs and audit the proofs. [Engine API and checkpoint protocol](docs/architecture.md#sequential-storage)

## Reproduce on Linux x86-64

Run from the repository root with Bash, curl, tar, unzip, sha256sum, and Python 3 available. The bootstrap script installs pinned tools in `../work/toolchains`. Set `ALVOKI_TOOLCHAINS` and pass the same directory to bootstrap to use a different location.

```sh
bash scripts/bootstrap.sh
bash scripts/check.sh
bash scripts/check-sequential.sh

# Optional runtime prototypes and baseline timings.
bash scripts/check.sh --runtime
bash scripts/reproduce.sh --out /tmp/alvoki-trials.csv
python3 benchmarks/summarize.py /tmp/alvoki-trials.csv
bash scripts/environment.sh
```

GitHub Actions runs both stock check commands. `check.sh` runs Lean, Rust, and Verus checks for the packed primitives. `check-sequential.sh` runs the storage-engine proofs, transitive axiom audit, differential tests, and native fault fixtures. The runtime option runs the opt-in C and linkage experiment fixtures. Benchmark drivers require Python assertions to be enabled. [Correctness workflow](.github/workflows/correctness.yml)

The default reproduction builds the baseline Lean and Rust executables, checks the original Lean theorems and their axioms, runs Verus, and compares both baseline Lean variants and Rust with the Python reference. The `--out` flag additionally benchmarks all three configurations. Use `--sizes 1000 --trials 3` for a shorter run. The experiment reports give the commands for later workloads. [Experiment index](docs/benchmarks.md#packed-storage-experiments)

## Storage engine replay benchmark

```sh
bash scripts/disk-replay.sh --out /tmp/alvoki-replay-before.csv
bash scripts/disk-replay.sh --out /tmp/alvoki-replay-after.csv \
  --baseline /tmp/alvoki-replay-before.csv
```

The native benchmark measures reopening databases with the same keys inserted in ascending, descending, and seeded shuffled order. It records individual samples and compares medians against a saved run on the same machine. Add `--max-slowdown 1.25` to fail a comparison when any median exceeds 125% of its baseline. [Workload and measurements](docs/benchmarks.md#disk-replay)
