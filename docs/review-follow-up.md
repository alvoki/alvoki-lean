# Repository review follow-up

The stock Lean and Rust replay CLIs now verify each supplied decision against the two current keys and require complete input consumption. The regression fixtures cover both traces from the review. Online selection and merge use the runs directly. The packed run API checks natural-number indices before conversion to machine width. Rust's borrowed block offers checked indexing and its panicking accessor checks before computing an offset. [Original findings](repository-review.md#findings) · [Replay fixtures](../benchmarks/merge_phases.py) · [Lean API](../lean/PackedRun.lean) · [Rust API](../rust/src/lib.rs)

The stock gate and the opt-in runtime gate passed on a fresh toolchain install. The generic byte proofs build independently of replay. Parser acceptance now connects the optimized reader and lower bound to the logical records. The stock per-record merge and the branching direct scan refine a shared right-biased union model. The GitHub Actions workflow runs the stock gate, with the runtime gate available by manual dispatch. [Proof coverage](verification-status.md) · [Correctness workflow](../.github/workflows/correctness.yml)

## Stock Lean comparison

The paired run used one million records, the same inputs for each build, 12 process rounds per build in randomized order on one pinned CPU, and three retained trials per process. Medians are in milliseconds. The pre-review and candidate revisions and toolchains are recorded with the raw trials. [Paired trials](../benchmarks/review-follow-up/paired-trials.csv) · [Environment](../benchmarks/review-follow-up/environment.txt)

| Workload | Before | After |
|---|---:|---:|
| Validate interleaved | 0.447 | 0.281 |
| Validate columnar | 0.443 | 0.277 |
| Adaptive merge, alternating | 8.273 | 8.032 |
| Adaptive merge, clustered | 1.326 | 1.383 |
| Adaptive merge, update-heavy | 5.541 | 5.273 |
| Direct scan, alternating | 2.158 | 2.024 |
| Direct scan, shuffled | 6.256 | 5.985 |

Validation carries a byte cursor and a proof that it matches the logical record index. The generated loop advances the cursor by adding the stride and uses a proved extent for the wide load. The paired merge and scan medians changed by at most 6.2% in either direction on this VM. The single-run packed scan still generates vector instructions. [Validator](../lean/PackedView.lean#L153) · [Paired trials](../benchmarks/review-follow-up/paired-trials.csv)

## Matched Rust span control

The fused suite now includes a Rust emitter with the same eight-record probe, 256-record window, and right-biased merge policy as the stock Lean fused emitter. The Rust implementation uses safe slice copies. At one million inputs, the clustered merge took 0.98 ms in fused Lean and 0.89 ms in Rust with spans. The clustered merge–validate–scan–lookup pipeline took 5.15 and 5.56 ms. The fastest Rust variants for alternating and shuffled inputs used per-record emission. [Rust span emitter](../rust/src/bin/alvoki-merge-phases.rs) · [Fused trials](../benchmarks/review-follow-up/fused-merge-trials.csv)

## Reproduce

Run from the repository root. Bootstrap first and use its toolchain directory for both checkouts.

```sh
bash scripts/check.sh
bash scripts/check.sh --runtime
export ALVOKI_TOOLCHAINS="$(realpath "${ALVOKI_TOOLCHAINS:-../work/toolchains}")"
before=$(mktemp -d)
git archive b6b4f2e | tar -x -C "$before"
for suite in fused-merge optimize native; do
  (cd "$before" && bash "scripts/$suite.sh")
done
python3 benchmarks/compare_stock.py --baseline-bin "$before/lean/.lake/build/bin" \
  --out /tmp/alvoki-paired-trials.csv
for suite in fused-merge optimize native merge-phases stock-builder; do
  bash "scripts/$suite.sh" --out "/tmp/alvoki-$suite-trials.csv" --sizes 1000000 --trials 9
done
```

The review batches use the suites' release builds, deterministic fixture data, pinned CPU, one warm-up per process, and nine retained trials. The paired run uses the process allocation described above. The original experiment data remains available. [Optimization trials](../benchmarks/review-follow-up/optimize-trials.csv) · [Native trials](../benchmarks/review-follow-up/native-trials.csv) · [Merge phases](../benchmarks/review-follow-up/merge-phases-trials.csv) · [Stock builder trials](../benchmarks/review-follow-up/stock-builder-trials.csv)

The next proof targets are the faster span emitters, acceptance of replay against the union model, and the full-block codec round trip. Real compaction traces and an upstream write primitive remain follow-up work. [Roadmap](roadmap.md)
