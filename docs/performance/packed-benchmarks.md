# Packed benchmark history

## First VM measurements

In the baseline experiment, whole-block validation and materialized decoding had larger overhead than random lookups. Encoding improved when the Lean byte append loop was unrolled. A single extent check in place of eight checked reads did not consistently speed up packed query workloads.

### One million records

Median of seven timed batches after one warm-up. Ratios are elapsed time relative to Rust. Scan times include two lower-bound searches and traversal of matching records.

| Workload | Rust | Lean | Lean optimized | Lean / Rust | Optimized / Rust |
|---|---:|---:|---:|---:|---:|
| Random hit | 182 ns | 510 ns | 547 ns | 2.80× | 3.00× |
| Random miss | 186 ns | 512 ns | 547 ns | 2.76× | 2.94× |
| Mixed random | 179 ns | 502 ns | 544 ns | 2.80× | 3.03× |
| Sequential hit | 45 ns | 369 ns | 375 ns | 8.20× | 8.34× |
| Small range | 297 ns | 1.09 µs | 1.09 µs | 3.67× | 3.67× |
| Large range | 4.93 µs | 36.43 µs | 36.99 µs | 7.39× | 7.50× |
| Encode | 1.34 ms | 59.12 ms | 31.36 ms | 44.27× | 23.48× |
| Decode | 0.79 ms | 35.52 ms | 34.98 ms | 45.22× | 44.54× |
| Validate in memory | 0.58 ms | 15.62 ms | 15.56 ms | 26.87× | 26.78× |
| Warm file load and validate | 1.55 ms | 17.93 ms | 16.92 ms | 11.54× | 10.89× |

Checked Lean mixed random lookups were 4.21× Rust time at 1,000 records and 3.83× at 100,000. At one million records, mixed lookup throughput was 5.57 million/s in Rust and 1.99 million/s in checked Lean. Optimized Lean encoding rose from 258 to 487 MiB/s at that scale. Peak process RSS for materialized decode was approximately 32 MiB in Rust and 100 MiB in Lean. This includes the loaded blocks, runtime, and allocations across all repetitions in that process.

### Method

The KVM guest reports AMD EPYC 9V74, five visible logical CPUs, a four-CPU cgroup quota, and a 16 GiB memory limit. The harness pins the runner and its children to one allowed CPU. Native Lean 4.36.0 compiled generated C with Clang `-O3 -DNDEBUG`. Rust 1.100.0 used Cargo release mode. The benchmark uses files of approximately 16 KiB, 1.53 MiB, and 15.26 MiB. These span different working-set sizes without establishing an out-of-cache or cold-storage regime.

Each query batch uses deterministic pregenerated inputs. Point and short-range batches have 20,000 queries. Long-range batches have 400 queries. Widths are 8 and 4096 key units, respectively, on data with a stride of two. Encoding and decoding consume a new output per repetition. Validation uses an in-memory block. Load reads a file and validates it with the OS page cache warm. The process-level wall column includes startup, initial validation, warm-up, all trials, and output. Linux `VmHWM` is measured by the child executable and repeated across its trial rows.

The raw data contains 630 timed samples. The summary includes per-batch minima and maxima, medians, throughput, and time ratios. Individual query p50/p95/p99, allocator event counts, hardware counters, and cold I/O are unmeasured. Some max times are several times the median. Small differences among the Lean reader variants are inconclusive in this VM. Sizes and workloads should be rerun on controlled hardware before making throughput targets.

### Code generation findings

Inspection of generated `Block.c` shows the Lean native decode path boxing two `UInt64` values and allocating a pair constructor before pushing the pair into the generic array. Rust materializes two inline 64-bit words per tuple. That representation difference and the higher Lean RSS are consistent with significant allocation overhead. The experiment does not attribute a measured percentage of the gap to individual allocations.

The Lean search loop still dispatches the predicate through `lean_apply_1`, uses runtime `Nat` operations for midpoint arithmetic, and assembles fixed-width words from individual byte loads. The optimized reader changes per-byte bounds handling but still assembles eight byte loads. The encoding improvement isolates the work removed by explicitly unrolling the append loop because the benchmark materializes input records before starting the timer. `perf` and Valgrind were unavailable. Inspect the generated C locally after building.

```sh
rg -n 'lean_box_uint64|lean_alloc_ctor|lean_apply_1|lean_byte_array_(get|fget)' lean/.lake/build/ir/Alvoki/Codec/Block.c
rg -- '-O3' lean/.lake/build/ir/Alvoki/Codec/Block.c.o.export.trace
```

The later optimization suite isolated these costs with fixed-width loads, scalar-field records, streaming decode, and specialized search. [Optimization results](../experiments/optimizations.md)

### Code size and tool timings

Counts below exclude blank and comment-only lines. Lean proof lines include lemma statements and proof scripts. Verus specification lines count function contracts and spec definitions, with loop invariants and instantiation hints counted as proof. Executable counts the implementation file for Rust and Lean and excludes module wrappers for Verus.

| Source | Executable core | Specification | Proof and lemma lines | CLI |
|---|---:|---:|---:|---:|
| Rust packed block | 77 | 0 | 0 | 58 |
| Lean packed block | 85 | 4 | 165 | 46 |
| Verus sorted-key core | 28 | 22 | 17 | 0 |

The shared Python correctness code has 35 lines in the oracle and 18 lines in fixture generation, which the benchmark also uses. Lean's axiom audit adds eight lines. The Lean and Verus proof sizes cover different obligations, and the experiment did not track engineer-hours.

After cleaning the build outputs, Rust release compilation took 0.456 s and the Lean native build took 2.748 s. Building Lean's proof module with the executable dependency already built took 2.040 s. Rechecking the module with `leanchecker` took 1.706 s. Verus took 1.175 s and reported four verified and zero errors.

The archived logs preserve the paths recorded at the time of each run. The current reproduction examples write fresh samples to `/tmp`. [Reproduction commands](../../README.md#reproduce-on-linux-x86-64)

- [Raw observations](../../benchmarks/results/packed/baseline/results-cloud.csv)
- [Derived summary](../../benchmarks/results/packed/baseline/summary-cloud.csv)
- [Environment](../../benchmarks/results/packed/baseline/environment-cloud.txt)
- [Build and verification log](../../benchmarks/results/packed/baseline/reproduction-cloud.txt)

## Review follow-up measurements

### Stock Lean comparison

The paired run used one million records, the same inputs for each build, 12 process rounds per build in randomized order on one pinned CPU, and three retained trials per process. Medians are in milliseconds. The baseline was `b6b4f2e8ba31e20f45adbc2981b041879d40c050` and the candidate was `e454631a5069e4b7e0554abb483544f391fa5e50`. The environment file records the pinned toolchains. [Paired trials](../../benchmarks/review-follow-up/paired-trials.csv) · [Environment](../../benchmarks/review-follow-up/environment.txt)

| Workload | Before | After |
|---|---:|---:|
| Validate interleaved | 0.447 | 0.281 |
| Validate columnar | 0.443 | 0.277 |
| Adaptive merge, alternating | 8.273 | 8.032 |
| Adaptive merge, clustered | 1.326 | 1.383 |
| Adaptive merge, update-heavy | 5.541 | 5.273 |
| Direct scan, alternating | 2.158 | 2.024 |
| Direct scan, shuffled | 6.256 | 5.985 |

The validator change carried a byte cursor and a proof that it matches the logical record index. The generated loop advances the cursor by adding the stride and uses a proved extent for the wide load. The paired merge and scan medians changed by at most 6.2% in either direction on this VM. The single-run packed scan still generates vector instructions. [Validator on the measured candidate](https://github.com/alvoki/alvoki-lean/blob/e454631a5069e4b7e0554abb483544f391fa5e50/lean/PackedView.lean) · [Paired trials](../../benchmarks/review-follow-up/paired-trials.csv)

### Matched Rust span control

The fused suite included a Rust emitter with the same eight-record probe, 256-record window, and right-biased merge policy as the stock Lean fused emitter. The Rust implementation uses safe slice copies. At one million inputs, the clustered merge took 0.98 ms in fused Lean and 0.89 ms in Rust with spans. The clustered merge–validate–scan–lookup pipeline took 5.15 and 5.56 ms. The fastest Rust variants for alternating and shuffled inputs used per-record emission. [Rust span emitter](../../rust/src/bin/alvoki-merge-phases.rs) · [Fused trials](../../benchmarks/review-follow-up/fused-merge-trials.csv)

### Reproduce the measured revisions

From the repository root, bootstrap the pinned toolchain before extracting the two revisions. The candidate's five release runs also build the native binaries used by the paired comparison.

```sh
export ALVOKI_TOOLCHAINS="$(realpath "${ALVOKI_TOOLCHAINS:-../work/toolchains}")"
before=$(mktemp -d)
after=$(mktemp -d)
git archive b6b4f2e8ba31e20f45adbc2981b041879d40c050 | tar -x -C "$before"
git archive e454631a5069e4b7e0554abb483544f391fa5e50 | tar -x -C "$after"
for suite in fused-merge optimize native; do
  (cd "$before" && bash "scripts/$suite.sh")
done
(
  cd "$after"
  bash scripts/check.sh
  bash scripts/check.sh --runtime
  for suite in fused-merge optimize native merge-phases stock-builder; do
    bash "scripts/$suite.sh" --out "/tmp/alvoki-$suite-trials.csv" --sizes 1000000 --trials 9
  done
  python3 benchmarks/compare_stock.py --baseline-bin "$before/lean/.lake/build/bin" \
    --out /tmp/alvoki-paired-trials.csv
)
```

The release runs use deterministic fixtures, one pinned CPU, one warm-up per process, and nine retained trials. The paired comparison uses three retained trials per process over twelve rounds. [Optimization trials](../../benchmarks/review-follow-up/optimize-trials.csv) · [Native trials](../../benchmarks/review-follow-up/native-trials.csv) · [Merge phases](../../benchmarks/review-follow-up/merge-phases-trials.csv) · [Stock builder trials](../../benchmarks/review-follow-up/stock-builder-trials.csv)
