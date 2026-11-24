# Benchmarks

## Packed storage experiments

The reports give workload definitions, release commands, raw trials, and proof scope. Compare each result with controls from its original run.

| Workload | Reports |
|---|---|
| Point lookup, scans, layout and scalar records | [Optimization results](optimizations.md) · [Native SIMD](native-experiments.md) · [Packed ownership](packed-experiments.md) |
| Merge, replay and packed transforms | [Emission and updates](emission-experiments.md) · [Selection and replay phases](merge-phases.md) · [Fused emission and direct scans](fused-merge.md) · [Proved fast paths](fast-path-refinement.md) |
| Output builders and toolchain changes | [Fixed-width copy](fixed-copy.md) · [Stock builder](stock-builder.md) · [Scoped runtime experiment](scoped-builder.md) · [Wide-accessor ablation](../benchmarks/results/packed/wide-accessors) |
| Versioned compaction and materialization | [V3 compaction](compaction.md) · [Stock cursor](../benchmarks/results/packed/stock-v3-cursor) · [Whole-loop writer comparison](../benchmarks/results/packed/v3-writer-comparison) |

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
rg -n 'lean_box_uint64|lean_alloc_ctor|lean_apply_1|lean_byte_array_(get|fget)' lean/.lake/build/ir/Block.c
rg -- '-O3' lean/.lake/build/ir/Block.c.o.export.trace
```

The later optimization suite isolated these costs with fixed-width loads, scalar-field records, streaming decode, and specialized search. [Optimization results](optimizations.md)

### Code size and tool timings

Counts below exclude blank and comment-only lines. Lean proof lines include lemma statements and proof scripts. Verus specification lines count function contracts and spec definitions, with loop invariants and instantiation hints counted as proof. Executable counts the implementation file for Rust and Lean and excludes module wrappers for Verus.

| Source | Executable core | Specification | Proof and lemma lines | CLI |
|---|---:|---:|---:|---:|
| Rust packed block | 77 | 0 | 0 | 58 |
| Lean packed block | 85 | 4 | 165 | 46 |
| Verus sorted-key core | 28 | 22 | 17 | 0 |

The shared Python correctness code has 35 lines in the oracle and 18 lines in fixture generation, which the benchmark also uses. Lean's axiom audit adds eight lines. The Lean and Verus proof sizes cover different obligations, and the experiment did not track engineer-hours.

After cleaning the build outputs, Rust release compilation took 0.456 s and the Lean native build took 2.748 s. Building Lean's proof module with the executable dependency already built took 2.040 s. Rechecking the module with `leanchecker` took 1.706 s. Verus took 1.175 s and reported four verified and zero errors.

The archived logs preserve the paths recorded at the time of each run. The current reproduction examples write fresh samples to `/tmp`. [Reproduction commands](../README.md#reproduce-on-linux-x86-64)

- [Raw observations](../benchmarks/results/packed/baseline/results-cloud.csv)
- [Derived summary](../benchmarks/results/packed/baseline/summary-cloud.csv)
- [Environment](../benchmarks/results/packed/baseline/environment-cloud.txt)
- [Build and verification log](../benchmarks/results/packed/baseline/reproduction-cloud.txt)

## Disk replay

`scripts/disk-replay.sh` measures native `DiskTable.open` with a marked WAL and no checkpoint. The workloads write the same keys and values in ascending, descending, or deterministically shuffled order. Before timing, the Python driver independently generates the WAL frames and a commit marker covering the complete frames. The Lean executable validates the entire recovered key range on the untimed warmup and checks the recovered watermark on every sample.

Each sample times the whole open, including lock acquisition, file reads, frame validation, replay, and the durability operations required to return a handle. The timer excludes fixture generation, process startup, validation of the returned snapshot, and close. The warmup makes this a warm-cache measurement. The driver pins itself and its child to one CPU and records the raw samples in CSV. Use the same machine, sizes, and storage setup for baseline comparisons.

```sh
bash scripts/disk-replay.sh --out /tmp/alvoki-replay-before.csv
bash scripts/disk-replay.sh --out /tmp/alvoki-replay-after.csv \
  --baseline /tmp/alvoki-replay-before.csv --max-slowdown 1.25
```

`--sizes` selects the row counts and `--trials` sets the timed samples per case. The default runs 5,000, 10,000, and 20,000 rows with five samples each. `--baseline` compares medians case by case, and `--max-slowdown` is an optional local failure threshold. Compare runs with the same durability protocol and workload settings. The table below records the original replay baseline, before the durable-marker protocol. [Raw reference run](../benchmarks/results/disk/disk-replay-trials.csv) · [Environment](../benchmarks/results/disk/disk-replay-environment.txt)

| Records | Ascending median | Descending median | Shuffled median |
|---:|---:|---:|---:|
| 5,000 | 79.7 ms | 1.16 ms | 42.6 ms |
| 10,000 | 329 ms | 2.59 ms | 174 ms |
| 20,000 | 1,328 ms | 4.89 ms | 857 ms |

Ascending insertion traverses the sorted memtable on every replayed record, so doubling the row count roughly quadruples time. Descending insertion adds each key at the front and takes roughly linear time. These timings establish the baseline for replacing the memtable. [Current insertion](../lean/Alvoki/Storage/Table/PackedTable.lean)

### Canonical database path at open

We measured the directory-identity change on the same Linux VM using seven release trials for each of 100, 5,000, and 10,000 records in all three replay orders. The median ratios after the change ranged from 0.84× to 1.08× at 5,000 and 10,000 records. At 100 records the shuffled median rose from 39.6 to 48.0 microseconds and the other two medians moved by less than one microsecond. The comparison uses one run per build. Native code performs `realpath` and the absolute-path check once on open, and the path proof is erased. [Before samples](../benchmarks/results/disk/disk-identity-before.csv) · [After samples](../benchmarks/results/disk/disk-identity-after.csv) · [Environment and command](../benchmarks/results/disk/disk-identity-environment.txt)

### WAL sync on successful reopen

The same-machine comparison uses seven release trials at each size and order. For 100 records, the median ranged from 29 to 49 microseconds before the fix and from 0.97 to 1.21 milliseconds after it. For 10,000 descending records it rose from 2.50 to 3.82 milliseconds, and for ascending records from 326 to 330 milliseconds. An aligned reopen invokes one GNU `sync` process for the WAL and directory. The benchmark includes that operation and replay. Retain these results as a reference for work on the durability barrier and the memtable. [Before samples](../benchmarks/results/disk/disk-reopen-before.csv) · [After samples](../benchmarks/results/disk/disk-reopen-after.csv) · [Environment and command](../benchmarks/results/disk/disk-reopen-environment.txt)

### Torn WAL repair

Use `bash scripts/disk-replay.sh --repair-tail --out /tmp/alvoki-tail-repair.csv` to measure reopen with an incomplete frame outside the marker-selected prefix. Each trial reinstalls the same WAL bytes outside the timer and verifies that open trimmed the tail. The timed work includes replay, staged file write and sync, rename, and directory sync.

We used seven trials per size and order to compare the shared replacement sequence with the previous inline sequence. Median ratios were 0.92× to 1.00× at 5,000 and 10,000 records and 0.85× to 1.17× at 100 records. These runs measure the full tail-repair path. [Before samples](../benchmarks/results/disk/disk-publication-before.csv) · [After samples](../benchmarks/results/disk/disk-publication-after.csv) · [Environment and command](../benchmarks/results/disk/disk-publication-environment.txt)

### Durable WAL boundary

`bash scripts/disk-write.sh 64 7` measures consecutive acknowledged writes in a fresh database. It excludes opening the database, checking the result, and closing. Seven same-machine release trials give a median of 1.28 ms per write before the durable marker and 3.11 ms per write after it. Publication groups the WAL and staged marker file syncs in one process and uses a second invocation for the directory after rename. A future durable batch can amortize publication across several writes. [Write samples before](../benchmarks/results/disk/disk-boundary-write-before.csv) · [Write samples after](../benchmarks/results/disk/disk-boundary-write-after.csv) · [Environment and commands](../benchmarks/results/disk/disk-boundary-environment.txt)

Warm-cache reopen medians ranged from 0.92× to 1.10× across the same-machine WAL-only workload matrix. The aligned selector reuses the original byte array. [Reopen samples before](../benchmarks/results/disk/disk-boundary-replay-before.csv) · [Reopen samples after](../benchmarks/results/disk/disk-boundary-replay-after.csv)

### Shared checkpoint publication schedule

`bash scripts/disk-checkpoint.sh 4 128 7` measures checkpoint publication starting from an installed run set. Generation setup, open, and post-checkpoint reopen and read checks are outside the timer. For one, four, and sixteen runs of 128 rows, the same-machine medians were 5.91, 9.91, and 28.70 ms before switching to the shared schedule and 5.51, 10.13, and 27.58 ms afterward. Both implementations issue the same file syncs, directory barriers, and rename. [Before samples](../benchmarks/results/disk/disk-checkpoint-before.csv) · [After samples](../benchmarks/results/disk/disk-checkpoint-after.csv) · [Environment and command](../benchmarks/results/disk/disk-checkpoint-environment.txt)

Add `--reopen` to time `DiskTable.open` with an installed run set and a WAL fully covered by the checkpoint. The harness seeds a v2 manifest and checks its generation, run count, and WAL watermark before timing, then verifies recovered rows after each trial.

### Shared reopen durability branch

The native adapter and proof use the same decision between staged tail repair and a grouped sync of the already aligned WAL and directory. On the same VM and CPU, 14 interleaved pairs per workload timed a marked WAL with 32 or 2,048 records in each branch. Median paired ratios ranged from 0.992× to 1.031× in the first run and 0.947× to 1.053× when reproducing the experiment with the same binaries. Generated C inlines branch selection and calls the existing replacement and sync paths. [Raw samples, driver and environment](../benchmarks/results/disk/shared-reopen)

### Shared checkpoint preparation

The native publication benchmark with four installed runs of 32 rows measured pooled medians of 10.067 ms before sharing the flush decision and 10.032 ms after it. The median paired ratio was 0.996× across 12 pairs. The emitted `DiskTable.checkpoint` body, including the pending-row branch, is identical after normalizing generated names. [Raw samples and reproduction](../benchmarks/results/disk/shared-checkpoint-preparation)

### Typed disk write outcomes

The existing `DiskTable.write` path measured 3.158 ms per acknowledged write before the typed outcome API and 3.089 ms after it. The median paired ratio was 1.001× across 14 samples of 64 writes per build. Generated C for `write` differs in generated names. Both bodies use the same state transitions and durability calls. [Samples and reproduction](../benchmarks/results/disk/typed-write-outcomes)

### Shared marked open

The shared checkpoint loader and marked WAL replay were measured with 14 interleaved pairs per workload. The median paired candidate-to-baseline ratios were 0.985× to 1.026× for marked WALs with 32 or 2,048 records, covering aligned and repaired WALs. Reopen with four runs of 32 rows measured 0.984× and with 32 runs of 128 rows measured 0.977×. Repeating the two checkpoint workloads gave 0.968× and 1.036×. The generated C retains the checkpoint read loop and inlines the durability callbacks. [Samples and reproduction](../benchmarks/results/disk/shared-marked-open)

Sharing the optional marker and WAL reads gave pooled median paired ratios of 0.953× to 1.014× over the four marked WAL cases and two checkpoint cases. The A/A control ranged from 0.946× to 1.039×. The generated code inlines the read schedule with the same number of allocation sites and primitive calls. [Cohorts, control and reproduction](../benchmarks/results/disk/shared-open-wal-reads)

### Shared publication file and sync targets

The shared dispatcher passes the exact native write, grouped sync, rename and directory sync targets to the adapter callbacks. Generated C inlines the dispatch. Native measurements comparing this refactor gave median paired ratios of 0.999× for write, 1.012× for checkpoint and 0.992× to 1.038× across four reopen workloads. Both builds use the same acknowledgement barriers. [Raw samples, driver and environment](../benchmarks/results/disk/shared-publication-effects)

### Selected WAL frame ordinals

Seven interleaved native release trials per build timed `DiskTable.open` on a warm cache, pinned to CPU 4. The checkpointed fixtures held a single run and a WAL fully covered by the checkpoint. The log-only fixture used descending keys. Ordinal validation runs during decoding and adds no sync calls. Checkpointed reopen medians stayed within 2% of baseline across the measured sizes. [Raw samples](../benchmarks/results/disk/ordinals/replay-ordinals-trials.csv) · [Environment](../benchmarks/results/disk/ordinals/replay-ordinals-environment.txt)

| Workload | WAL frames | Baseline median | Checked median |
|---|---:|---:|---:|
| Checkpointed | 2,000 | 1.772 ms | 1.742 ms |
| Checkpointed | 20,000 | 7.252 ms | 7.347 ms |
| Checkpointed | 50,000 | 16.891 ms | 16.577 ms |
| Log only | 20,000 | 6.395 ms | 6.196 ms |

### Disk snapshot session identity

The disk read guard compares the handle's session token with the database's token before accessing the pin. Each native trial opens one checkpoint with a 256-row run, acquires a pin and warms both loops before timing. The loops perform 1,048,576 point reads and 131,072 eight-row ranges. The harness sums payloads and checks the totals after timing. Each core ran 14 pairs, alternating build order. The first run on CPU 4 had more variable elapsed times than the rerun on CPU 1. [Raw samples, harness and reproduction](../benchmarks/results/disk/session-handles)

| Core | Read | Baseline median | Checked median | Median paired ratio |
|---|---|---:|---:|---:|
| 1 | Point | 116.17 ns | 116.50 ns | 1.028× |
| 1 | Eight-row range | 592.64 ns | 604.31 ns | 1.024× |
| 4 | Point | 111.18 ns | 131.99 ns | 1.128× |
| 4 | Eight-row range | 609.49 ns | 888.49 ns | 1.101× |

### WAL sync process overhead

In an interleaved native experiment with seven 64-write trials per mode, the old one-sync control took 1.17 ms per write and the durable-boundary reference took 2.58 ms per write. Lean launching and waiting for `/usr/bin/true` took 0.69 ms. This identifies process startup as a substantial part of the regression. A native control measured 0.63 ms for staging, all three sync calls, and rename without per-write process startup.

| Mode | Median write time |
|---|---:|
| Current GNU `sync` protocol | 2.58 ms |
| GNU `sync` with only stderr captured | 2.49 ms |
| One Rust sync helper per write | 1.79 ms |
| Persistent Rust sync helper per open | 0.72 ms |

Both helper prototypes leave rename in the Lean process under the database lock, sync the files before rename, and report directory sync success before acknowledgement. Both passed the scratch fixtures for a successful write, file sync failure, directory sync failure, and helper death. The experiment also provides a direct-rename control. That control can outlive the lock holder and is unsuitable for the adapter. These are experimental results on one VM. [Reproduction and raw samples](../benchmarks/wal-sync-experiment)

### Lean readability review

The checkpoint loader cleanup uses Lean's `IO.ofExcept` and constructs an installed state after WAL recovery. Acknowledged writes measured 3.20 ms before and 3.13 ms after. Reopen medians ranged from 0.93× to 1.03× over the same-machine WAL workload matrix. The initial four-run checkpoint medians were 9.24 and 10.29 ms. In a follow-up with 12 interleaved rounds of three samples per build, the pooled medians were 11.47 and 11.47 ms, with a median paired ratio of 1.012×. [Raw samples and environment](../benchmarks/results/disk/readability)

## Review follow-up measurements

### Stock Lean comparison

The paired run used one million records, the same inputs for each build, 12 process rounds per build in randomized order on one pinned CPU, and three retained trials per process. Medians are in milliseconds. The baseline was `b6b4f2e8ba31e20f45adbc2981b041879d40c050` and the candidate was `e454631a5069e4b7e0554abb483544f391fa5e50`. The environment file records the pinned toolchains. [Paired trials](../benchmarks/review-follow-up/paired-trials.csv) · [Environment](../benchmarks/review-follow-up/environment.txt)

| Workload | Before | After |
|---|---:|---:|
| Validate interleaved | 0.447 | 0.281 |
| Validate columnar | 0.443 | 0.277 |
| Adaptive merge, alternating | 8.273 | 8.032 |
| Adaptive merge, clustered | 1.326 | 1.383 |
| Adaptive merge, update-heavy | 5.541 | 5.273 |
| Direct scan, alternating | 2.158 | 2.024 |
| Direct scan, shuffled | 6.256 | 5.985 |

The validator change carried a byte cursor and a proof that it matches the logical record index. The generated loop advances the cursor by adding the stride and uses a proved extent for the wide load. The paired merge and scan medians changed by at most 6.2% in either direction on this VM. The single-run packed scan still generates vector instructions. [Validator on the measured candidate](https://github.com/alvoki/alvoki-lean/blob/e454631a5069e4b7e0554abb483544f391fa5e50/lean/PackedView.lean) · [Paired trials](../benchmarks/review-follow-up/paired-trials.csv)

### Matched Rust span control

The fused suite included a Rust emitter with the same eight-record probe, 256-record window, and right-biased merge policy as the stock Lean fused emitter. The Rust implementation uses safe slice copies. At one million inputs, the clustered merge took 0.98 ms in fused Lean and 0.89 ms in Rust with spans. The clustered merge–validate–scan–lookup pipeline took 5.15 and 5.56 ms. The fastest Rust variants for alternating and shuffled inputs used per-record emission. [Rust span emitter](../rust/src/bin/alvoki-merge-phases.rs) · [Fused trials](../benchmarks/review-follow-up/fused-merge-trials.csv)

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

The release runs use deterministic fixtures, one pinned CPU, one warm-up per process, and nine retained trials. The paired comparison uses three retained trials per process over twelve rounds. [Optimization trials](../benchmarks/review-follow-up/optimize-trials.csv) · [Native trials](../benchmarks/review-follow-up/native-trials.csv) · [Merge phases](../benchmarks/review-follow-up/merge-phases-trials.csv) · [Stock builder trials](../benchmarks/review-follow-up/stock-builder-trials.csv)
