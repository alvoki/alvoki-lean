# First VM measurements

The first experiment supports further investigation of Lean's verification and packed search. It exposes much larger costs in whole-block validation and materialized decoding than in random lookups. Encoding improved when the Lean byte append loop was unrolled. A single extent check in place of eight checked reads did not consistently speed up packed query workloads.

## One million records

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

## Method

The KVM guest reports AMD EPYC 9V74, five visible logical CPUs, a four-CPU cgroup quota, and a 16 GiB memory limit. The harness pins the runner and its children to one allowed CPU. Native Lean 4.36.0 compiled generated C with Clang `-O3 -DNDEBUG`. Rust 1.100.0 used Cargo release mode. The benchmark uses files of approximately 16 KiB, 1.53 MiB, and 15.26 MiB. These span different working-set sizes without establishing an out-of-cache or cold-storage regime.

Each query batch uses deterministic pregenerated inputs. Point and short-range batches have 20,000 queries. Long-range batches have 400 queries. Widths are 8 and 4096 key units, respectively, on data with a stride of two. Encoding and decoding consume a new output per repetition. Validation uses an in-memory block. Load reads a file and validates it with the OS page cache warm. The process-level wall column includes startup, initial validation, warm-up, all trials, and output. Linux `VmHWM` is measured by the child executable and repeated across its trial rows.

The raw data contains 630 timed samples. The summary includes per-batch minima and maxima, medians, throughput, and time ratios. Individual query p50/p95/p99, allocator event counts, hardware counters, and cold I/O are unmeasured. Some max times are several times the median. Small differences among the Lean reader variants are inconclusive in this VM. Sizes and workloads should be rerun on controlled hardware before making throughput targets.

## Code generation findings

Inspection of generated `Block.c` shows the Lean native decode path boxing two `UInt64` values and allocating a pair constructor before pushing the pair into the generic array. Rust materializes two inline 64-bit words per tuple. That representation difference and the higher Lean RSS are consistent with significant allocation overhead. The experiment does not attribute a measured percentage of the gap to individual allocations.

The Lean search loop still dispatches the predicate through `lean_apply_1`, uses runtime `Nat` operations for midpoint arithmetic, and assembles fixed-width words from individual byte loads. The optimized reader changes per-byte bounds handling but still assembles eight byte loads. The encoding improvement isolates the work removed by explicitly unrolling the append loop because the benchmark materializes input records before starting the timer. `perf` and Valgrind were unavailable. Inspect the generated C locally after building.

```sh
rg -n 'lean_box_uint64|lean_alloc_ctor|lean_apply_1|lean_byte_array_(get|fget)' lean/.lake/build/ir/Block.c
rg -- '-O3' lean/.lake/build/ir/Block.c.o.export.trace
```

A focused follow-up should isolate native fixed-width word loads, compare a scalar-field Lean record with boxed pairs and streaming decode, then test whether a specialized search loop can remove the per-probe callback and use fixed-width indices. Establish proof obligations for the representation changes alongside those experiments.

## Code size and tool timings

Counts below exclude blank and comment-only lines. Lean proof lines include lemma statements and proof scripts. Verus specification lines count function contracts and spec definitions, with loop invariants and instantiation hints counted as proof. Executable counts the implementation file for Rust and Lean and excludes module wrappers for Verus.

| Source | Executable core | Specification | Proof and lemma lines | CLI |
|---|---:|---:|---:|---:|
| Rust packed block | 77 | 0 | 0 | 58 |
| Lean packed block | 85 | 4 | 165 | 46 |
| Verus sorted-key core | 28 | 22 | 17 | 0 |

The shared Python correctness code has 35 lines in the oracle and 18 lines in fixture generation, which the benchmark also uses. Lean's axiom audit adds eight lines. The Lean and Verus proof sizes cover different obligations, and the experiment did not track engineer-hours.

After cleaning the build outputs, Rust release compilation took 0.456 s and the Lean native build took 2.748 s. Building Lean's proof module with the executable dependency already built took 2.040 s. Rechecking the module with `leanchecker` took 1.706 s. Verus took 1.175 s and reported four verified and zero errors. See the raw run logs for the commands and tool output.

- [Raw observations](../benchmarks/results-cloud.csv)
- [Derived summary](../benchmarks/summary-cloud.csv)
- [Environment](../benchmarks/environment-cloud.txt)
- [Build and verification log](../benchmarks/reproduction-cloud.txt)

## Disk replay

`scripts/disk-replay.sh` measures native `DiskTable.open` on a database with only a WAL. All three workloads write the same set of keys and values in ascending, descending, or deterministically shuffled order. The independent Python driver generates the WAL frames before timing. The Lean executable validates the entire recovered key range on the untimed warmup and checks the recovered watermark on every sample.

Each sample measures lock acquisition, WAL file loading, decoding, and replay. It excludes fixture generation, process startup, validation, and close. The warmup makes this a warm-cache measurement. The driver pins itself and its child to one CPU and records the raw samples in CSV. Use the same machine, sizes, and storage setup for baseline comparisons.

```sh
bash scripts/disk-replay.sh --out /tmp/alvoki-replay-before.csv
bash scripts/disk-replay.sh --out /tmp/alvoki-replay-after.csv \
  --baseline /tmp/alvoki-replay-before.csv --max-slowdown 1.25
```

`--sizes` selects the row counts and `--trials` sets the timed samples per case. The default runs 5,000, 10,000, and 20,000 rows with five samples each. `--baseline` compares medians case by case, and `--max-slowdown` is an optional local failure threshold. [Raw reference run](../benchmarks/results/disk/disk-replay-trials.csv) · [Environment](../benchmarks/results/disk/disk-replay-environment.txt)

| Records | Ascending median | Descending median | Shuffled median |
|---:|---:|---:|---:|
| 5,000 | 79.7 ms | 1.16 ms | 42.6 ms |
| 10,000 | 329 ms | 2.59 ms | 174 ms |
| 20,000 | 1,328 ms | 4.89 ms | 857 ms |

Ascending insertion traverses the sorted memtable on every replayed record, so doubling the row count roughly quadruples time. Descending insertion adds each key at the front and takes roughly linear time. These timings establish the baseline for replacing the memtable. [Current insertion](../lean/storage/table/PackedTable.lean)

### Canonical database path at open

We measured the directory-identity change on the same Linux VM using seven release trials for each of 100, 5,000, and 10,000 records in all three replay orders. The median ratios after the change ranged from 0.84× to 1.08× at 5,000 and 10,000 records. At 100 records the shuffled median rose from 39.6 to 48.0 microseconds and the other two medians moved by less than one microsecond. The comparison uses one run per build. Native code performs `realpath` and the absolute-path check once on open, and the path proof is erased. [Before samples](../benchmarks/results/disk/disk-identity-before.csv) · [After samples](../benchmarks/results/disk/disk-identity-after.csv) · [Environment and command](../benchmarks/results/disk/disk-identity-environment.txt)

### WAL sync on successful reopen

The same-machine comparison uses seven release trials at each size and order. For 100 records, the median ranged from 29 to 49 microseconds before the fix and from 0.97 to 1.21 milliseconds after it. For 10,000 descending records it rose from 2.50 to 3.82 milliseconds, and for ascending records from 326 to 330 milliseconds. An aligned reopen invokes one GNU `sync` process for the WAL and directory. The benchmark includes that operation and replay. Retain these results as a reference for work on the durability barrier and the memtable. [Before samples](../benchmarks/results/disk/disk-reopen-before.csv) · [After samples](../benchmarks/results/disk/disk-reopen-after.csv) · [Environment and command](../benchmarks/results/disk/disk-reopen-environment.txt)

### Torn WAL repair

Use `bash scripts/disk-replay.sh --repair-tail --out /tmp/alvoki-tail-repair.csv` to measure reopen with an incomplete final frame. Each trial reinstalls the same independent WAL fixture outside the timer and verifies that open trimmed the tail. The timed work includes replay, staged file write and sync, rename, and directory sync.

We used seven trials per size and order to compare the shared replacement sequence with the previous inline sequence. Median ratios were 0.92× to 1.00× at 5,000 and 10,000 records and 0.85× to 1.17× at 100 records. These runs measure the full tail-repair path. [Before samples](../benchmarks/results/disk/disk-publication-before.csv) · [After samples](../benchmarks/results/disk/disk-publication-after.csv) · [Environment and command](../benchmarks/results/disk/disk-publication-environment.txt)

### Durable WAL boundary

`bash scripts/disk-write.sh 64 7` measures consecutive acknowledged writes in a fresh database. It excludes opening the database, checking the result, and closing. Seven same-machine release trials give a median of 1.28 ms per write before the durable marker and 3.11 ms per write after it. Publication groups the WAL and staged marker file syncs in one process and uses a second invocation for the directory after rename. A future durable batch can amortize publication across several writes. [Write samples before](../benchmarks/results/disk/disk-boundary-write-before.csv) · [Write samples after](../benchmarks/results/disk/disk-boundary-write-after.csv) · [Environment and commands](../benchmarks/results/disk/disk-boundary-environment.txt)

Warm-cache reopen medians ranged from 0.92× to 1.10× across the same-machine WAL-only workload matrix. The aligned selector reuses the original byte array. [Reopen samples before](../benchmarks/results/disk/disk-boundary-replay-before.csv) · [Reopen samples after](../benchmarks/results/disk/disk-boundary-replay-after.csv)

### Shared checkpoint publication schedule

`bash scripts/disk-checkpoint.sh 4 128 7` measures checkpoint publication starting from an installed run set. Generation setup, open, and post-checkpoint reopen and read checks are outside the timer. For one, four, and sixteen runs of 128 rows, the same-machine medians were 5.91, 9.91, and 28.70 ms before switching to the shared schedule and 5.51, 10.13, and 27.58 ms afterward. Both implementations issue the same file syncs, directory barriers, and rename. [Before samples](../benchmarks/results/disk/disk-checkpoint-before.csv) · [After samples](../benchmarks/results/disk/disk-checkpoint-after.csv) · [Environment and command](../benchmarks/results/disk/disk-checkpoint-environment.txt)

Add `--reopen` to time `DiskTable.open` with an installed run set and a WAL fully covered by the checkpoint. The harness checks the manifest's generation, run count, and WAL watermark before timing, then verifies recovered rows after each trial.

### Selected WAL frame ordinals

Seven interleaved native release trials per build timed `DiskTable.open` on a warm cache, pinned to CPU 4. The checkpointed fixtures held a single run and a WAL fully covered by the checkpoint. The log-only fixture used descending keys. Ordinal validation runs during decoding and adds no sync calls. Checkpointed reopen medians stayed within 2% of baseline across the measured sizes. [Raw samples](../benchmarks/results/disk/ordinals/replay-ordinals-trials.csv) · [Environment](../benchmarks/results/disk/ordinals/replay-ordinals-environment.txt)

| Workload | WAL frames | Baseline median | Checked median |
|---|---:|---:|---:|
| Checkpointed | 2,000 | 1.772 ms | 1.742 ms |
| Checkpointed | 20,000 | 7.252 ms | 7.347 ms |
| Checkpointed | 50,000 | 16.891 ms | 16.577 ms |
| Log only | 20,000 | 6.395 ms | 6.196 ms |

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
