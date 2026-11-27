# Disk benchmark history

## Disk replay

`scripts/disk-replay.sh` measures native `DiskTable.open` with marked WAL segments and no checkpoint. The workloads write the same keys and values in ascending, descending, or deterministically shuffled order. Before timing, the Python driver independently generates the WAL frames and a commit marker covering the complete frames. The Lean executable validates the entire recovered key range on the untimed warmup and checks the recovered watermark on every sample.

Each sample times the whole open, including lock acquisition, file reads, frame validation, replay, and the durability operations required to return a handle. The timer excludes fixture generation, process startup, validation of the returned snapshot, and close. The warmup makes this a warm-cache measurement. The driver pins itself and its child to one CPU and records the raw samples in CSV. Use the same machine, sizes, and storage setup for baseline comparisons.

```sh
bash scripts/disk-replay.sh --out /tmp/alvoki-replay-before.csv
bash scripts/disk-replay.sh --out /tmp/alvoki-replay-after.csv \
  --baseline /tmp/alvoki-replay-before.csv --max-slowdown 1.25
```

`--sizes` selects the row counts and `--trials` sets the timed samples per case. The default runs 5,000, 10,000, and 20,000 rows with five samples each. `--baseline` compares medians case by case, and `--max-slowdown` is an optional local failure threshold. Compare runs with the same durability protocol and workload settings. The table below records the original replay baseline, before the durable-marker protocol. [Raw reference run](../../benchmarks/results/disk/disk-replay-trials.csv) · [Environment](../../benchmarks/results/disk/disk-replay-environment.txt)

| Records | Ascending median | Descending median | Shuffled median |
|---:|---:|---:|---:|
| 5,000 | 79.7 ms | 1.16 ms | 42.6 ms |
| 10,000 | 329 ms | 2.59 ms | 174 ms |
| 20,000 | 1,328 ms | 4.89 ms | 857 ms |

Ascending insertion traverses the sorted memtable on every replayed record, so doubling the row count roughly quadruples time. Descending insertion adds each key at the front and takes roughly linear time. These timings establish the baseline for replacing the memtable. [Current insertion](../../lean/Alvoki/Storage/Table/PackedTable.lean)

### Verified tree memtable

On the same x86-64 VM with Lean 4.36, Linux 6.18.57 and an AMD EPYC 9V74, five warm-cache trials of `scripts/disk-replay.sh --sizes 5000 10000 20000 --segments 1 --trials 5 --out /tmp/replay.csv` measured these 20,000-record reopen medians. The list build was `b7b901c`. The fixture and durability protocol were identical.

| WAL key order | List | Tree |
|---|---:|---:|
| Ascending | 1,352.29 ms | 7.90 ms |
| Descending | 5.04 ms | 8.10 ms |
| Shuffled | 904.30 ms | 10.13 ms |

Descending distinct keys use the list's constant-time prepend path. The tree uses the same ordered insert for every input order. [Tree backend](../../lean/Alvoki/Storage/Table/MemTableTree.lean)

### Native segmented WAL

Use `--segments 1 8 32` to compare segment layouts with the same frame stream. The paired release comparison against the earlier single-file adapter measured a 32-frame aligned reopen at 1.169 ms and 2.227 ms. Torn-tail reopen at that size took 2.868 ms and 5.112 ms. Acknowledged writes stayed near 3 ms per write. The segmented protocol keeps separate directory and keeper barriers for aligned open and additional barriers for repair. The measured startup cost is the tradeoff for adopting that crash-safe schedule while the full segmented trace and its durability optimizations are developed. [Raw samples, controls and reproduction](../../benchmarks/results/disk/native-segmented-wal)

### WAL reopen memory and bytes read

Build the native `alvoki-disk-replay` executable with the resource probe in each segmented checkout. The Python driver measures Linux process peak RSS immediately after one open and uses a second open under `strace` to sum bytes returned by reads of WAL segment paths. Each open starts from a fresh copy of the same marked fixture and validates the recovered rows. Read counts include userspace buffering and describe bytes returned by the kernel to the process. Use the timed replay command separately for latency. [Resource driver](../../benchmarks/disk_replay_resources.py) · [Native probe](../../lean/Alvoki/Bench/Disk/DiskReplayBench.lean)

```sh
python3 benchmarks/disk_replay_resources.py \
  --base /path/to/before/lean/.lake/build/bin/alvoki-disk-replay \
  --candidate /path/to/after/lean/.lake/build/bin/alvoki-disk-replay \
  --segments 1 8 32 --tail-bytes 0 11 8388608 33554432 \
  --out /tmp/alvoki-replay-resources.csv
```

With a 32 MiB tail, the bounded keeper requests reduced the measured WAL reads from about 33.65 MB to 98–99 kB across 1, 8 and 32 segments. Median peak RSS fell by about 34 MiB. The aligned 32-frame median moved from 2.38 to 2.32 ms on CPU 1, with an interval spanning parity. [Matched resource and timing samples](../../benchmarks/results/disk/bounded-keeper-replay)

A separate native preparation experiment processed each sealed segment as it arrived. On 600,000 frames over 32 segments, peak RSS fell from about 116 to 60 MiB. Reordering keeper extraction alone left memory use unchanged. Timings varied across runs. The production adapter continues to use the bounded vector worker while the per-segment replay proof is developed. [Per-segment experiment](../../benchmarks/results/disk/segmented-replay-lifetimes)

### Canonical database path at open

We measured the directory-identity change on the same Linux VM using seven release trials for each of 100, 5,000, and 10,000 records in all three replay orders. The median ratios after the change ranged from 0.84× to 1.08× at 5,000 and 10,000 records. At 100 records the shuffled median rose from 39.6 to 48.0 microseconds and the other two medians moved by less than one microsecond. The comparison uses one run per build. Native code performs `realpath` and the absolute-path check once on open, and the path proof is erased. [Before samples](../../benchmarks/results/disk/disk-identity-before.csv) · [After samples](../../benchmarks/results/disk/disk-identity-after.csv) · [Environment and command](../../benchmarks/results/disk/disk-identity-environment.txt)

### WAL sync on successful reopen

The same-machine comparison uses seven release trials at each size and order. For 100 records, the median ranged from 29 to 49 microseconds before the fix and from 0.97 to 1.21 milliseconds after it. For 10,000 descending records it rose from 2.50 to 3.82 milliseconds, and for ascending records from 326 to 330 milliseconds. In that single-file revision, an aligned reopen invoked one GNU `sync` process for the WAL and directory. The benchmark includes that operation and replay. Retain these results as a reference for work on the durability barrier and the memtable. [Before samples](../../benchmarks/results/disk/disk-reopen-before.csv) · [After samples](../../benchmarks/results/disk/disk-reopen-after.csv) · [Environment and command](../../benchmarks/results/disk/disk-reopen-environment.txt)

### Torn WAL repair

Use `bash scripts/disk-replay.sh --repair-tail --out /tmp/alvoki-tail-repair.csv` to measure reopen with an incomplete frame outside the marker-selected prefix. Each trial reinstalls the same WAL bytes outside the timer and verifies that open trimmed the tail. The timed work includes replay, staged file write and sync, rename, and directory sync.

We used seven trials per size and order to compare the shared replacement sequence with the previous inline sequence. Median ratios were 0.92× to 1.00× at 5,000 and 10,000 records and 0.85× to 1.17× at 100 records. These runs measure the full tail-repair path. [Before samples](../../benchmarks/results/disk/disk-publication-before.csv) · [After samples](../../benchmarks/results/disk/disk-publication-after.csv) · [Environment and command](../../benchmarks/results/disk/disk-publication-environment.txt)

### Durable WAL boundary

`bash scripts/disk-write.sh 64 7` measures consecutive acknowledged writes in a fresh database. It excludes opening the database, checking the result, and closing. Seven same-machine release trials give a median of 1.28 ms per write before the durable marker and 3.11 ms per write after it. Publication groups the WAL and staged marker file syncs in one process and uses a second invocation for the directory after rename. A future durable batch can amortize publication across several writes. [Write samples before](../../benchmarks/results/disk/disk-boundary-write-before.csv) · [Write samples after](../../benchmarks/results/disk/disk-boundary-write-after.csv) · [Environment and commands](../../benchmarks/results/disk/disk-boundary-environment.txt)

Warm-cache reopen medians ranged from 0.92× to 1.10× across the same-machine WAL-only workload matrix. The aligned selector reuses the original byte array. [Reopen samples before](../../benchmarks/results/disk/disk-boundary-replay-before.csv) · [Reopen samples after](../../benchmarks/results/disk/disk-boundary-replay-after.csv)

### Shared checkpoint publication schedule

`bash scripts/disk-checkpoint.sh 4 128 7` measures checkpoint publication starting from an installed run set. Generation setup, open, and post-checkpoint reopen and read checks are outside the timer. For one, four, and sixteen runs of 128 rows, the same-machine medians were 5.91, 9.91, and 28.70 ms before switching to the shared schedule and 5.51, 10.13, and 27.58 ms afterward. Both implementations issue the same file syncs, directory barriers, and rename. [Before samples](../../benchmarks/results/disk/disk-checkpoint-before.csv) · [After samples](../../benchmarks/results/disk/disk-checkpoint-after.csv) · [Environment and command](../../benchmarks/results/disk/disk-checkpoint-environment.txt)

Add `--reopen` to time `DiskTable.open` with an installed run set and a WAL fully covered by the checkpoint. The harness seeds a v2 manifest and checks its generation, run count, and WAL watermark before timing, then verifies recovered rows after each trial.

### Shared reopen durability branch

The native adapter and proof use the same decision between staged tail repair and a grouped sync of the already aligned WAL and directory. On the same VM and CPU, 14 interleaved pairs per workload timed a marked WAL with 32 or 2,048 records in each branch. Median paired ratios ranged from 0.992× to 1.031× in the first run and 0.947× to 1.053× when reproducing the experiment with the same binaries. Generated C inlines branch selection and calls the existing replacement and sync paths. [Raw samples, driver and environment](../../benchmarks/results/disk/shared-reopen)

### Shared checkpoint preparation

The native publication benchmark with four installed runs of 32 rows measured pooled medians of 10.067 ms before sharing the flush decision and 10.032 ms after it. The median paired ratio was 0.996× across 12 pairs. The emitted `DiskTable.checkpoint` body, including the pending-row branch, is identical after normalizing generated names. [Raw samples and reproduction](../../benchmarks/results/disk/shared-checkpoint-preparation)

### Typed disk write outcomes

The existing `DiskTable.write` path measured 3.158 ms per acknowledged write before the typed outcome API and 3.089 ms after it. The median paired ratio was 1.001× across 14 samples of 64 writes per build. Generated C for `write` differs in generated names. Both bodies use the same state transitions and durability calls. [Samples and reproduction](../../benchmarks/results/disk/typed-write-outcomes)

### Shared marked open

The shared checkpoint loader and marked WAL replay were measured with 14 interleaved pairs per workload. The median paired candidate-to-baseline ratios were 0.985× to 1.026× for marked WALs with 32 or 2,048 records, covering aligned and repaired WALs. Reopen with four runs of 32 rows measured 0.984× and with 32 runs of 128 rows measured 0.977×. Repeating the two checkpoint workloads gave 0.968× and 1.036×. The generated C retains the checkpoint read loop and inlines the durability callbacks. [Samples and reproduction](../../benchmarks/results/disk/shared-marked-open)

Sharing the optional marker and WAL reads gave pooled median paired ratios of 0.953× to 1.014× over the four marked WAL cases and two checkpoint cases. The A/A control ranged from 0.946× to 1.039×. The generated code inlines the read schedule with the same number of allocation sites and primitive calls. [Cohorts, control and reproduction](../../benchmarks/results/disk/shared-open-wal-reads)

### Shared publication file and sync targets

The shared dispatcher passes the exact native write, grouped sync, rename and directory sync targets to the adapter callbacks. Generated C inlines the dispatch. Native measurements comparing this refactor gave median paired ratios of 0.999× for write, 1.012× for checkpoint and 0.992× to 1.038× across four reopen workloads. Both builds use the same acknowledgement barriers. [Raw samples, driver and environment](../../benchmarks/results/disk/shared-publication-effects)

### Selected WAL frame ordinals

Seven interleaved native release trials per build timed `DiskTable.open` on a warm cache, pinned to CPU 4. The checkpointed fixtures held a single run and a WAL fully covered by the checkpoint. The log-only fixture used descending keys. Ordinal validation runs during decoding and adds no sync calls. Checkpointed reopen medians stayed within 2% of baseline across the measured sizes. [Raw samples](../../benchmarks/results/disk/ordinals/replay-ordinals-trials.csv) · [Environment](../../benchmarks/results/disk/ordinals/replay-ordinals-environment.txt)

| Workload | WAL frames | Baseline median | Checked median |
|---|---:|---:|---:|
| Checkpointed | 2,000 | 1.772 ms | 1.742 ms |
| Checkpointed | 20,000 | 7.252 ms | 7.347 ms |
| Checkpointed | 50,000 | 16.891 ms | 16.577 ms |
| Log only | 20,000 | 6.395 ms | 6.196 ms |

### Disk snapshot session identity

The disk read guard compares the handle's session token with the database's token before accessing the pin. Each native trial opens one checkpoint with a 256-row run, acquires a pin and warms both loops before timing. The loops perform 1,048,576 point reads and 131,072 eight-row ranges. The harness sums payloads and checks the totals after timing. Each core ran 14 pairs, alternating build order. The first run on CPU 4 had more variable elapsed times than the rerun on CPU 1. [Raw samples, harness and reproduction](../../benchmarks/results/disk/session-handles)

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
| GNU `sync` reference | 2.58 ms |
| GNU `sync` with only stderr captured | 2.49 ms |
| One Rust sync helper per write | 1.79 ms |
| Persistent Rust sync helper per open | 0.72 ms |

Both helper prototypes leave rename in the Lean process under the database lock, sync the files before rename, and report directory sync success before acknowledgement. Both passed the scratch fixtures for a successful write, file sync failure, directory sync failure, and helper death. The experiment also provides a direct-rename control. That control can outlive the lock holder and is unsuitable for the adapter. These are experimental results on one VM. [Reproduction and raw samples](../../benchmarks/wal-sync-experiment)

### Native descriptor sync

The Linux adapter now retains the directory and active append descriptors across writes. In seven alternating pairs of native release runs, `alvoki-disk-write 64 1` measured a median of 2.991 ms per acknowledged write at `810fb81` and 0.728 ms with direct descriptor sync. Each process warmed up before its timed trial. Both builds used Lean 4.36 and CPU 0 on the same x86-64 VM with an AMD EPYC 9V74, Linux 6.18.57, and an OverlayFS temporary directory.

A separate `strace -f -yy -e trace=execve,openat,close,fsync,rename` run of `alvoki-disk-write 4 1` covered two opens and eight writes including warmup. GNU `sync` execs fell from 24 to zero, successful WAL segment opens from 20 to four, and successful temporary marker opens from 20 to ten. Both builds issued 32 `fsync` calls. [Native adapter](../../lean/Alvoki/Storage/Disk/DiskTable.lean)

The shared append handle schedule preserves the generated operations on the reused-handle path. Paired native release trials at one and 128 acknowledged writes per process showed substantial variation. [Paired timings and reproduction](../../benchmarks/results/disk/append-handle-custody)

### Exclusive staging creation

The native replacement path uses exclusive creation for its scratch files. Same-machine measurements compare acknowledged writes, aligned reopen and torn-tail repair. The report includes repeated write cohorts, same-build controls and syscall counts. [Raw samples and reproduction](../../benchmarks/results/disk/fresh-staging-files)

### Lean readability review

The checkpoint loader cleanup uses Lean's `IO.ofExcept` and constructs an installed state after WAL recovery. Acknowledged writes measured 3.20 ms before and 3.13 ms after. Reopen medians ranged from 0.93× to 1.03× over the same-machine WAL workload matrix. The initial four-run checkpoint medians were 9.24 and 10.29 ms. In a follow-up with 12 interleaved rounds of three samples per build, the pooled medians were 11.47 and 11.47 ms, with a median paired ratio of 1.012×. [Raw samples and environment](../../benchmarks/results/disk/readability)

