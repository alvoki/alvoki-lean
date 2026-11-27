# Native segmented WAL measurements

The original single-file adapter is `a8a32a6`. The segmented adapter is `fb7be49` with the segmented benchmark harness from `c50cb73`. The same runtime and benchmark source are integrated in [`272c5c4`](https://github.com/alvoki/alvoki-lean/tree/272c5c467e447b8f76274f6eba4ff641d3b45671). Each build uses the pinned Lean release toolchain. The comparisons use a warm cache on CPU 4 of the same Linux VM. [Environment](environment.txt) · [Raw guarded comparison](guarded-cpu4.csv)

| Workload | Single-file median | Segmented median | Ratio | 95% paired interval |
|---|---:|---:|---:|---:|
| 32 ascending frames, aligned | 1.169 ms | 2.227 ms | 1.905× | 1.694–1.980× |
| 32 ascending frames, torn tail | 2.868 ms | 5.112 ms | 1.783× | 1.702–1.906× |
| 2,048 ascending frames, aligned | 14.085 ms | 15.271 ms | 1.084× | 1.056–1.132× |
| 2,048 ascending frames, torn tail | 16.684 ms | 18.267 ms | 1.095× | 0.962–1.153× |
| 20,000 descending frames, aligned | 6.549 ms | 7.320 ms | 1.118× | 1.065–1.148× |
| 20,000 descending frames, torn tail | 8.443 ms | 11.225 ms | 1.330× | 1.267–1.414× |
| Checkpointed reopen, 4 runs × 128 rows | 1.335 ms | 2.439 ms | 1.827× | 1.649–1.947× |
| Checkpointed reopen, 32 runs × 128 rows | 2.879 ms | 4.051 ms | 1.407× | 1.343–1.464× |
| Acknowledged write, 40 per trial | 3.002 ms | 2.990 ms | 0.996× | 0.949–1.040× |

The candidate uses one segment for these comparisons. Aligned open separately syncs directory metadata and the keeper. The previous adapter groups those in one process invocation. Torn-tail repair settles metadata and suffix absence before replacing the keeper. The measured small aligned reopen adds about 1 ms and the small torn reopen adds about 2.2 ms. Candidate-only controls for 32-frame aligned open and 2,048-frame repair measure 1.028× and 0.986×. The same-build write control measures 0.929×. The write comparison supports no clear latency change at this sample size. A preliminary cohort from `7ef0d1a` before the checkpoint path guard likewise measured 1.932× and 1.928× for 32-frame aligned and torn reopen. [Earlier samples](initial-cpu4.csv) · [Segmented adapter](../../../../lean/Alvoki/Storage/Disk/DiskTable.lean)

| 2,048 ascending frames, same segmented build | One segment | More segments | Ratio | 95% paired interval |
|---|---:|---:|---:|---:|
| Aligned, 8 segments | 15.270 ms | 15.430 ms | 1.010× | 0.970–1.022× |
| Aligned, 32 segments | 15.034 ms | 15.602 ms | 1.038× | 0.994–1.068× |
| Torn tail, 8 segments | 18.368 ms | 18.664 ms | 1.016× | 0.942–1.048× |
| Torn tail, 32 segments | 18.606 ms | 19.137 ms | 1.029× | 0.980–1.047× |

Each cohort uses 12 process pairs, two retained samples per executable invocation, and one untimed warmup. The runner balances which arm goes first and shuffles case order with seed 20261126. The reported ratio divides the medians of the pooled samples. The 95% intervals resample whole pairs 3,000 times with seed 20261127. The raw CSV records each sample in nanoseconds. For writes divide by 40 for per-write latency. In checkpoint rows, `records` means rows per run and `segments` counts runs.

Build `alvoki-disk-replay`, `alvoki-disk-checkpoint`, and `alvoki-disk-write` in both checkouts with the pinned release toolchain. From the current repository, run the comparison with the resulting binary directories.

```sh
PYTHONPATH=benchmarks python3 benchmarks/results/disk/native-segmented-wal/compare.py \
  --base /path/to/reference/lean/.lake/build/bin \
  --candidate /path/to/segmented/lean/.lake/build/bin \
  --cpu 4 --out /tmp/alvoki-segmented-trials.csv
```

Use `--without-write` with the earlier runtime and corresponding segmented benchmark harness to reproduce the preliminary cohort. The independent generator uses the same numbered frames and absolute marker across layouts. It prepares each database before time measurement. The Lean harness validates recovered contents on the warmup and checks the watermark on every trial. The torn case reinstalls the keeper tail before each open. The segmented executable verifies exact selected keeper bytes after repair. [Replay fixture generator](../../../disk_replay.py) · [Replay timer](../../../../lean/Alvoki/Bench/Disk/DiskReplayBench.lean)
