# Shared append handle schedule

This comparison uses the stock `alvoki-disk-write` workload at baseline `580c098` and the isolated append-path candidate `05b251e`. The native fixture and benchmark sources were identical in both builds. The changed routing and `DiskTable` objects and the stock benchmark main were compiled with the pinned Lean 4.36.0 Lake release flags, `-O3 -DNDEBUG`, and linked with the same remaining objects. The build ran on Linux 6.18.57 x86-64 with glibc 2.41 and an AMD EPYC 9V74. Each process ran on CPU 0 with `TMPDIR=/tmp` on OverlayFS.

Use two disposable worktrees at `580c098`. Cherry-pick `4e9e80b` into the candidate worktree to reconstruct the measured append patch on that base. Run `bash scripts/disk-write.sh 1 1` and `bash scripts/disk-write.sh 128 1` in each worktree to reproduce the workload. For pairing, build both release executables once. Alternate baseline-first and candidate-first calls to `taskset -c 0` with those same arguments. The driver performs its normal warmup and checks the final sequence and key in the open session before close.

| Writes per trial | Pairs | Baseline median ms/write | Candidate median ms/write | Median paired change |
|---:|---:|---:|---:|---:|
| 1 | 24 | 0.819 | 0.781 | -4.94% |
| 128 | 10 | 0.669 | 0.696 | +5.04% |

The observed variation between pairs was larger than either median change. These measurements do not resolve a small difference. The generated code retains the operations for choosing, writing, flushing and storing the reused handle. The two fresh-open branches share their result handling. [Paired raw timings](paired.csv)

## Retest after durable batch integration

The retest compares GitHub base `9781037` and the integrated append change at `b3a9a26`. The platform, CPU affinity, pinned release flags and alternating variant order match the first comparison. For the additional workload, build `alvoki-disk-batch` with `lake build alvoki-disk-batch` from `lean`. Run `taskset -c 0 lean/.lake/build/bin/alvoki-disk-batch "$scratch" 1024 32` from the repository root, with a freshly created empty directory for `scratch` on every invocation. Each batch trial verifies the recovered sequence and all keys after close and reopen.

| Workload | Pairs | Baseline median ms/commit | Candidate median ms/commit | Median paired change |
|---|---:|---:|---:|---:|
| 1 single write | 24 | 0.821 | 0.811 | -0.64% |
| 128 single writes | 14 | 0.749 | 0.697 | -6.03% |
| 1,024 rows in batches of 32 | 12 | 0.770 | 0.736 | +1.45% |

The variation between pairs dominates these shifts. The generated staging, sync and batch wrapper bodies agree up to local names. The append helper retains the write, flush and cache-update sequence on the reused-handle path. [Single-write raw timings](batch-base-single.csv) · [Batched raw timings](batch-base-batched.csv)
