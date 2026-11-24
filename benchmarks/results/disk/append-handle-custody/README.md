# Shared append handle schedule

This comparison uses the stock `alvoki-disk-write` workload at baseline `580c098` and the isolated append-path candidate `05b251e`. The native fixture and benchmark sources were identical in both builds. The changed routing and `DiskTable` objects and the stock benchmark main were compiled with the pinned Lean 4.36.0 Lake release flags, `-O3 -DNDEBUG`, and linked with the same remaining objects. The build ran on Linux 6.18.57 x86-64 with glibc 2.41 and an AMD EPYC 9V74. Each process ran on CPU 0 with `TMPDIR=/tmp` on OverlayFS.

Use two disposable worktrees at `580c098`. Cherry-pick `4e9e80b` into the candidate worktree to reconstruct the measured append patch on that base. Run `bash scripts/disk-write.sh 1 1` and `bash scripts/disk-write.sh 128 1` in each worktree to reproduce the workload. For pairing, build both release executables once. Alternate baseline-first and candidate-first calls to `taskset -c 0` with those same arguments. The driver performs its normal warmup and checks the recovered final state in both executables.

| Writes per trial | Pairs | Baseline median ms/write | Candidate median ms/write | Median paired change |
|---:|---:|---:|---:|---:|
| 1 | 24 | 0.819 | 0.781 | -4.94% |
| 128 | 10 | 0.669 | 0.696 | +5.04% |

The observed variation between pairs was larger than either median change. These measurements do not resolve a small difference. The generated code retains the operations for choosing, writing, flushing and storing the reused handle. The two fresh-open branches share their result handling. [Paired raw timings](paired.csv)
