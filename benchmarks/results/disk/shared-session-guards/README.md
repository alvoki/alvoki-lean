# Shared disk session guards

Baseline `477d315` and the shared phase and handle checks both use the pinned Lean 4.36.0 release build. Linux 6.18.57 ran on an AMD EPYC 9V74 with five visible CPUs and a four-CPU cgroup quota. The generated C for `installed`, `release`, `lookup`, `range`, `acquire`, `acquireAt`, `writeWith` and `checkpoint` matched after consistently renaming generated local variables and labels within each function.

The existing session fixture times 1,048,576 point reads and 131,072 eight-row range reads through one live pin and a 256-row checkpoint. Each of two CPU affinities ran 14 pairs with alternating order. The fixture validates both results with checksums. [Workload and scripts](../session-handles/Bench.lean)

| CPU | Operation | Baseline median (ns) | Candidate median (ns) | Median paired ratio |
| --- | --- | ---: | ---: | ---: |
| 4 | Lookup | 101.89 | 103.72 | 1.0259 |
| 4 | Range | 591.15 | 598.43 | 1.0086 |
| 1 | Lookup | 103.04 | 102.23 | 0.9883 |
| 1 | Range | 588.78 | 574.47 | 0.9740 |

Copy the files in the session fixture to a temporary directory. Run `bash build.sh BASE_WORKTREE base` and `bash build.sh CANDIDATE_WORKTREE checked` with `ALVOKI_TOOLCHAINS` pointing to the pinned toolchains. Run `./base setup database`, then `python3 run.py 4 cpu4` and `python3 run.py 1 cpu1`. [Raw CPU 4 trials](trials-cpu4.csv) · [Raw CPU 1 trials](trials-cpu1.csv)
