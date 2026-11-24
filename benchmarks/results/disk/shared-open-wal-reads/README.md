# Shared optional WAL read benchmark

Baseline `91e54853d8190a73a95f19ca27406bb8f68b4f1a` and candidate
`f3b90eee2f1d8f6df28689d57d2ca47564d440f7` used Lean 4.36.0 Release on
Linux 6.18.57 x86-64, KVM AMD EPYC 9V74, GNU Coreutils 9.7 and Python 3.12.14.
The drivers pinned CPU 1 and alternated binary order within cohorts of 14
pairs. The WAL-only cases include the durability syncs. Checkpoint trials
time reopen after publishing a run set and verify the recovered sequence
and last key. Each checkpoint batch contains three timed opens per build.

| Workload | Pairs | Median paired candidate/base |
|---|---:|---:|
| 32 aligned WAL frames | 42 | 0.999× |
| 32 frames and a repaired tail | 42 | 1.011× |
| 2,048 aligned WAL frames | 42 | 0.953× |
| 2,048 frames and a repaired tail | 42 | 1.014× |
| 4 checkpoint runs of 32 rows | 28 | 1.006× |
| 32 checkpoint runs of 128 rows | 28 | 1.005× |

The WAL-only comparison pools three separate cohorts. The repaired
2,048-frame case ranged from 0.972× to 1.102× across individual cohorts.
The separate A/A control used the baseline binary in both positions and
gave median paired ratios from 0.946× to 1.039×. The measured timings
include filesystem and sync-process variation. The candidate worker's
generated C inlines the shared read helper. Both workers contain 22
constructor-allocation sites, two optional
read calls, one marker decode call, and zero closure allocations or
indirect callback applications.
[First WAL cohort](wal-trials.csv) · [Second WAL cohort](wal-trials-rerun.csv) · [Third WAL cohort](wal-trials-third.csv) · [A/A control](wal-trials-control.csv) · [First checkpoint cohort](checkpoint-trials.csv) · [Second checkpoint cohort](checkpoint-trials-rerun.csv)

## Reproduce

Build `alvoki-disk-replay` and `alvoki-disk-checkpoint` with the pinned
toolchain in both checkouts.

```sh
(cd lean && lake build alvoki-disk-replay alvoki-disk-checkpoint)
```

Copy the [WAL driver](../shared-reopen/compare.py) into a scratch directory.
Place the two replay executables there as `base` and `candidate`. For the
A/A control, use the same baseline executable in both positions.

```sh
python3 SCRATCH/compare.py REPO
python3 benchmarks/results/disk/shared-marked-open/compare_checkpoint.py BASE_BIN CANDIDATE_BIN /tmp/checkpoint-trials.csv
```

The WAL driver writes `trials.csv` next to the script. The checkpoint
arguments name the two checkpoint executables. Median ratios above pool
the per-pair ratios computed by the existing drivers.
[Checkpoint driver](../shared-marked-open/compare_checkpoint.py)
