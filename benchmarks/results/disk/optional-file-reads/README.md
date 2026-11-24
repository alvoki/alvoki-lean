# Optional database file reads

The baseline is `477d315`. The candidate adds the shared lookup and read decision from the commit adding these results. Both builds use Lean `v4.36.0` Release on Linux 6.18.57 x86-64 on an AMD EPYC 9V74 VM. The paired drivers are pinned to CPU 2 and alternate the order of the two builds.

| Workload | Pairs | Median paired candidate/base |
|---|---:|---:|
| 32 aligned WAL frames | 14 | 0.994× |
| 32 WAL frames and a repaired tail | 14 | 0.983× |
| 2,048 aligned WAL frames | 14 | 1.005× |
| 2,048 WAL frames and a repaired tail | 14 | 1.015× |
| 4 checkpoint runs of 32 rows | 14 | 0.999× |
| 32 checkpoint runs of 128 rows | 14 | 1.005× |

The generated `readOptionalFile` function and its lstat continuation match after normalizing generated identifiers. The higher-level `openLocked` function assigns temporary variables in a different order. The native benchmark includes filesystem and sync-process variation. [WAL trials](wal-trials.csv) · [Checkpoint trials](checkpoint-trials.csv)

Build `alvoki-disk-replay` and `alvoki-disk-checkpoint` in both checkouts using the pinned Lean toolchain. Use the existing WAL driver with the replay executables as `base` and `candidate` in the driver's scratch directory. Run `taskset -c 2 python3 SCRATCH/compare.py CHECKOUT`. Run `taskset -c 2 python3 benchmarks/results/disk/shared-marked-open/compare_checkpoint.py BASE_CHECKPOINT_BIN CANDIDATE_CHECKPOINT_BIN checkpoint-trials.csv` for the checkpoint runs. [WAL driver](../shared-reopen/compare.py) · [Checkpoint driver](../shared-marked-open/compare_checkpoint.py)
