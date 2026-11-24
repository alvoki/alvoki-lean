# Integrated native adapter measurements

These measurements compare `477d315` with the integrated optional-file, open, checkpoint and session helpers. The candidate is the commit adding this directory. Both builds use pinned Lean Release on the same Linux x86-64 VM. The drivers are pinned to CPU 2 and alternate binary order. See the [optional read instructions](../../optional-file-reads/README.md) for reproduction commands.

| Reopen workload | Candidate pairs | Median paired candidate/base | Median paired A/A |
|---|---:|---:|---:|
| 32 aligned frames | 70 | 0.986× | 0.964× |
| 32 frames and a repaired tail | 70 | 1.012× | 1.012× |
| 2,048 aligned frames | 70 | 1.022× | 0.989× |
| 2,048 frames and a repaired tail | 70 | 1.006× | 1.004× |
| 4 checkpoint runs of 32 rows | 28 | 0.978× | |
| 32 checkpoint runs of 128 rows | 28 | 1.028× | |

The identical-binary controls contain 42 WAL pairs per workload. The first 32-frame aligned cohort had a ratio of 1.128×. Across the four follow-up cohorts the ratios ranged from 0.931× to 0.992×. Checkpoint comparisons use the three-trial median on each side of a pair. These timings include the filesystem and sync process.
