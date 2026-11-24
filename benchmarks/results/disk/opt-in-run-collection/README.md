# Existing disk workloads after adding opt-in run collection

The existing disk adapter function bodies in generated C match the baseline. The new code changes generated declarations and module initialization and adds the collector's functions. Two paired cohorts on the shared Linux VM show variation across CPUs and same-build controls, with no consistent increase in the two workloads.

| Workload | Candidate / baseline | Baseline control | Candidate control |
| --- | ---: | ---: | ---: |
| 16 acknowledged writes | 0.991× [0.957, 1.073] | 0.982× [0.916, 1.106] | 0.972× [0.913, 1.021] |
| Reopen 32 runs of 128 rows | 0.970× [0.920, 1.036] | 0.990× [0.961, 1.008] | 1.001× [0.955, 1.273] |

The figures use medians of matched ratios and descriptive 95% bootstrap intervals stratified by CPU. On each of CPUs 1 and 4 there are 16 pairs per workload and eight pairs of each same-build control. Each observation uses the median of three timed trials. Both programs use pinned Lean 4.36.0 release builds on Linux 6.18.57 x86-64 and AMD EPYC 9V74. The baseline is `639fd95`, whose disk runtime matches `790ded0`. The candidate is `bdf1e3a`, whose native sources match the rebased collector. Measurements exercise existing foreground operations without calling maintenance.

Build `alvoki-disk-write` and `alvoki-disk-checkpoint` in each pinned checkout. Copy the four executables to a scratch directory as `base-write`, `base-checkpoint`, `candidate-write` and `candidate-checkpoint`. Run the [existing paired driver](../run-collection-paths/repeat/compare-repeat.py) with the paths ending in `base` and `candidate`, the output CSV path, and `--pairs 16`. Use `--cpu 1 --seed 74321` and `--cpu 4 --seed 19263` for the two cohorts. Pass both CSVs to the [summarizer](../run-collection-paths/repeat/summarize-repeat.py).

The candidate's native sources are the same in the first main-branch commit containing this archive. Use that revision to rebuild the experiments from the repository.
