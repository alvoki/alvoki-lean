# Empty bootstrap and marked reopen with the strict marker policy

The candidate restricts markerless open to empty bootstrap. Fresh directory creation and fixture checks are outside the timed open. Marked fixtures supply the committed byte count, and repair fixtures append an 11-byte tail outside that boundary.

| Workload | CPU 1 candidate / baseline | CPU 4 candidate / baseline | Pooled candidate / baseline | CPU 1 baseline control |
| --- | ---: | ---: | ---: | ---: |
| Fresh empty directory | 1.047× | 1.033× | 1.040× [0.958, 1.095] | 0.987× |
| 32 marked frames | 1.024× | 0.964× | 1.000× [0.972, 1.035] | 0.981× |
| 32 marked frames with repair | 0.955× | 1.032× | 1.008× [0.965, 1.032] | 1.015× |
| 2,048 marked frames | 0.998× | 1.002× | 1.002× [0.939, 1.041] | 0.947× |
| 2,048 marked frames with repair | 0.989× | 0.971× | 0.981× [0.958, 1.049] | 0.958× |

Each cohort uses 14 alternating pairs per workload. The pooled column gives the median of 28 matched ratios with descriptive 95% bootstrap intervals stratified by CPU, using 10,000 resamples and seed 74321. Every interval includes parity. The fresh cohorts have higher candidate medians. Checkpoint reopen on CPU 1 measured 0.981× for four runs of 32 rows and 0.995× for 32 runs of 128 rows. Each comparison uses 14 pairs, with the median of three timed samples on each side of a pair.

The generated open worker removes the legacy tail parser and one of its two replay call sites. It has 23 constructor allocation sites and 18 tag-inspection sites, compared with 22 and 19 in the baseline, across all branches. Both builds emit direct calls with zero closure allocations and zero indirect applications in this worker. Generated point, range and snapshot acquisition bodies match after renaming local identifiers. Write and checkpoint bodies also refer to the same constants under updated generated names.

The baseline is `09178d7` and the published candidate is [`d2d0ae7`](https://github.com/alvoki/alvoki-lean/tree/d2d0ae7), with the measured strict open source from `78d6f4d`. The release toolchain is Lean 4.36.0 on Linux 6.18.57 x86-64 and AMD EPYC 9V74. Use the [existing bootstrap benchmark patch](../shared-open-bootstrap/benchmark.patch) in two measurement checkouts and build `alvoki-disk-replay` and `alvoki-disk-checkpoint`. In a scratch copy of the [paired driver](../shared-open-bootstrap/compare.py), use `for mode in ("marked",)` to time marked cases and the existing fresh case. Pin each invocation with `taskset -c 1` or `taskset -c 4`. Pass the baseline executable in both argument positions for the same-build control. Use the [checkpoint driver](../shared-marked-open/compare_checkpoint.py) with both checkpoint executables on CPU 1.

The historical paired driver writes a flat `WAL`. Use the pinned checkouts for that fixture. [Historical candidate](https://github.com/alvoki/alvoki-lean/tree/d2d0ae7) · [Current segmented WAL measurements](../native-segmented-wal)
