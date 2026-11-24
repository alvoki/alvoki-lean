# Native default v2 checkpoint performance

The baseline and candidate use their respective default manifest formats for checkpoint and open. V2 scans every run once for its checksum in addition to the existing publication or structural validation work. The generated checksum loop has a native byte-array cursor and unboxed `UInt64` accumulator. After normalizing local identifiers, generated C bodies for acknowledged writes, write outcomes, point and range lookups and pin acquisition match the baseline.

| Workload | CPU 1 candidate / baseline | CPU 4 candidate / baseline | Pooled candidate / baseline |
| --- | ---: | ---: | ---: |
| 16 acknowledged writes | 0.910× | 1.040× | 0.956× [0.855, 1.040] |
| Reopen 32 runs of 128 rows | 1.171× | 1.018× | 1.106× [0.984, 1.205] |
| Checkpoint four runs of 8,192 rows | 0.845× | 1.123× | 1.069× [0.678, 1.337] |
| Reopen four runs of 8,192 rows | 1.103× | 1.181× | 1.129× [0.982, 1.387] |

The first two cases use 16 pairs per CPU and interleave eight same-build controls for each executable. Pooled same-build control medians range from 0.866× to 0.999×. The large cases use 12 alternating pairs per CPU. Each pair uses three timed trials on each side. Reported ratios are medians of matched process medians. Intervals are descriptive 95% bootstrap intervals stratified by CPU. The large-case calculation uses 10,000 resamples and seed 74321. All intervals include parity. Concurrent activity on the shared VM made several cohorts noisy, particularly checkpoint publication. Both reopen cases had higher pooled medians.

Build `alvoki-disk-write` and `alvoki-disk-checkpoint` at baseline `ace8937` and at the revision containing this archive with the pinned Lean 4.36.0 toolchain. The measured strict-v2 sources are those of `b1615d1`. The host runs Linux 6.18.57 x86-64 on AMD EPYC 9V74. Use the [existing paired driver](../run-collection-paths/repeat/compare-repeat.py) with the executable prefixes ending in `alvoki-disk`, `--pairs 16`, plus `--cpu 4 --seed 74321` and `--cpu 1 --seed 19263` for the two cohorts. Use `compare-large.py` with the two checkpoint executable paths and `--cpu 1` or `--cpu 4` for the large fixtures. Run each command with a fresh CSV output path.
