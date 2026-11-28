# ALVSST06 paired benchmark

Run from the repository root with the pinned Lean 4.36.0 toolchain. This
uses the same release executable, data, ordering, query seeds, result
checks, and row-cursor scan as the ALVSST05 benchmark. Build samples
include streaming and flush. File sync is outside this workload for both
formats. The native correctness fixture separately exercises file sync.

```sh
(cd lean && lake build immutableSSTableCheck)
taskset -c 0 lean/.lake/build/bin/immutableSSTableCheck --bench-paired
taskset -c 0 python3 benchmarks/sstable/measure-recursive-rss.py
```

Run on Linux 6.18.57, x86-64 AMD EPYC 9V74, overlayfs, GCC 14.2.0,
pinned to CPU 0. The ALVSST05 case ran first for each pair. Lookup and
scan medians are from three warm-cache samples. Positional requests
were independently counted on the same fixture and exclude open.
The CSV's historical `leaf_blocks` column counts all non-root index
pages for ALVSST06. [Raw timing and read samples](recursive-paired.csv)

| Layout at 4 KiB data and 1 KiB index targets | Index height 05 / 06 | Reads per hit 05 / 06 | Hit µs 05 / 06 | Miss µs 05 / 06 | Row scan µs per row 05 / 06 |
| --- | ---: | ---: | ---: | ---: | ---: |
| Fixed / fixed | 2 / 2 | 2 / 2 | 5.39 / 5.53 | 5.45 / 5.49 | 4.64 / 4.74 |
| Fixed / variable | 2 / 3 | 2 / 3 | 5.61 / 8.87 | 5.62 / 8.88 | 4.80 / 8.39 |
| Variable / fixed | 2 / 3 | 2 / 3 | 5.57 / 9.01 | 5.51 / 8.59 | 4.63 / 7.60 |
| Variable / variable | 2 / 3 | 2 / 3 | 5.56 / 8.82 | 5.55 / 8.94 | 4.71 / 7.87 |

At the same targets the 4 KiB fixed/variable, variable/fixed and
variable/variable cases needed an additional index read per hit and
row scan. The recorded 16-case matrix also varies the targets. The
row-cursor scan reacquires its path at each row.

The separate writer-only experiment used one process per run with fixed
8-byte keys and values and the same 4 KiB / 1 KiB targets. Peak RSS is
Linux `wait4` high-water memory and includes process overhead. Build
throughput and peak RSS columns show the median of three fresh processes.
[Raw writer-only samples](recursive-rss.csv)

| Rows | ALVSST05 M rows/s | ALVSST06 M rows/s | Peak RSS 05 / 06 (KiB) |
| ---: | ---: | ---: | ---: |
| 1,000,000 | 4.46 | 4.37 | 10,892 / 10,936 |
| 8,000,000 | 4.26 | 4.37 | 12,864 / 10,936 |

The [index target experiment](index-targets.md) measures larger upper-level targets at several table sizes.
