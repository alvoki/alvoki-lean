# ALVSST06 partitioned Bloom benchmark

Run from the repository root with the pinned Lean toolchain.

```sh
(cd lean && lake build immutableSSTableCheck)
taskset -c 0 lean/.lake/build/bin/immutableSSTableCheck --bench-filter
```

The release fixture runs both ALVSST06 variants using the same 65,537
ordered rows, 4 KiB data targets and 1 KiB index targets. It uses the
same deterministic queries and scan as the [recursive comparison](recursive.md).
For each layout the unfiltered run comes first. The same platform and timing
method apply. The miss pass counts a false positive when an absent query
reads both its filter and its data packet. FPR uses only queries with
a filter read as its denominator. [Raw samples](bloom-paired.csv)

| Layout | False positives / filter probes | FPR | Hit µs off / on | Miss µs off / on | Build µs/row off / on |
| --- | ---: | ---: | ---: | ---: | ---: |
| Fixed / fixed | 22 / 2,048 | 1.07% | 5.50 / 7.01 | 5.56 / 5.13 | 0.24 / 1.35 |
| Fixed / variable | 18 / 2,048 | 0.88% | 9.01 / 10.51 | 9.13 / 8.51 | 0.40 / 1.39 |
| Variable / fixed | 15 / 2,048 | 0.73% | 8.64 / 10.29 | 8.68 / 7.98 | 0.31 / 1.39 |
| Variable / variable | 15 / 2,048 | 0.73% | 9.06 / 10.34 | 9.22 / 8.31 | 0.40 / 1.51 |

The filter avoided 2,026–2,033 data reads out of 2,048 misses per layout.
Each hit added one filter read. Filter packets added 83,011–84,924 bytes
per table, including checksum overhead. The scan issued no filter reads.
The results describe this warm-cache workload. The implementation remains
opt-in.

The [placement and construction study](bloom-placement.md) compares
complete table probes, startup reads and mask residency. It also isolates
the current hashing, probe planning and bitset costs.
