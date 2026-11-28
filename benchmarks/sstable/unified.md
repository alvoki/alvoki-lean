# ALVSST05 benchmark matrix

```sh
taskset -c 0 bash scripts/check-immutable-sstable.sh --bench
```

Run from the repository root on Linux x86-64 with the pinned Lean toolchain,
GCC and G++. Choose a CPU in your affinity mask. The runner builds the pinned
[Google CRC32C backend](checksums.md). Every ALVSST05 case uses this backend
with lazy verification and the same two-level index. The current runner
builds the fixture with Lake in release mode (`-O3 -DNDEBUG` for generated
Lean C). The recorded trials below used the previous GCC `-O2 -DNDEBUG` build.

Each file holds 65,537 ordered rows. Fixed fields contain 8 bytes. Variable
keys contain 8–15 bytes and variable values 8–23 bytes, using deterministic
suffixes. The ALVSST03 comparison in the earlier matrix used the same input
bytes for each paired case. Reproduce that baseline at
[commit cb35d0f5](https://github.com/alvoki/alvoki-lean/tree/cb35d0f5).
The current runner exercises ALVSST05. Each case runs the same deterministic
sequence of 4,096 mixed lookups, plus the hit and miss subsets separately.
The scan walks all rows via the public `next` operation.

Data targets are 1, 4 and 16 KiB with 1 KiB index leaves. An additional case
uses 4 KiB targets for data and index leaves. These targets include the packet
checksum and do not imply exact physical alignment. Larger-than-target
individual entries would still be allowed within the hard format limits.

Lookup and scan results are checked against the same oracle in a warm-up, an
untimed read-count pass, and three timed runs. A separate row records the
streaming build time including flush, and three samples record open time.
The index/data request counters describe lookup and scan only. Open loads
and checks the root once, outside those timers. Scan timings use the current
row-cursor API. A block iterator would be a separate workload.

The previous [single-layout run](history/unified-single-layout-trials.csv)
is preserved. The [earlier experiments](README.md) cover the separate FNV-1a
formats, including exact alignment and alternative validation policies.

## Current results

Three warm-cache trials on CPU 0 of an AMD EPYC 9V45, Linux 6.18.57,
overlayfs, Lean 4.36.0 and GCC 14.2.0. Times below are median microseconds
per mixed lookup through the public table whose operations the end-to-end
theorem covers. [Raw build, open, hit, miss, lookup and scan data](unified-trials.csv)

| Key / value | 1 KiB data / 1 KiB leaf | 4 KiB data / 1 KiB leaf | 16 KiB data / 1 KiB leaf | 4 KiB data / 4 KiB leaf |
| --- | ---: | ---: | ---: | ---: |
| Fixed / fixed | 4.48 | 4.75 | 5.50 | 12.00 |
| Fixed / variable | 4.60 | 4.94 | 5.73 | 12.03 |
| Variable / fixed | 4.58 | 4.76 | 7.04 | 10.94 |
| Variable / variable | 4.78 | 4.87 | 5.72 | 11.38 |

With 4 KiB data targets and 1 KiB leaf targets, each mixed lookup requested
one leaf and one data block. The root was loaded at open. The reader
requested about 5.1 kB per lookup. These are file-read requests and bytes.
The run has no device-level I/O counters.

| Key / value | Index leaves | Data blocks | File bytes | Hit µs | Miss µs | Scan via `next` µs/row |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Fixed / fixed | 13 | 258 | 1,062,748 | 4.69 | 4.72 | 4.19 |
| Fixed / variable | 25 | 508 | 2,096,252 | 4.94 | 4.98 | 4.22 |
| Variable / fixed | 24 | 443 | 1,832,479 | 4.73 | 4.71 | 4.34 |
| Variable / variable | 37 | 693 | 2,864,682 | 4.86 | 4.81 | 4.08 |

The [previous paired matrix](history/unified-before-proof-trials.csv)
records the ALVSST03 baselines and the prototype before it was connected to
the public proof. The current benchmark runs only ALVSST05.
