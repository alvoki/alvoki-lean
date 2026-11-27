# Unified SSTable lookup

```sh
taskset -c 0 bash scripts/check-unified-sstable.sh --bench
```

Run from the repository root on Linux x86-64 with the pinned Lean toolchain,
GCC and G++. Use a CPU in your affinity mask. The runner uses the pinned
Google CRC32C backend described in the [checksum comparison](checksums.md).

The workload builds 65,537 ordered 8-byte key/value pairs in both formats
and runs the same deterministic batch of 4,096 queries with equal numbers
of hits and misses. The unified writer uses a 16 KiB data target and a
1 KiB leaf-index target. This produces multiple leaves behind the root.
Each timed batch is preceded by warm-up. Open and construction are outside
the timer. A separate oracle-checked pass counts requested reads and bytes;
it excludes the footer and root read at open.

The same unified file is also read with the bitwise portable Lean CRC32C
reference to show the payoff of the native backend on the complete lookup
path. The portable definition is a specification baseline. An optimized
portable backend could perform differently.

## Recorded run

Three warm-cache trials on CPU 0 of an AMD EPYC 9V45, Linux 6.18.57,
overlayfs, Lean 4.36.0 and GCC 14.2.0. [Raw trials](unified-trials.csv)

| Reader | File bytes | Median mixed lookup | Read requests per lookup | Requested bytes per lookup |
| --- | ---: | ---: | ---: | ---: |
| ALVSST03 | 2,621,512 | 10.10 µs | 34 | 816 |
| Unified, Google CRC32C | 1,052,244 | 5.36 µs | 2 | 17,355 |
| Unified, portable Lean CRC32C | 1,052,244 | 138.65 µs | 2 | 17,355 |

The unified reader trades fewer requests for more bytes. These runs measure
warm lookup latency and requested file bytes under the configured block
targets. They give no device-level I/O counts or cold-cache latency.
