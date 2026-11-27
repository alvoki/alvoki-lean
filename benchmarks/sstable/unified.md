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
