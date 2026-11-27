# Fixed-width SSTable experiment

Run from the repository root with the pinned Lean toolchain and a C compiler.

```sh
taskset -c 0 bash benchmarks/sstable/run-fixed.sh 8193 512 5 > policy-trials.csv
```

Choose a CPU in the current process affinity mask. The arguments give the row
count, mixed lookup count per sample and trial count. The runner compiles native
code with `cc -O2 -DNDEBUG`. Each layout gets the same ordered 8-byte keys and
8-byte values. Lookups use a deterministic sequence of row positions with equal
numbers of hits and misses. The format order rotates per trial and each read
workload gets an untimed warm-up. The benchmark checks the result checksum
against the generated data before printing each sample.

Build timings include the streaming writer and final flush. Read timings
exclude open. A separate pass records positional read requests and their byte
counts through the same reader. The block scan uses the verified block payload
once before reading the next block. The other scans call the common row-cursor
API once per row.

## Initial run

Five trials on Linux 6.18.57 x86-64, KVM AMD EPYC 9V45, pinned to CPU 0, with Lean
4.36.0 and GCC 14.2.0. Temporary files were on overlayfs. Timings are warm-cache
medians in ns per operation. [Raw CSV](fixed-trials.csv)

| Format | File bytes | Build per row | Mixed lookup | Read calls per lookup | Scan with `next` per row | Block scan per row |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Variable | 327,752 | 334 | 8,341 | 28 | 600 | |
| Fixed, 1 row per block | 196,688 | 303 | 5,872 | 14 | 421 | |
| Fixed, 128 rows per block | 131,664 | 187 | 32,575 | 14 | 2,340 | 58 |

The 128-row layout requests about 14.7 MB across 512 lookups. The one-row
layout requests 172 KB for the same queries and read-call count. In a block
scan, the 128-row layout uses 65 requests and reads 131,608 bytes. With
`next` it uses 8,193 requests and reads 16,842,776 bytes. Group size trades
point-read cost for smaller files and faster scans when the caller consumes
each block once.

## Validation and lookup reuse

The current runner compares one-row groups with full blocks of 1,016, 4,088
and 16,376 bytes (63, 255 and 1,023 rows). It measures hits and misses
separately as well as the mixed workload, and reports data checksum checks
in the untimed counting pass. On successful fixed-width reads this count
is one per block read with validation enabled, excluding the footer.
An eager open verifies all blocks and discards them. Later reads still
verify their newly loaded bytes. Skip retains footer and exact-length checks.

Five warm-cache trials with the same platform and workload as above.
The table shows the mixed lookup medians.
[Raw CSV](policy-trials.csv)

| Format | Row lookup, lazy | Reuse lookup, lazy | Reuse lookup, skip | Eager open |
| --- | ---: | ---: | ---: | ---: |
| Fixed, 1 row | 6.19 µs | 6.48 µs | 5.02 µs | 2.68 ms |
| Fixed, 63 rows | 19.31 µs | 11.67 µs | 3.72 µs | 165 µs |
| Fixed, 255 rows | 60.76 µs | 25.16 µs | 3.08 µs | 130 µs |
| Fixed, 1,023 rows | 220.41 µs | 56.35 µs | 3.39 µs | 123 µs |

The existing variable-width path took 8.28 µs per mixed lookup. Lazy open
for the fixed layouts read one 56-byte footer and took 0.76–0.99 µs.
With 255 rows per block, lookup reuse reduced data checksum checks from
14 to 5.7 per mixed query. The skip results estimate the cost of data checksum validation on the
same read schedule. These results describe
the pinned warm-cache workload. The one-block scan verified batches of
63–1,023 rows at 55–60 ns per row.

## Exact 4 KiB alignment

```sh
taskset -c 0 bash benchmarks/sstable/run-fixed.sh aligned 65537 4096 5 > aligned-trials.csv
```

Both layouts use 255 rows per full block, the same row bytes and checksums,
and the same lookup with block reuse. The aligned writer pads every block
to 4,096 bytes, including the short final block. The packed layout uses
4,088 bytes for a full block and omits padding from the final block.
Each timed workload checks its result against the same oracle.

On the same Linux overlayfs host, a cold-advised batch starts after
`POSIX_FADV_DONTNEED` on the synced file. The advice runs outside the
timer. It requests kernel page-cache eviction. It supplies no measurement of
physical storage reads, and the batch can warm the file again as it runs.
[Raw CSV](aligned-trials.csv)

| Layout | File bytes | Warm mixed lookup | Cold-advised mixed lookup | Warm block scan | Cold-advised block scan |
| --- | ---: | ---: | ---: | ---: | ---: |
| Packed, 4,088 B | 1,050,712 | 39.58 µs | 40.98 µs | 55.4 ns/row | 74.0 ns/row |
| Aligned, 4,096 B | 1,056,848 | 39.17 µs | 41.59 µs | 55.0 ns/row | 78.8 ns/row |

The scan issued 258 data reads in either layout. This workload did not show
a consistent latency gain from alignment. Both readers used buffered
positional IO, and the aligned adapter also slices each physical read
back to the packed payload and checksum. A physical IO comparison would
require device-level accounting and a workload on the target filesystem.
