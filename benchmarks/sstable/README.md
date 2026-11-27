# Fixed-width SSTable experiment

Run from the repository root with the pinned Lean toolchain and a C compiler.

```sh
taskset -c 0 bash benchmarks/sstable/run-fixed.sh 8193 512 5 > fixed-trials.csv
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

## Recorded run

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
