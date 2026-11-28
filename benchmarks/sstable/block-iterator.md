# ALVSST06 block iterator measurements

The native release benchmark uses fixed 4-byte keys and 40-byte values, Linux
6.18.57 on x86-64 AMD EPYC 9V74, Lean 4.36.0, and an overlay filesystem with
warm file data. It alternates row-index and block-cursor order across three
paired trials. Open and the input builds are outside the timed regions.
The benchmark counts calls to the native source, requested bytes, and Lean
small allocations via the per-thread heartbeat counter. It does not count
large allocations or measure cold storage latency. Other build jobs shared
the machine during these trials, so the raw timings show scheduling variance.

The scan consumes one file. The merge consumes two files with partially
overlapping key ranges and distinct values on equal keys. It uses the real
`SortedRun.next` from PR #33 at
`11543b2b6246dac7fba2789080fdbbe7dc47a174` and streams into the native synced
builder. The two merge variants emitted byte-identical files on every trial.
Throughput is in input rows per second. The output counts were 20,000 and
83,334 for inputs with 12,000 and 50,000 rows per file, respectively.

| Rows per file | Targets (data / index) | Height | Workload | M input rows/s, row → block | Reads, row → block | Bytes, row → block | Lean small allocations, row → block |
| ---: | --- | ---: | --- | ---: | ---: | ---: | ---: |
| 12,000 | 16 KiB / 16 KiB | 1 | Scan | 0.10 → 6.48 | 12,000 → 33 | 195,298,176 → 528,132 | 132,004 → 84,268 |
| 12,000 | 16 KiB / 16 KiB | 1 | Merge | 0.07 → 1.18 | 24,000 → 66 | 390,596,352 → 1,056,264 | 492,294 → 396,822 |
| 12,000 | 4 KiB / 256 B | 4 | Scan | 0.05 → 6.57 | 48,000 → 164 | 57,072,120 → 535,784 | 561,004 → 85,512 |
| 12,000 | 4 KiB / 256 B | 4 | Merge | 0.06 → 0.95 | 96,000 → 328 | 114,144,240 → 1,071,568 | 1,351,223 → 400,239 |
| 50,000 | 16 KiB / 16 KiB | 1 | Scan | 0.11 → 2.68 | 50,000 → 135 | 817,128,640 → 2,200,540 | 550,004 → 351,084 |
| 50,000 | 16 KiB / 16 KiB | 1 | Merge | 0.10 → 1.07 | 100,000 → 270 | 1,634,257,280 → 4,401,080 | 2,051,159 → 1,653,319 |
| 50,000 | 4 KiB / 256 B | 4 | Scan | 0.07 → 1.15 | 200,000 → 673 | 237,724,776 → 2,232,084 | 2,336,664 → 356,191 |
| 50,000 | 4 KiB / 256 B | 4 | Merge | 0.08 → 1.51 | 400,000 → 1,346 | 475,449,552 → 4,464,168 | 5,628,303 → 1,667,357 |

The table uses median elapsed time. The read, byte, and small-allocation
counts were identical within each variant. [Raw trials](recursive-block-iterator-trials.csv)

The script also checks the iterator's `Pull.Exact` contract in a disposable
tree containing the pinned SortedRun contract and proofs. The ALVSST06
library has no SortedRun import.

```bash
git fetch origin refs/pull/33/head
bash benchmarks/sstable/run-block-iterator.sh 12000 50000
```
