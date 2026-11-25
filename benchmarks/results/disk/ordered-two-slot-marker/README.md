# Ordered two-slot WAL marker

Native release comparison at `29e31be`, on Linux 6.18.57 on an overlay
mount. Each backend used a fresh database, one pinned foreground CPU,
8,000 operations with alternating writes and reads, 256 keys and seed
1847. RocksDB 9.10.0 used synchronous writes. The trial order rotated
after one warm-up per backend and scenario. The latency figures are
medians of three per-trial p99s in a closed-loop test.

| Scenario | Backend | Operations/sec | Read p99 | Confirmed write p99 |
|---|---|---:|---:|---:|
| Mixed | Rename | 2,447 | 9.2 µs | 2,063 µs |
| Mixed | Ordered slots | 4,490 | 5.4 µs | 1,232 µs |
| Mixed | RocksDB 9.10.0 | 8,745 | 5.0 µs | 635 µs |
| Maintenance | Rename | 2,376 | 4.8 µs | 2,732 µs |
| Maintenance | Ordered slots | 4,680 | 3.9 µs | 851 µs |
| Maintenance | RocksDB 9.10.0 | 8,702 | 13.1 µs | 502 µs |

Maintenance ran every 1,000 operations with a snapshot spanning multiple
cycles. Alvoki checkpoints and collects; RocksDB flushes and compacts.
The runs compare workload behavior under maintenance, with different
mechanisms and reclamation semantics. The mixed run sustained 51.4% of
RocksDB throughput, with 1.08× read and 1.94× write service p99. Release
acceptance also needs response latency at a common offered load.

At the end of maintenance the summed regular-file sizes were 88,328 bytes
for rename, 96,496 for slots and 113,837 for RocksDB. The marker itself
accounts for the 8,168-byte Alvoki difference. Median process-accounted
`/proc/self/io` write bytes were 33.3 MB, 49.7 MB and 16.9 MB,
respectively. These counters do not identify physical blocks or the
filesystem's internal writes. Fewer barriers improved foreground latency
while the marker variant increased this write-byte counter.

At a common offered load of 4,000 operations/s, median response p99 for
reads and acknowledged writes was 144.08 and 144.33 ms with slots, versus
14.71 and 14.96 ms for RocksDB. Slots drained 3,724 operations/s while
RocksDB kept up with arrivals. The closed-loop service latency above
therefore overstates how close the engines are under load.

The reopen fixture checkpoints 1,024 writes, acknowledges another 16,
then kills the writer. Reopen medians were 0.924 ms for rename and 1.245 ms
for slots. With a synthetic torn tail they were 1.488 and 1.933 ms,
respectively. The sample is small. Both paths rejected a missing acknowledged
frame without modifying the WAL or marker. Synthesized slot images tested
selection of a complete newer slot and recovery from an invalid target slot.

Open with `Alvoki.Storage.TwoSlotDiskTable.open` to initialize or reopen
a two-slot database. The existing `DiskTable.open` selects rename
publication. Each entry point requires its own on-disk format. Switching
an existing database between formats requires a migration.

The prototype changes only marker publication. It appends and syncs the WAL,
writes the inactive slot in the already opened marker file, syncs the marker,
and then acknowledges. Both marker records use an epoch and checksum. Reopen
syncs the marker before repairing or permitting another overwrite. The
filesystem model requires successful syncs to make their completed writes
durable and a failed or interrupted update to preserve the non-target slot.
An interrupted slot image must decode as the old or new record or be rejected.
A 4096-byte stride is a file layout choice. It does not establish device
failure isolation, and the checksum has finite coverage.

The raw operation samples and harnesses are in the working directory
`work/alvoki-performance/two-slot-marker`. The harness uses the same
[workload](../../../../lean/DiskWorkloadBench.lean) and
[crash fixture](../../../../lean/DiskCrashBench.lean) with each marker adapter. For offered load it
uses the fixed-arrival harness from the experimental revision `81cfb63`
with the same adapters. The harness sends scheduled requests to one FIFO
consumer, drains the queue, and times responses from their nominal arrivals.

The sequential check suite covered Lean kernel checking, dependency audit,
differential workloads, native disk faults, process exit, and exact replay
with and without a torn tail. Its Linux cut fixtures exercise the reported
effects and visible byte images.
