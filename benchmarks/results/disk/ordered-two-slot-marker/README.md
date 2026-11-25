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
At 3,000 operations/s both kept up. Slots measured 7.87 ms for reads
and 8.20 ms for writes, versus 3.96 and 4.29 ms for RocksDB. One of three
paired trials exceeded twice RocksDB's p99 for both reads and writes.
The separate 2,000 operations/s run did not meet the p99 target.


The reopen fixture checkpoints 1,024 writes, acknowledges another 16,
then kills the writer. Reopen medians were 0.924 ms for rename and 1.245 ms
for slots. With a synthetic torn tail they were 1.488 and 1.933 ms,
respectively. The sample is small. An aligned comparison with RocksDB
at 16, 128 and 512 suffix entries yielded 1.04–1.28 ms medians for slots
and 6.02–6.94 ms for RocksDB. Their checkpoint and WAL formats differ. Both paths rejected a missing acknowledged
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

### Rerun after bounded marker reads

At `bedf647`, the same closed-loop workloads yielded 2,464, 4,356 and
8,359 operations/s in mixed mode for rename, ordered slots and RocksDB
9.10.0 respectively. Ordered slots measured 4.5 µs read p99 and 1,445 µs
acknowledged write p99. The reference recorded 6.5 µs and 665 µs. Slots
reached 52.1% of reference throughput and 2.17× its write p99 in this run.
This comparison measures service latency. Common-load response latency
remains a separate release check.

Maintenance throughput was 2,323, 4,577 and 8,556 operations/s in the same
engine order. The aligned, torn-tail and missing-acknowledged-frame cases
passed, as did the unchanged, unwritten and torn-checksum slot images.
Raw samples and crash checks are in
`work/alvoki-performance/two-slot-ledger-rerun`.

### Working-set and sync diagnostics

At `824e719`, paired trials against RocksDB 9.10.0 reproduced the
individually durable, closed-loop mixed workload with 256 and 4,096
possible keys. Slots reached 4,700 versus 9,807 operations/s with 256 keys
and 4,439 versus 8,973 with 4,096. The corresponding write p99 ratios
were 1.92× and 2.48×. Read p99 was 4.0 and 4.2 µs for slots and 4.0
and 5.1 µs for RocksDB. Under maintenance with an old snapshot, the
write p99 ratios were 2.09× and 2.30×. The larger keyspace changes
hit rate as well as the number of distinct written keys.

A traced 256-key control counted 12,004, 8,004 and 4,008 fsync calls
for rename, slots and RocksDB respectively across 4,000 writes.
RocksDB also issued three fdatasync calls. These are syscall counts.
The trace does not measure physical blocks or device barriers.
A separate paired probe replaced only the marker fsync with fdatasync
on an already established inode. Commit p99 improved in five of ten
pairs and median commit p50 rose from 324 to 341 µs. The engine keeps
fsync.

Aligned reopen with slots took 0.88–0.95 ms across 16, 128 and 512
acknowledged suffix entries, versus 6.51–8.23 ms for RocksDB. With a
16-entry suffix and a torn tail, slots took 1.29 ms versus 1.19 ms for
rename. Both Alvoki adapters rejected missing acknowledged WAL bytes
without modifying the inputs. The full sequential suite passed on
the measured revision.

Workspace raw samples and harnesses are under
`work/alvoki-performance/two-slot-keyspace-4096` and
`work/alvoki-performance/two-slot-marker-data-sync`.

### Offered-load repeat

A repeat with the same frozen binaries and RocksDB 9.10.0 used 256 keys,
8,000 requests, seed 1847 and three paired trials. Both engines kept up
at 2,500 and 3,000 operations/s. At 2,500, slots measured 2.389 ms read
and 2.784 ms acknowledged-write response p99, versus 1.156 and 1.552 ms
for RocksDB. At 3,000, the medians were 16.435 and 16.763 ms versus
10.768 and 11.097 ms. One of the three 3,000-operation pairs exceeded
2.30× for both operations. The lower rate did not reliably close the
tail-latency gap.

The raw request samples, paired ratios, binary hashes and reproduction
harness are under `work/alvoki-performance/two-slot-offered-repeat`
in the workspace.

[Per-trial results](offered-repeat.csv) retain the elapsed time and both
response p99 values in nanoseconds for all 18 runs, including rename.
Each p99 is the nearest-rank percentile of the 4,000 responses of its kind.

### Durability contract for the ordered slots

The alternate strategy writes the inactive 40-byte record at offset 0
or 4096 on a held, non-append descriptor. A batch syncs the WAL before
it writes that record, then syncs the marker before acknowledging the
batch. Reopen validates the selected WAL, syncs the same marker
descriptor used to read the selection, and only then repairs the WAL.

The modeled crash contract requires the database lock and stable
descriptor identity. An interrupted inactive-slot write must preserve
the active record. The inactive record may survive as the old record,
the complete new record, or an invalid record. This last case requires
that a torn image cannot pass the decoder as a different valid record.
Checksums detect many corruptions and this exclusion is a filesystem
and fault-model premise. The 4096-byte spacing by itself establishes
neither power-loss atomicity nor separate physical failure domains.

The model also requires a successful sync to make the relevant writes
durable on the selected inode, and a successful directory sync where
the shared file-management code publishes or removes names. An error
or interruption can occur on either side of the modeled persistence
effect. See the [retry and client-return proofs](../../../../lean/Alvoki/Storage/Disk/WalTwoSlotClientReturn.lean).

The native fault fixture exercises a partial write to each slot and
stops a batch writer immediately after the marker fsync succeeds.
The post-sync case recovers the entire batch and extends the WAL both
before and after keeper rotation. A separate differential test compares
returned batch ordinals, pinned snapshot reads across maintenance, and
rows after reopen with the rename strategy. These tests exercise
process death and visibility through the running kernel's page cache.
The Lean recovery proof takes durable byte and binding observations as
premises. The remaining native refinement obligation is to connect the
reboot namespace and bytes on the same held directory and inode inventory
to those premises, including across failed recovery attempts.

[Native process crash checks](../../../../scripts/check-disk-process-death.py) ·
[Strategy comparison](../../../../lean/Alvoki/Checks/DiskTableChecks.lean)
