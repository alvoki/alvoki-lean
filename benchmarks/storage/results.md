# First native storage measurements

## Inventory and comparability

| Source | Workloads and historical evidence |
| --- | --- |
| ALVSST05 | The current release fixture measures a four-layout and four-block-target matrix with deterministic mixed/hit/miss lookup, row-cursor scan, streaming build and open. The checked-in measurements also count lookup and scan requests. They used an older GCC `-O2` build on an AMD VM, with a different result oracle. [Matrix and raw CSV](../sstable/unified.md) |
| Earlier SSTables and checksum work | ALVSST03/04 trials cover fixed and variable widths, alignment, cache advice, checksum validation and two-level search. The pinned CRC32C benchmark compares the Lean-side implementations and Google CRC32C on deterministic buffers. [Format experiments](../sstable/README.md) · [Checksum experiments](../sstable/checksums.md) |
| Retired DiskTable | The prior engine has single-file versus segmented recovery, clean and torn reopen, batched durability, checkpoint and resource measurements, plus RocksDB runs. The format, public interfaces and durability schedules differ from the current components. [Historical segmented WAL cohorts](https://github.com/alvoki/alvoki-lean/tree/ab79e5f8a861cb6d3e650b5ff69774da0f811d45/benchmarks/results/disk/native-segmented-wal) · [Historical engine data](https://github.com/alvoki/alvoki-lean/tree/ab79e5f8a861cb6d3e650b5ff69774da0f811d45/benchmarks/results/disk) |
| Rust references | The retired `alvoki-block` crate includes packed block, merge and compaction experiments. A separate Rust 1.95 helper measures sync subprocess overhead against the retired Lean adapter. The current tree has no equivalent Rust producer for the measured WAL, ALVSST05 or L0 contracts. [Historical crate](https://github.com/alvoki/alvoki-lean/tree/ab79e5f8a861cb6d3e650b5ff69774da0f811d45/rust) · [Sync experiment and raw results](https://github.com/alvoki/alvoki-lean/tree/ab79e5f8a861cb6d3e650b5ff69774da0f811d45/benchmarks/wal-sync-experiment) |
| Current segmented WAL and L0 | Native correctness fixtures already exercise public operations and fault schedules. The repository had no timing suite for these native APIs at the inspected pins. [WAL merge](https://github.com/alvoki/alvoki-lean/commit/a375c871879e51558be60661d86f73b9cbaa904c) · [L0 snapshot](https://github.com/alvoki/alvoki-lean/commit/791940352e0068a9e303236c8b50b22d638fa139) |

## Measurement platform

The component runtime comes from `main` at
`a375c871879e51558be60661d86f73b9cbaa904c`. L0 is a provisional native snapshot
at `791940352e0068a9e303236c8b50b22d638fa139`. The snapshot passed
`bash scripts/check-native-l0.sh` in a detached worktree. The component
worktree passed `bash scripts/reproduce.sh`. The L0 results describe
execution at the stated pin. Formal acceptance is still pending.

The 28 November 2026 runs were pinned to CPU 0 on an Intel Xeon Platinum
8573C cloud VM, Linux 6.18.57 x86-64 and Debian 13. The build used Lean
4.36.0, Lake's bundled Clang 23.1.1 with `-O3 -DNDEBUG` for generated C,
and GCC/G++ 14.2.0 with `-O2` for the existing native I/O adapters and
`-O3 -DNDEBUG` for the pinned CRC32C. Each cohort used
one warm-up and seven timed repetitions per case. Reported batch values
are medians of uninstrumented trials, with min–max in the generated
summaries. Call p50/p95/p99 are nearest-rank quantiles from the separate
latency pass. Syscall counts come from one separate trace per case.

### Historical capture provenance

The original environment records carry the exact source and harness
checkouts, working-tree status, commands and binary digests. The
component tmpfs run records source and harness `79d5db67`. Both
overlay runs record `3cafc888`. Those three runs used the same
recorded executable digest. The runtime source in those checkouts is
`a375c871` plus the benchmark commits. The L0 tmpfs run records an
L0 checkout at `79194035` with the harness overlay from `9587ec9f`.
[Component tmpfs](raw/components-tmpfs/environment.json) ·
[Overlay](raw/components-overlay/environment.json) ·
[Overlay with eviction advice](raw/components-overlay-advised/environment.json) ·
[L0 tmpfs](raw/l0-tmpfs/environment.json)

Both original tmpfs records contain `shm tmpfs ro,nosuid,nodev,relatime`.
The harness captured `findmnt -T` and its per-mount `VFS-OPTIONS`
before creating the scratch directory. In the current sandbox, the
same query selects a read-only `/dev/shm` mount record. Opening the
directory and reading `mnt_id` from `/proc/self/fdinfo/<fd>` instead
identifies the writable `/dev` tmpfs. Its device number matches the
directory's `stat` result, and `fstatvfs` on the descriptor reports
that it is writable. The writable parent mount shadows the read-only
record that `findmnt` selects.

The archived component trace shows a successful exclusive file create
and `fsync` under `/dev/shm` in `sst-build-sync`. The L0
`l0-flush-64` trace shows successful creates and a manifest rename
under `/dev/shm`. Mount shadowing reproduces the mismatch today.
The historical runs did not record descriptor mount IDs, so their
exact mount topology cannot be confirmed retrospectively. For repeat
runs, compare `findmnt -T "$data_dir" -o ID,TARGET,VFS-OPTIONS,FS-OPTIONS`
with the mount ID of the opened data directory in `/proc/self/fdinfo`
and the corresponding `/proc/self/mountinfo` entry.
[Component traces](raw/components-tmpfs/syscall-traces.tar.gz) ·
[L0 traces](raw/l0-tmpfs/syscall-traces.tar.gz)

## WAL and SSTable on tmpfs

| WAL workload | `logOnly` median wall | `boundary` median wall |
| --- | ---: | ---: |
| 128 appends, in place | 0.431 ms | 0.694 ms |
| 128 appends, 15 rotations | 1.274 ms | 1.687 ms |
| 64 appends, after 1 batch | 0.178 ms | 0.241 ms |
| 64 appends, after 2,049 batches | 1.239 ms | 1.327 ms |
| Reopen empty | 0.116 ms | 0.143 ms |
| Reopen 128 batches | 0.623 ms | 0.861 ms |
| Reopen 2,048 batches, 16 segments | 5.228 ms | 5.629 ms |
| Reopen 2,048 batches, 128 segments | 8.336 ms | 10.447 ms |
| Reopen 8,192 batches, 64 segments | 22.537 ms | 21.381 ms |

The two no-rotation history cases hold policy, batch size, active fill
and sync counts constant. The longer history increased measured CPU
time about 6.9× for `logOnly` and 5.5× for `boundary`, with identical
Lean small-allocation counts within each policy. Release C for
`View.tail` calls `List.lengthTR`. The public guard and the returned
position each compute a tail. `View.append` calls `List.appendTR`. The
linked x86-64 implementation calls and then tail-calls `reverseAux`,
traversing the existing spine twice. This combination explains why
append gets slower even when the thread reuses list nodes. The generated
files are `Alvoki/Experiments/WAL/Segmented/{Contract,Protocol,Native}.c`
under the build IR directory. The tmpfs sync profile puts the per-call
delay near the timer floor in these in-place cases.

The pure decode control uses about 1.64 µs per frame and 70 small
allocations per frame. Generated C shows the scan within the loop on
the bytes obtained from the IO reference. At capacity 128, native
reopen of 8,192 records uses about one million small allocations and
24.6–24.7 MiB process high-water RSS, versus roughly 14.6–14.7 MiB at
2,048. Wall and thread CPU are close on tmpfs. Fixed-history runs with
128 smaller segments are slower than with 16, so recovery needs both
a byte-processing profile and a segment-count control. The two 8,192
wall-time spreads overlap and establish no policy ranking.

| ALVSST05 workload | Median wall | Items/s | Small allocations | `pread64` within measured phase |
| --- | ---: | ---: | ---: | ---: |
| Random lookup, 4,096 queries | 31.86 ms | 128,546 | 228,267 | 8,192 |
| Sequential row cursor, 65,537 rows | 429.71 ms | 152,515 | 2,471,308 | 131,076 |
| Streaming build, 65,537 rows | 19.54 ms | 3,354,839 | 328,473 | 0 |
| Streaming build with file sync | 20.12 ms | 3,257,531 | 328,473 | 0 |

Lookup hit/miss p50 was 6.70/6.71 µs and p95 was 7.40/7.41 µs. A lookup
loads one leaf and one data packet once the root is open. The cursor
scan transferred 333,054,112 bytes through `pread64` for about 1 MiB of
table data. The two initial seek reads account for the remainder over
two calls per row. `Handle.next` reloads and verifies the leaf and
data packet for each row. This is the dominant measured amplification
in sequential iteration. Per-packet validation and decode are still
part of any equivalent candidate path.

## Durability and page cache on overlayfs

These are results from this VM's filesystem stack. The preload measures
elapsed time inside libc sync calls with their native descriptors and no
ptrace. The separate syscall trace measures counts. The backing device,
device cache behavior and host contention were not controlled.

| Native case | Syncs per batch of 128 appends | Median wall / CPU | Call p50 / p95 | `fsync` p50 / p95 |
| --- | ---: | ---: | ---: | ---: |
| `logOnly`, in place | 128 | 42.35 / 6.72 ms | 281 / 471 µs | 278 / 514 µs |
| `boundary`, in place | 256 | 75.79 / 11.21 ms | 500 / 862 µs | 247 / 415 µs |
| `logOnly`, 15 rotations | 248 | 86.92 / 18.70 ms | 3.21 / 4.37 ms, rotating calls | 266 / 601 µs |
| `boundary`, 15 rotations | 436 | 145.78 / 28.41 ms | 4.65 / 5.83 ms, rotating calls | 255 / 611 µs |

A rotation adds eight barriers to a `logOnly` append and twelve to a
`boundary` append in this fixture. Opening a 2,048-batch history at
capacity 128 issued 50 and 82 syncs for the respective policies, with
median wall times of 11.50 and 15.61 ms. These costs are part of the
existing recovery and publication protocol. The WAL overlay curves have
large spreads, including 133.8–260.3 ms for the boundary rotation trial.
The observed sync delay and counts justify target-device measurements
before any storage-bound ranking.

Warm versus eviction-advised SSTable lookup took 32.19
[30.79–86.33] ms versus 43.88 [39.88–67.33] ms per 4,096 queries.
Hit p99 increased from 39.7 to 106.9 µs. Sequential iteration took
434.94 [418.72–756.58] ms warm and 451.73 [444.17–480.72] ms advised.
The spreads overlap. Advice and elapsed time alone do not establish
physical reads, and the batch can rewarm the fixture. The synced SSTable
build measured a median original-descriptor sync of 2.03 ms across seven
calls. Warm build wall-time spreads overlap, so the single-call data
give the more direct estimate of sync delay here.

## Native L0 at the provisional pin

| Tables | Newest hit p50 / p95 | Oldest hit p50 / p95 | Miss p50 / p95 | Table opens per lookup, newest / oldest / miss |
| ---: | ---: | ---: | ---: | ---: |
| 2 | 8.5 / 13.8 µs | 17.0 / 28.8 µs | 10.5 / 15.8 µs | 1 / 2 / 2 |
| 8 | 8.4 / 9.1 µs | 68.0 / 141.9 µs | 42.1 / 82.0 µs | 1 / 8 / 8 |
| 16 | 8.7 / 9.3 µs | 135.8 / 229.7 µs | 84.8 / 169.1 µs | 1 / 16 / 16 |

An oldest hit at 16 tables issued 64 `pread64` calls per request,
including footer/root checks. The out-of-range miss issued 32, because
it could stop after the footer and root within each table. Newest hits
issued four across all depths. The fixed oldest query set rose from about
155 small allocations per lookup at two tables to 1,163 at 16 tables.
The fall-through read path shows roughly linear amplification for
these non-overlapping fixtures.

The median flush was 0.391 ms for 64 rows and 0.524 ms for 256 rows,
with four syncs in either case. The 80/15/5 get/put/delete workload
with eight additional flushes reached 38,473 operations/s on tmpfs.
Mixed get p50/p95 was 0.238/124 µs, reflecting both memtable hits and
oldest-table reads. Its 1,288 operations include the flushes. All flush
and mixed runs verified outcomes after reopening.

## Priorities after L0 acceptance

1. **WAL retained history.** Compare a cached count and an append-friendly
   representation separately. Verify public append positions, scan order,
   discard and reopen against the same contract. The first target is a
   flatter short/long append curve without moving disproportionate cost
   onto `scan`, including the L0 consumer. Measure both policies and
   exercise retained aliases if a candidate relies on uniqueness.
2. **L0 table probes.** Re-pin the accepted implementation. Test proved
   key-range pruning first on disjoint runs, then on overlapping runs and
   tombstones. Compare caching validated root metadata or handles for the
   remaining probes, tracking RSS and descriptor count. Preserve inode
   binding, newer-table precedence and the public error contract.
3. **SSTable sequential reads.** Try a block-retaining cursor through the
   same checked reader, including boundary and short final block cases.
   Count reads and allocations and compare exact iteration results. Use
   a distinct point-lookup workload for any packet decoding changes.
4. **WAL recovery.** Separate file-to-list conversion, validation and
   history assembly experimentally. Measure allocation/footprint and
   recovery on both the fixed-history segment-count pair and the history
   ladder. Require equivalent selected histories and fault results before
   considering a runtime candidate.
5. **Durability and rotation.** Repeat the instrumented cohort on the
   target filesystem and device, including a long interleaved A/A
   run. If rotation still dominates, investigate file preparation and
   namespace work within the existing barrier order. Keep both policies'
   acknowledgement and interruption guarantees fixed.

The figures describe the current code. The optimization items are
hypotheses. No production runtime or proof changes were benchmarked.
The VM denied even a user-only `perf_event_open` probe. CPU attribution
here uses thread clocks, allocations, syscall profiling and the generated
release code. The [runner guide](README.md) includes the local perf command.


## Raw cohorts

The CSVs retain the original trial boundaries, including warm-ups and
separate latency and sync passes. Each traced cohort also contains a
compressed archive of the marked syscall regions.

- [Component tmpfs cohort](raw/components-tmpfs/environment.json) · [Trials](raw/components-tmpfs/trials.csv.gz) · [Syscalls](raw/components-tmpfs/syscalls.csv) · [Sync samples](raw/components-tmpfs/sync.csv.gz) · [Syscall traces](raw/components-tmpfs/syscall-traces.tar.gz)
- [Component overlayfs cohort](raw/components-overlay/environment.json) · [Trials](raw/components-overlay/trials.csv.gz) · [Syscalls](raw/components-overlay/syscalls.csv) · [Sync samples](raw/components-overlay/sync.csv.gz) · [Syscall traces](raw/components-overlay/syscall-traces.tar.gz)
- [Eviction-advised overlayfs cohort](raw/components-overlay-advised/environment.json) · [Trials](raw/components-overlay-advised/trials.csv.gz)
- [Provisional L0 tmpfs cohort](raw/l0-tmpfs/environment.json) · [Trials](raw/l0-tmpfs/trials.csv.gz) · [Syscalls](raw/l0-tmpfs/syscalls.csv) · [Sync samples](raw/l0-tmpfs/sync.csv.gz) · [Syscall traces](raw/l0-tmpfs/syscall-traces.tar.gz)
