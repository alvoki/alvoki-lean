# Native engine baseline against RocksDB

The pilot uses native Alvoki at `e892ac7` and Debian RocksDB 9.10.0 (`9.10.0-1+b1`). The machine was an x86-64 AMD EPYC 9V74 VM running Linux 6.18.57. Both workloads used CPU 0 and the same OverlayFS volume. This setup is useful for diagnosis and paired regression tests. The storage device behind OverlayFS and its behavior under machine power loss were outside the measurement.

## Workloads and measurement

- **Mixed and maintenance.** Five trials per engine, 8,000 foreground operations, 256 uniformly sampled keys, seed 1847. Both engines alternate puts and point reads with 8-byte keys and 8-byte values against the same key sequence, start with an empty database, and verify results against an in-memory oracle. Every put waits for durability. RocksDB enables its WAL, uses `sync=true` and `use_fsync=true`, disables compression, and uses one foreground caller with up to two background jobs on the same CPU. Alvoki includes acquiring and releasing the latest snapshot in the read time because the public API requires a pin. Warm-up uses a separate fresh database. Throughput includes the measured workload loop and scheduled maintenance. Per-operation p99 is computed within each trial and the table reports medians across trials.
- **Maintenance.** Every 1,000 operations, Alvoki checkpoints, rotates and collects WAL, compacts adjacent runs when available, and collects obsolete runs. RocksDB waits for flush, then manually compacts from the second boundary. Its automatic compaction is disabled in this scenario. Both pin a snapshot at the first boundary, read a historical value during maintenance and release the pin at the third boundary. Alvoki then advances its floor and retains versions for publication at the next checkpoint. Apparent database bytes include engine metadata and logs. Process write bytes are Linux `/proc/self/io` attribution across the workload loop and are distinct from media write bytes.
- **Crash reopen.** A writer checkpoints or flushes 1,024 rows, makes 16, 128 or 512 individually durable puts and stops after reporting the exact acknowledgement count. The harness sends `SIGKILL`. A fresh reader measures open through the first successful point read, captures peak RSS at that point, then verifies all rows. Filesystem caches stay warm. The Alvoki-only variant injects 17 unacknowledged bytes after the kill and verifies that repair preserves the exact committed WAL suffix. The RocksDB comparison uses aligned process-death inputs.

The pilot drives each engine closed loop at its own speed. The roadmap's latency target requires a subsequent common-offered-load run. Maintenance is scheduled at matched operation counts, with engine-specific work at each boundary. The interrupted-frame case covers the Alvoki format. The pilot does not isolate read bytes or sync time in the crash matrix.

## Pilot results

| Scenario | Engine | Operations/s | Read p99 | Acknowledged write p99 |
|---|---|---:|---:|---:|
| Mixed | Alvoki | 2,423 | 6.2 µs | 1.772 ms |
| Mixed | RocksDB | 8,942 | 4.8 µs | 0.531 ms |
| Maintenance | Alvoki | 2,567 | 5.0 µs | 1.439 ms |
| Maintenance | RocksDB | 9,268 | 12.2 µs | 0.463 ms |

Across the five maintenance trials, Alvoki's median apparent size fell from 48,136 to 24,328 bytes between the snapshot-release boundary and the next checkpoint, with 500 writes in between. The corresponding RocksDB measurements were 67,418 and 73,208 bytes. The engines use different maintenance and retention policies, so the size change describes each configuration. Linux attributed approximately 33.3 MB of process writes to Alvoki and 16.9 MB to RocksDB in this scenario.

| Required WAL suffix | Alvoki after SIGKILL | RocksDB after SIGKILL | Alvoki with injected tail |
|---:|---:|---:|---:|
| 16 records | 0.886 ms | 6.084 ms | 1.568 ms |
| 128 records | 0.813 ms | 6.834 ms | 1.621 ms |
| 512 records | 1.040 ms | 6.703 ms | 1.805 ms |

Median peak RSS through the first read was about 10.6 MiB for Alvoki and 14.3–14.4 MiB for RocksDB on the aligned cases. These small, warm-cache runs describe process-death recovery on this setup.

## First bottleneck

The mixed workload reached 27% of RocksDB's throughput. Alvoki's mean put took 0.821 ms out of about 0.826 ms of elapsed workload time per put/read pair. The gap persists when timed maintenance is absent. A separate 128-operation syscall trace found that each of the 64 Alvoki puts synced the WAL, synced the staged marker, renamed it and synced the directory. Each RocksDB put synced its WAL once, alongside additional setup syncs. Use this trace for syscall counts and path attribution. The untraced trials supply the latency numbers.

Start with a durable batch experiment that writes consecutive frames and publishes their boundary once. Define whole-batch visibility, the acknowledgement point and allowed results after a crash before adopting the path. Measure batch sizes 1, 8 and 32 with matched atomicity and durability on both engines, reporting per-batch latency and throughput in logical operations. Keep the single-write cell as its own baseline. Add a common offered-load measurement before assessing the p99 target.

[Raw workload samples and run metadata](../benchmarks/results/disk/engine-baseline) · [Roadmap target](roadmap.md#release-performance)

## Reproduce

Use the pinned Lean toolchain from the repository, a C++17 compiler, and matching RocksDB 9.10.0 development headers and shared library. With a default system library installation:

```sh
(cd lean && lake build alvoki-disk-workload alvoki-disk-crash)
c++ -std=c++17 -O3 -DNDEBUG benchmarks/rocksdb_workload.cc -lrocksdb -o /tmp/rocksdb-workload
c++ -std=c++17 -O3 -DNDEBUG benchmarks/rocksdb_reopen.cc -lrocksdb -o /tmp/rocksdb-reopen

python3 benchmarks/engine_workload.py --rocks-bin /tmp/rocksdb-workload \
  --operations 8000 --keys 256 --interval 1000 --trials 5 --cpu 0 --out /tmp/workload.csv
python3 benchmarks/engine_reopen.py --lean-bin lean/.lake/build/bin/alvoki-disk-crash \
  --rocks-bin /tmp/rocksdb-reopen --prefix 1024 --suffix-sizes 16 128 512 \
  --trials 5 --cpu 0 --out /tmp/reopen.csv
```

For an extracted Debian package, add its include and library directories with `-I` and `-L`, and set `LD_LIBRARY_PATH` to the directory containing the shared objects at run time. Use `--db-root` and `--scratch` to place both databases on the same measured filesystem.
