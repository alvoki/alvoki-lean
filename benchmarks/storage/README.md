# Native storage baseline

This suite runs the public segmented WAL and ALVSST05 SSTable operations on
Linux x86-64. An optional runner builds a native L0 benchmark from a pinned,
detached worktree. Use [the first run](results.md) for findings and raw
measurements.

## Run locally

Install the repository's pinned Lean toolchain, Git, GCC, G++, Python 3, and
Linux utilities `taskset`, `findmnt`, and `lsblk`. Install `strace` to
collect syscall counts. The repository bootstrap command below puts Elan
in a sibling directory. A working Elan already on PATH suffices.

```sh
bash scripts/bootstrap.sh ../work/toolchains
export ELAN_HOME="$(realpath ../work/toolchains)/elan"
export PATH="$ELAN_HOME/bin:$PATH"
(cd lean && lake -v build storageBench) > /tmp/alvoki-storage-build.log 2>&1

python3 benchmarks/storage/run.py --data-dir /dev/shm \
  --output /tmp/alvoki-storage-tmpfs --strace --sync-timing
python3 benchmarks/storage/summarize.py /tmp/alvoki-storage-tmpfs
```

Choose an idle CPU in the affinity mask with `--cpu`. The default is the
first available CPU. Each case gets one warm-up and seven fresh throughput
processes by default. Cases with per-call latency use a second set of
seven processes. The runner shuffles the case order deterministically
within each round. The output directory must be new. Use `--quick
--repeats 1` to smoke-test or repeat `--case NAME` to select a subset. The
default full suite needs up to roughly 30 MiB of workspace on the test
filesystem. Longer runs on slow storage can spend most of their time
preparing fixtures.

Repeat the same release build and case arguments with `--data-dir` on a
known local filesystem to measure durability-path cost. Record device
model and firmware, filesystem and mount options, write-cache settings,
CPU governor and competing I/O when collecting a comparison. Keep the
output and trace directory on a different filesystem from the test files
when practical. Compare candidates on the same host and filesystem with
paired/interleaved repeats and a same-build A/A check before interpreting
small differences.

For a page-cache sensitivity run, use a real filesystem and
`--case sst-lookup --case sst-scan --cache advised`. The runner builds and
syncs the fixture, then issues `POSIX_FADV_DONTNEED` before each process.
Open and subsequent reads can warm the cache, and eviction is advisory.
Warm runs explicitly read the whole SSTable fixture from the same
filesystem before starting the process. Use device counters on the
target host to establish whether the advised run reached storage. The
tmpfs run keeps the WAL and build sync schedules intact and provides a
memory-backed control for their filesystem work.

For the optional L0 baseline, run from the benchmark branch with the
candidate commit available locally. The script stages the harness only in
a new detached worktree. The default pin is the candidate documented in
[results](results.md). Pin the accepted SHA explicitly for the next run,
and run that candidate's native checks before treating it as a new baseline.

```sh
bash benchmarks/storage/build-l0.sh /tmp/alvoki-storage-l0
python3 benchmarks/storage/run.py --suite l0 \
  --binary /tmp/alvoki-storage-l0/lean/.lake/build/bin/storageL0Bench \
  --data-dir /dev/shm --output /tmp/alvoki-storage-l0-tmpfs --strace --sync-timing
```

## Workloads and timed boundaries

| Case | Deterministic work | Included in the timer |
| --- | --- | --- |
| WAL in-place / rotate | 128 serial appends with 32-byte payloads and 0/15 rotations at capacity 128/8. Both `logOnly` and `boundary`. | Public append through acknowledgement. Setup, close, full-history and segment-count checks follow separate timing boundaries. |
| WAL short / long history | Capacity 128, append 64 after 1 or 2,049 acknowledged appends. The timed region begins one batch into the active segment in both cases and contains zero rotations. | Same public append workload. |
| WAL reopen | Recover 0, 128, 2,048 or 8,192 acknowledged batches at capacity 128, plus 2,048 batches at capacity 16. Healthy histories, no injected torn tail. The same fixture is reused within each case. | Public `openExisting`, including selected-history validation and its own barriers. Compare the exact returned history with deterministic input after timing. |
| WAL decode CPU | Repeatedly scan 128 complete frames held in memory. | Scan and exact-result comparison. This control has no filesystem calls in the measured phase. |
| SSTable random lookup | Fixed 8-byte keys and values, 65,537 rows, 4 KiB data and 1 KiB leaf targets, 4,096 seeded alternating hits and in-range misses. Same dimensions as the historical fixed/fixed cohort. | Checked lookup and exact value check on a held, opened native table. |
| SSTable sequential iteration | Same table, all rows in key order. | Public seek once and row-cursor `next` through EOF, checking key, value and cursor. |
| SSTable streaming build | Same logical rows generated on demand. File-flush and original-descriptor-fsync variants use identical input. | Row generation, streaming builder, exclusive create, flush, and the file sync for `build-sync`. Reopen and full scan validate the build outside the timer. |
| L0 read amplification | 2, 8 or 16 flushed tables of 64 rows. Identical lookup keys across depths. Newest hits, oldest hits, and out-of-range misses are separate cases. | Public `get` including table opens/reads and exact result check. |
| L0 flush | 64 or 256 rows already acknowledged and in memory. | One public `flush`, including native table and manifest publication. Reopen and verify exact rows after timing. |
| L0 mixed | Start with eight flushed tables, then 64 rounds of 16 gets, three puts and one delete. Flush every eight rounds. The gets cycle through two fresh values, the just-written tombstone, and an oldest-table key. | All operations including periodic flush and the read oracle. Reopen and verify all changed keys afterward. |

Per-append acknowledgement checks run within the throughput loop. Per-call
latency takes a clock before and after the individual public call in a
separate pass. WAL call samples distinguish rotation from in-place append.
SSTable samples distinguish hits and misses. The L0 mixed pass labels each
API operation. Recovery, scan and build each produce one elapsed sample
per process. Their distributions are across trials, not calls within the
trial.

## Raw data and profiling

`environment.json` records the runtime and harness commits, compiler
versions, binary digest, CPU, mount, exact invocation and workload
parameters. `trials.csv` retains warm-up, throughput, latency and optional
instrumented batch rows. Throughput rows report wall time, current-thread
CPU, Lean current-thread small allocations (raw heartbeats), and Linux
process high-water RSS up to the end of the timed phase. RSS includes
setup and runtime startup. Heartbeats include harness allocations and
exclude large and non-Lean allocations.

`--strace` runs separately, counts file/descriptor syscalls on the thread
executing the timed region and retains that region as `CASE.strace.gz`.
Report syscall counts and bytes from this pass. Its syscall elapsed times
include ptrace overhead. With `--sync-timing`, an independent preload
pass times the original libc `fsync` and `fdatasync` calls without ptrace
and saves every duration and return value in `sync.csv`. It uses the same
file descriptors, barriers and return results. Use the uninstrumented
throughput pass for end-to-end wall time. Summing calls or comparing
`wall - CPU` can help locate delay, but neither establishes physical media
latency on the VM.

For CPU sampling on a host that permits perf events, use the generated
release executable and long enough samples. The memory-backed decode
control can be profiled directly, for example with
`perf record -e cpu-clock:u -g -- lean/.lake/build/bin/storageBench codec 16384`.
For SSTable and WAL native workloads the binary arguments are recorded in
`environment.json`. The generated C is under `lean/.lake/build/ir/`, and
`objdump -d` on the matching executable shows which traversals and copies
survive the release build. See the [repository benchmark rules](../../docs/performance/benchmarks.md).
