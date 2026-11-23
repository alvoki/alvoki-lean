# WAL sync latency experiment

This experiment builds the Lean write benchmark from commit `097d8b5` in a temporary directory. Only the temporary build receives the adapter patch. It uses stock Lean and a Rust 1.95 helper compiled with optimizations. The helper relies on the Rust standard library for `fsync`. Lean communicates with it through pipes.

Run the experiment on Linux with the repository's bootstrapped Lean toolchain, Git, GNU Coreutils, and Python 3. Install Rust 1.95.0 in the same toolchains directory to match the recorded build.

```sh
ALVOKI_CPU=4 bash benchmarks/wal-sync-experiment/run.sh /tmp/alvoki-sync-results
```

Set `ALVOKI_CPU` to a permitted CPU. If unset, the benchmark selects the highest CPU in its affinity mask. The results path must be new. The two optional arguments following the path are the write count and trial count, which default to 64 and seven. `ALVOKI_TOOLCHAINS` overrides the default `../work/toolchains` directory. All databases and experimental binaries are temporary.

| Mode | Timed write path |
|---|---|
| `reference` | Lean invokes GNU `sync` for the WAL and staged marker and again for the directory, with rename between them. `IO.Process.output` captures both output streams. |
| `plain` | The same GNU `sync` command sequence with stdout discarded and stderr inherited. |
| `stderr` | The same sequence with only stderr captured. |
| `once` | One Rust child per write. The child syncs the WAL and staged marker and replies. Lean renames under the database lock, then waits for the child to sync the directory before acknowledging. |
| `persistent` | The same two-request protocol with one child for the open session. Process setup is outside the write timer. |
| `legacy` | A timing control for the former single WAL sync. It does not update the durable marker and the test database is discarded without reopening. |
| `direct` | A timing control that lets the child rename the marker itself. A child could continue the rename after its parent dies and the lock is released. This mode is for temporary fixtures only. |

The runner checks the two Rust sync protocols with injected staged-file sync failure, directory sync failure, and early child exit. It also checks successful writes by reopening with the reference adapter. Each timed trial discards one warm-up, measures serial acknowledged writes, and verifies the final sequence and value. The reported medians are medians of trial means. The microbenchmarks measure Lean process calls against settled files and Rust filesystem operations with 48-byte appends and 24-byte staged markers.

The checked-in samples contain the raw observations and environment from the final interleaved run. [End-to-end samples](samples/latency-raw.csv) · [Process samples](samples/micro-raw.csv) · [Filesystem samples](samples/rust-stages.csv) · [Fault results](samples/failure-report.txt) · [Environment](samples/environment.txt) · [Summary](samples/report.txt)
