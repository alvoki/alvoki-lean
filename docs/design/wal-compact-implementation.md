# Compact WAL implementation checkpoints

The compact native handles carry metadata and ownership. The retained
history stays in the existing logical `Contract` and proof-model
representations. The native scan convenience wrapper builds a list only
when requested. Native recovery processes one bounded segment at a time.
The existing single-file decoder, CONTROL format, data and marker barriers,
and root publication and collection barriers are shared with the previous
schedules. The adopted design and original field inventory are in the
[runtime-state proposal](wal-runtime-state.md).

## Native and proof checkpoints

| Checkpoint | Review surface |
| --- | --- |
| [`42d40dcc`](https://github.com/alvoki/alvoki-lean/commit/42d40dcc) | Single-file native phase with cursor, lock and descriptors. Recovery fold reuses the decoder and settlement. The read-only scan borrows the actual installed reader with positional IO. |
| [`6eca6b4c`](https://github.com/alvoki/alvoki-lean/commit/6eca6b4c) | Compact segmented phase, shared bootstrap and CONTROL operations, ordered recovery and scan, and native scan-fault tests. |
| [`0bc603f8`](https://github.com/alvoki/alvoki-lean/commit/0bc603f8) | Release runner modes for scan and recovery fold, with current and high-water RSS. |
| [`69162885`](https://github.com/alvoki/alvoki-lean/commit/69162885) | Selected-history and absolute-position proof, bounded-recovery regression, and an L0 consumer fixture using real compact WAL handles. |

Single-file recovery holds up to 65,536 data bytes before decoding.
A marker names at most 65,535 bytes. The extra byte witnesses an
unselected suffix so repair still truncates it. A log-only child can
contain at most 255 frames of 52 bytes each. Bytes at and beyond the
buffer limit cannot enter its verified prefix or meet the final torn
frame size limit. Oversized input is drained in fixed chunks so a
reported read error can still precede parser validation. Marker buffers
keep one extra byte to distinguish oversized slots. Native tests exercise
preservation on oversized log-only rejection and boundary repair with a
suffix beyond the bounded buffer. This is a bounded-memory reader even
on malformed inputs. The consumed prefix, decoded batches and caller
accumulator can coexist briefly within a child scope.

A ready single-file handle retains its exact acquired read description.
The active read uses the installed cursor's extent and strict framing
checks. The segmented scan holds the root scope, validates and reads the
selected sealed children with scoped read-only descriptors, and borrows
the registered active child. In-place/rotation append and discard update
the compact session through the existing owning phase. The root and
child handles survive a reported scan error. The native fixture injects
an EIO at the active read after a retained sealed segment, compares
CONTROL and segment bytes, verifies both exclusive locks, retries scan,
appends, then reopens twice under both policies. The read-only scan
contributes the existing abstract scan event on success. Errors return
no history observation and preserve the phase, durable state and
resource ownership.

### Refinement evidence and remaining bridge

- `Native.compactBounds_eq` connects installed metadata to abstract
  base and tail. The old mutation model still supplies the logical
  history and effects proof. Native and model append use the same
  `appendOwnedCore` and single-file `appendStateWith`.
- `scanReadyWith_selected` proves that the scan schedule's ordered
  child fold equals folding exactly the abstract retained suffix with
  its absolute positions. `scanReadyWith_read` proves success and
  failure framing for that executable schedule from scoped child
  read reports. `ReadOutcome.healthy` derives healthy progress
  separately from the availability premise.
- The bounded-read lemmas prove marker decoding is unchanged by the
  cap, the boundary scanner sees the same selected prefix, the extra
  byte preserves its repair decision, and admitted log-only images fit.
  The Linux adapter still needs correspondence for the actual prefix
  read and drain/error behavior. The compact segmented open wrapper
  needs its reached-resource and retry proof before integrated L0
  can use the prior native refinement at the new boundary.
  [Bounded-read lemmas](../../lean/Alvoki/Experiments/WAL/Proofs/BoundedRead.lean)
- Existing model proofs, kernel/axiom checks and the native fixture
  suites exercise reported failures, marker reply loss, writeback,
  power-loss choices and reopen selection at their existing abstraction
  levels. The compact handoff still needs the native primitive bridge
  above. The fixture results and proof results are separate evidence.

Removing executable history simplifies the ready representation and
append guard. Factoring root-only effects also made the model's
collect/reopen equation definitional, eliminating its prior induction.
This checkpoint adds a compact read composition and exact position
proof while keeping the old logical producers for fault coverage.
Across WAL proof modules that is a net increase of 172 source lines
from the approved design commit, including comments and blank lines
(`git diff --numstat e1734fc7...69162885 -- '*/Proofs/*.lean'`).
The later bounded-read lemmas add a separate proof obligation. A net
reduction remains a hypothesis. Recount after the compact open
producer closes the new bridge and the compatibility proof projections
can be retired. There is one native implementation for each public
operation.

## Integrated L0 migration

A migration fixture uses the actual `ExperimentalL0.decode` and
memtable insert operations with the compact native WAL on both
policies. It verifies replay of puts and tombstones, exact watermarks,
the ready handle's metadata and repeated reopen. A corrupt later WAL
frame wins over an earlier private decode error or an invalid watermark.
With valid WAL framing, the watermark error wins over L0 decode and
required-table errors, and a decode error precedes a table error.
Run it with `cd lean && lake exe compactWalReplayCheck`.
[Fixture](../../lean/Alvoki/Checks/Tests/CompactWalReplay.lean)

1. After the accepted native L0 pin is available, use the public
   compact bounds observation for the write guard and the flush
   watermark. Feed the metadata frame from the reached ready
   WAL to the write/flush proof. Keep the manifest publication and
   current use of the WAL release boundary.
2. Keep manifest reopen first. Carry its watermark to
   `openExistingFold` with an `Except String MemTable` accumulator.
   Skip L0 decoding at or below the watermark while the WAL validates
   selected frames. A decode failure stays in the accumulator while
   WAL recovery finishes. At the ready return register the exact
   child immediately in the recovering L0 phase. Check the watermark
   range, then the deferred decode result, then the required tables.
   Only then publish L0 online. On failure, release the reached WAL
   and preserve the original error.
3. Replace `scanAfterReopen` in the integrated producer chain with
   the compact recovery postcondition. Keep the exact ready child,
   registered authority, reached disk and same permitted survivor on
   repeated reopen. Recheck the existing L0 failed-open and
   append/flush cut fixtures on the joint candidate. Compare the joint
   candidate against the pinned L0 benchmark only after this handoff.

The design fixture is scoped and executes before integrated L0
migration. The active integration reference used for the review was
[`79194035`](https://github.com/alvoki/alvoki-lean/commit/791940352e0068a9e303236c8b50b22d638fa139).

## Release measurements

Seven fresh processes per case after one warm-up, pinned to CPU 0 on a
Xeon Platinum 8573C VM, Linux 6.18.57, tmpfs. The shared cases use the
same deterministic 32-byte inputs and timed boundaries. Release Lean
4.36.0 uses Lake's Clang `-O3 -DNDEBUG`. The baseline is
`3470541f` with the same two benchmark-only RSS measurement files
copied into its detached worktree. The compact runtime and executable
are pinned at `69162885`. These are back-to-back cohorts.
Wall-time ranges and instrumented passes are in the raw files.
The filesystem measurements describe the memory-backed environment.

| Case, policy | Baseline | Compact |
| --- | ---: | ---: |
| Short-history append, logOnly, CPU ms / 64 | 0.175 | 0.137 |
| Long-history append, logOnly, CPU ms / 64 | 1.390 | 0.139 |
| Short-history append, boundary, CPU ms / 64 | 0.298 | 0.282 |
| Long-history append, boundary, CPU ms / 64 | 1.195 | 0.201 |
| Reopen 8,192, logOnly, wall ms / current RSS MiB | 21.11 / 24.70 | 20.73 / 18.68 |
| Reopen 8,192, boundary, wall ms / current RSS MiB | 23.05 / 24.62 | 19.33 / 18.66 |
| Reopen and check 8,192 through a fold, logOnly / boundary, wall ms | — | 24.03 / 24.37 |
| Ready scan and check 8,192 through a fold, logOnly / boundary, wall ms | — | 23.81 / 22.51 |

The append comparison keeps active occupancy, capacity, bytes and
durability policy fixed. Only the existing retained history length
changes from 1 to 2,049 batches. Release code derives tail from the two
CONTROL coordinates and active count. It also advances that count after
the child append, without traversing earlier batches. Median CPU in
the compact cohort shows no increase with retained history. Rotation
still exercises the same publication and durability work.

The 8,192-batch reopen uses 64 segments. Current RSS comes from
`smaps_rollup` immediately after the measured phase and before the
materializing correctness check. It includes Lean, allocator pages
and fixture inputs. Some small compact cases have higher process RSS.
At 8,192 the compact representation uses about 6 MiB less current RSS.
Both implementations still allocate about one million small objects
while decoding 8,192 frames. The observed no-consumer recovery timing
ranges overlap. The explicit recovery and scan folds validate every
payload and position in the benchmark accumulator.

The trace and independent sync probe agree on the shared durability
counts. For 8,192-batch reopen these are 194 sync calls for `logOnly`
and 322 for `boundary`, including the recovery barriers. The on-demand
scan uses 189/315 `openat` calls for log/boundary, one active
`pread64` and zero sync calls. The convenience list wrapper is outside
the scan timer.

See the [runner guide](../../benchmarks/storage/README.md) for the
release build and flags. The exact commands, platform and binary
digests are in the cohort metadata.

- Baseline [environment](../../benchmarks/storage/raw/compact-wal/baseline/environment.json) · [trials](../../benchmarks/storage/raw/compact-wal/baseline/trials.csv.gz) · [sync durations](../../benchmarks/storage/raw/compact-wal/baseline/sync.csv.gz) · [syscalls](../../benchmarks/storage/raw/compact-wal/baseline/syscalls.csv) · [traces](../../benchmarks/storage/raw/compact-wal/baseline/syscall-traces.tar.gz)
- Compact [environment](../../benchmarks/storage/raw/compact-wal/candidate/environment.json) · [trials](../../benchmarks/storage/raw/compact-wal/candidate/trials.csv.gz) · [sync durations](../../benchmarks/storage/raw/compact-wal/candidate/sync.csv.gz) · [syscalls](../../benchmarks/storage/raw/compact-wal/candidate/syscalls.csv) · [traces](../../benchmarks/storage/raw/compact-wal/candidate/syscall-traces.tar.gz)
