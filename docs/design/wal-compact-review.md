# Compact WAL standalone review

The component is reviewed against the WAL on `main` at `a375c871`.
The imported runtime starts from the reviewed compact candidate
[`6db5fd73`](https://github.com/alvoki/alvoki-lean/commit/6db5fd73f7e03402a88269c85fb38d4815abc12d).
The review contains the standalone WAL and its checks. The benchmark
runner and the L0 integration live on their existing branches.

## Linux prefix and drain

The pinned Lean 4.36 implementation of `Handle.rewind` calls
`fseek(fp, 0, SEEK_SET)` and returns any reported error. The pinned
`Handle.read` calls `fread(buffer, 1, count, fp)` and returns a
positive result before inspecting the stream indicators. A positive
short result can include an error. On glibc 2.41, a `fopencookie`
probe that supplies 19 bytes then EOF gave
`n=19 feof=1 ferror=0 errno=0`. Supplying 19 bytes then `EIO` gave
`n=19 feof=0 ferror=1 errno=5`.
[Lean 4.36 runtime](https://github.com/leanprover/lean4/blob/v4.36.0/src/runtime/io.cpp#L568)
· [glibc 2.41 fread](https://github.com/bminor/glibc/blob/glibc-2.41/libio/iofread.c)

The WAL chunk primitive checks `ferror` on every result and accepts a
short success only with EOF. It holds the exact acquired `FILE *` and
allocates at most 65,536 bytes per read. The model assumes a stable
regular-file binding for the held descriptor, a successful rewind to
zero, and the glibc chunk contract at that descriptor. On error the
primitive can have consumed bytes and returns the primary error. The
WAL read schedule returns no prefix on error. No parser, repair or
settlement call runs from that read result. The runtime can release the
errored stream regardless of its file position. At EOF no further
syscall is needed after a short successful chunk. Complete chunks
advance by the request size. The fixed drain fuel includes the EOF
probe even at the Linux signed 64-bit file extent limit.

`readPrefixWith_model` runs the same Lean prefix and drain schedule as
native recovery. Its local report determines the bytes advanced before
an error. A success reaches EOF and returns exactly the requested prefix.
An error is either the first read's report or the particular failing drain
report after a series of full chunks. A seek failure returns immediately.
The bounded-read lemmas connect those results to marker decoding,
boundary-mode selected-prefix parsing and the repair test on arbitrary
byte sequences. The log-only lemma preserves all bytes of every admitted
observation. Even outside the admitted crash model, an oversized log-only
file and its bounded observation both reject before repair. The native
fixtures exercise oversized malformed log-only
input, oversized markers, repair of an oversized boundary suffix, and a
positive short `fread` with `EIO` on the second drain read. The latter
checks that the file is untouched on the failed open and that two
subsequent opens agree on the survivor.
[Read proof](../../lean/Alvoki/Experiments/WAL/Proofs/LinuxBoundedRead.lean)
· [Linux fixture](../../lean/Alvoki/Checks/Tests/WalRecoveryFiles.lean)

## What the compact producers establish

- `openCompactModel_projects` connects the shared single-file native
  success continuation with every outcome in the scheduled open model,
  including reported faults, unacknowledged effects and process stops.
  It preserves the reached image exactly. `openCompactModel_refines`
  exposes the selected ghost history, exact compact reader, writer and
  marker bindings, cursor and equivalent fold on success. Failures
  preserve recoverability and release ownership in the model. The fold
  consumes the one selected decode.
- `recoverCompactWith_delivers` runs the shared compact segmented
  recovery schedule. From local acquisition, cursor/fold, close,
  collection and registration reports, it returns the exact active
  child authority and the folded retained suffix. The abstract segment
  layout determines the active count and the pre-existing bounds theorem
  relates it to base and tail. `withActiveChild_reportedFailure` checks
  that the active scope calls close on the reached error state and
  preserves the primary error when close itself reports an error.
- `scanReadyWith_fileReads` starts from a ready layout and per-file
  scope/read reports. The sealed worker uses two scoped marker reads
  in boundary mode and a scoped data read. Marker selection follows
  from the canonical settled boundary witness. The active worker reads
  the exact installed reader at the installed cursor. The strict
  parser and cursor/count checks are then executed in the proof.
  `scanReadyWith_read` frames the supplied world on success and error
  and yields the exact fold. The world can include the ready state,
  durable disk and owning scopes. Healthy progress is derived
  separately from the availability of the local reads.
  [Scan proofs](../../lean/Alvoki/Experiments/WAL/Segmented/Proofs/CompactScan.lean)
  · [Compact open proofs](../../lean/Alvoki/Experiments/WAL/Segmented/Proofs/CompactOpen.lean)

The Linux read proof uses a local stream contract. The scan composition
uses one local acquisition/read/finalization contract per file and the
installed active descriptor. It derives child contents from executable
marker decoding, data parsing and layout facts. Concrete `IO.FS.withFile`
last-reference release, mutex and path-to-inode correspondence remain
assumptions at this boundary. The native error fixture covers an active
scan error after visiting sealed children and confirms the retained ready
state, bytes and locks.

## Acceptance gate and producer migration

General segmented compact recovery refinement is still open. The
compact recovery stage theorem needs an interpretation of the
actual root selection and collection reports, child allocation/release
and installation cell across every failure or interruption. It must
return the selected ghost history and the reached disk together.
The existing history-based `publicOpenModel_refines`,
`reopensWithAppendAuthority` and retry theorems still prove the
fault cases for their shared history-model schedules. The healthy
compact theorem and active cleanup lemma leave the complete compact
segmented fault, lost-ACK and repeated-recovery composition open. The reported
Linux drain fixture supplies concrete retry evidence for one such cut.

Once the compact producer supplies that composition, replace the native
cached-view handoffs `scan_opened`, `scanActiveModel` and the
history-bearing `installScopedModel` result in the acceptance chain.
Keep the old logical history, `Ready`/`Dirty`, `Installed`, prefix/segment
partition and CONTROL publication proofs as abstract correctness
evidence. The descriptor-level prefix/drain, canonical boundary selection,
scoped read fold and active-cleanup lemmas can be reused by the compact
producer and its future consumer. A pinned detached L0 worktree is the
next consumer checkpoint after standalone review.

## Verification and performance smoke run

Run `ALVOKI_TOOLCHAINS=/path/to/toolchains bash scripts/reproduce.sh`
from the repository root. The source audit, actual injected failure
and kernel/axiom checks serve separate verification purposes.

The existing benchmark runner was exercised in a detached worktree at
`6db5fd73` with the four runtime source files overlaid. The previous
compact binary and the overlaid binary ran back-to-back on CPU 0,
Xeon Platinum 8573C VM, Linux 6.18.57, tmpfs, Lean 4.36.0 release.
Each case has seven runs after a warm-up.

| 8,192 batches at capacity 128 | Compact baseline median wall ms | Checked read median wall ms |
| --- | ---: | ---: |
| logOnly reopen | 23.77 | 25.21 |
| boundary reopen | 21.73 | 26.25 |
| logOnly scan fold | 26.15 | 23.74 |
| boundary scan fold | 23.62 | 25.08 |

All four wall-time ranges overlap. Current RSS is 18.66–18.71 MiB
across the medians. These measurements are a same-host smoke comparison.
[Existing benchmark infrastructure](https://github.com/alvoki/alvoki-lean/tree/perf/storage-baseline/benchmarks/storage)
