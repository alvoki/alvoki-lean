# Legacy WAL open after sharing recovery code

Measured the native `DiskTable.open` that adopts an existing WAL without a `WAL.commit` marker or a checkpoint. Each open validates independently encoded descending WAL frames and installs the marker. The repair case appends an 11-byte incomplete frame. The benchmark removes the marker before warmup and before the timed open. Fixture reset takes place outside the timer. The driver alternates binary order within the 14 pairs in each cohort.

| WAL rows | Tail | Baseline median | Candidate median | Median paired ratio | Baseline vs baseline |
| ---: | --- | ---: | ---: | ---: | ---: |
| 32 | Complete | 4.004 ms | 4.028 ms | 1.012× | 1.023× |
| 32 | Incomplete | 5.317 ms | 5.369 ms | 1.009× | 0.964× |
| 2,048 | Complete | 4.651 ms | 4.594 ms | 0.971× | 0.997× |
| 2,048 | Incomplete | 6.051 ms | 6.036 ms | 1.006× | 0.988× |

The first three cohorts contribute 42 baseline/candidate pairs per workload. The baseline vs baseline control contributes 14. Changes in the paired medians varied by workload and cohort. The observed differences were comparable to measurement variation in the control.

The baseline source was `76361447cf83a7d00ffabc18cef0ed73ff560aed`. The candidate was `6ad77c90779b23f337f203737a8d849215644713`. Both use release `alvoki-disk-replay` at Lean 4.36.0. The measurements ran on Linux 6.18.57 x86-64 under KVM on an AMD EPYC 9V74 with Python 3.12.14, pinned to CPU 1. The emitted C for `Recovery` and `WriteAheadLog` was identical. The C for `openLocked` changed local variable ordering and kept identical counts of constructor allocation and recovery/read call sites. The inline `recoverLegacy` introduced no call site or closure.

To repeat the experiment, use a separate checkout of each source revision. Apply `markerless.patch` with `git apply` in both checkouts. Build the pinned release target with `(cd lean && lake build alvoki-disk-replay)`. Copy the two `lean/.lake/build/bin/alvoki-disk-replay` binaries to a temporary directory as `base` and `candidate`. Copy `../shared-reopen/compare.py` to that directory, then run `python3 /path/to/temp/compare.py /path/to/alvoki-checkout`. Each run writes `trials.csv` alongside the script. Save it before running another cohort. Use the baseline binary for both positions to repeat the control.
