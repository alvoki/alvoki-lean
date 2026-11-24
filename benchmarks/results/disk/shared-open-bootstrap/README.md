# Shared WAL recovery and bootstrap schedule

The timed operation is native `DiskTable.open`. Fresh open uses a newly created empty directory for each trial, including warmup. The legacy cases start with an existing WAL and remove its marker before each open. Marked WAL cases start with a marker for the complete frames. The repair cases append an 11-byte tail. Fixture setup and result checks take place outside the timer. Checkpoint cases time open after republishing a seeded run set.

| Workload | Pairs | Baseline median | Candidate median | Median paired ratio | Baseline vs baseline |
| --- | ---: | ---: | ---: | ---: | ---: |
| Fresh empty directory | 42 | 4.280 ms | 4.225 ms | 1.020× | 1.028× |
| 32 legacy frames | 42 | 4.229 ms | 4.205 ms | 0.989× | 0.927× |
| 32 legacy frames with repair | 42 | 5.644 ms | 5.634 ms | 0.995× | 0.900× |
| 32 marked frames | 42 | 1.207 ms | 1.285 ms | 1.030× | 0.957× |
| 32 marked frames with repair | 42 | 2.821 ms | 2.915 ms | 1.016× | 0.966× |
| 2,048 legacy frames | 42 | 4.899 ms | 4.784 ms | 0.994× | 1.047× |
| 2,048 legacy frames with repair | 42 | 6.480 ms | 6.385 ms | 1.007× | 1.009× |
| 2,048 marked frames | 42 | 1.881 ms | 1.781 ms | 0.983× | 1.025× |
| 2,048 marked frames with repair | 42 | 3.575 ms | 3.480 ms | 0.981× | 0.996× |
| 4 checkpoint runs of 32 rows | 14 | 1.189 ms | 1.177 ms | 0.985× | |
| 32 checkpoint runs of 128 rows | 14 | 2.661 ms | 2.601 ms | 0.980× | |

The candidate-to-baseline ratios pool three 14-pair WAL cohorts. The baseline-versus-baseline control is a separate 14-pair cohort. Binary order alternates within each cohort. The 32-frame aligned marked case measured 1.083×, 0.970×, and 1.069× in its individual cohorts. Each checkpoint pair uses the median of three timed opens from each executable. The median paired ratio divides within each pair before taking the median.

The measured source revisions were `d8b6218` and `77556fb`. Both use Lean 4.36.0 release builds, pinned to CPU 1 on Linux 6.18.57 x86-64 under KVM on AMD EPYC 9V74, GNU Coreutils 9.7 and Python 3.12.14. Both generated `openLocked` workers contain 22 constructor-allocation sites, 19 object-tag inspections, the same file, validation and installation call sites, zero closure allocations and zero indirect applications. The reference-count sites differ. The shared WAL recovery schedule is inlined in the candidate.

[First WAL cohort](wal-trials-1.csv) · [Second WAL cohort](wal-trials-2.csv) · [Third WAL cohort](wal-trials-3.csv) · [WAL control](wal-trials-control.csv) · [Checkpoint trials](checkpoint-trials.csv)

## Reproduce

Use separate checkouts for the baseline and candidate. Apply the benchmark fixture patch in each, then build both release targets with the pinned Lean toolchain. Use the baseline binary in both positions to repeat the WAL control.

```sh
git apply --unidiff-zero /path/to/shared-open-bootstrap/benchmark.patch
(cd lean && lake build alvoki-disk-replay alvoki-disk-checkpoint)
python3 benchmarks/results/disk/shared-open-bootstrap/compare.py . BASE_REPLAY CANDIDATE_REPLAY /tmp/open-trials.csv
python3 benchmarks/results/disk/shared-marked-open/compare_checkpoint.py BASE_CHECKPOINT CANDIDATE_CHECKPOINT /tmp/checkpoint-trials.csv
```
