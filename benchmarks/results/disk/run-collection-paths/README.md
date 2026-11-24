# Native canonical path extraction

The baseline runtime was built at `2b96374`. Its native disk and benchmark sources match `2c2e75c`. The candidate `46d8c7c` moves the path helpers and makes the inlined WAL commit helper private. The final private revision emitted byte-identical `DiskTable.c` and `DiskPaths.c` and all four release disk binaries matched the measured candidate.

| Workload | Baseline median | Candidate median | Median paired candidate/base | Median paired A/A |
| --- | ---: | ---: | ---: | ---: |
| Open, 32 marked frames | 1.204 ms | 1.212 ms | 0.970× | 0.982× |
| Open, 32 marked frames with tail repair | 2.896 ms | 2.905 ms | 0.988× | 0.991× |
| Open, 2,048 marked frames | 1.766 ms | 1.701 ms | 0.971× | 1.016× |
| Open, 2,048 marked frames with tail repair | 3.614 ms | 3.488 ms | 0.963× | 0.980× |
| Publish 4 checkpoint runs of 32 rows | 10.382 ms | 10.324 ms | 0.990× | 1.010× |
| Reopen 32 checkpoint runs of 128 rows | 2.775 ms | 2.801 ms | 1.025× | 0.997× |
| 16 acknowledged writes | 50.781 ms | 49.940 ms | 1.031× | 1.007× |

Two A/B cohorts supply 24 pairs per workload. A/A uses the same baseline binary in both positions for 12 pairs. Each side contributes its median of three timed trials before calculating the pair ratio. Interleaving alternates binary order. These measurements include real file operations and sync processes. The checkpoint reopen and write paired ratios were above 1.0 in both A/B cohorts. The absolute write medians moved in the other direction, so the samples leave the size of any write impact uncertain.

The pinned Lean 4.36.0 release binaries ran on Linux 6.18.57 x86-64 under KVM on AMD EPYC 9V74, pinned to CPU 1. Of the 129 existing generated C functions across `DiskTable.c` and extracted `DiskPaths.c`, 127 matched after private path symbol relocation and local renaming. The remaining ordinary function, `openLocked`, matched under a type-preserving renaming and permutation of independent consecutive local copies. The module initializer gained the `DiskPaths` initialization. The native checkpoint binary has a separate `DiskDirectory.file` symbol after extraction, and the native open and checkpoint function sizes changed. A syscall trace via a relative symlink matched all 145 observed canonical path calls, and all five resulting file contents matched.

Build `alvoki-disk-replay`, `alvoki-disk-checkpoint` and `alvoki-disk-write` with the pinned Lake at the historical baseline `2b96374` and published candidate `790ded0`. The replay fixture uses a flat `WAL`. Copy the binaries to a temporary directory with the `base-` or `candidate-` prefix, copy `compare.py` there, and run `python3 compare.py ALVOKI_CHECKOUT ab1` from that directory. Use `ab2` for another measurement and `aa` for the same-build control. The driver records individual samples and alternating pair positions in the CSV files.

The repeated write and checkpoint reopen tests used adjacent identical-binary controls on two CPUs. The earlier paired slowdown did not recur. [Repeat measurements](repeat/README.md)

[Current segmented WAL measurements](../native-segmented-wal)
