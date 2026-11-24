# Shared disk lock lifecycle

Baseline `3585b31` and the shared lock schedule use the same pinned Lean 4.36.0 release build. The generated `DiskTable.c` and `DiskTable.c.o.export` files matched byte for byte. Measurements used CPU 1 on Linux 6.18.57 x86-64 under KVM on AMD EPYC 9V74.

The existing fresh, marked and legacy reopen benchmark ran 14 pairs per workload with alternating binary order. The A/A control used the baseline binary in both positions. Across all nine workloads, the candidate median paired ratios ranged from 0.939× to 1.028×. Baseline against baseline ranged from 0.872× to 1.050×. [Workloads and reproduction](../shared-open-bootstrap/README.md)

Repeat the WAL comparison with the existing benchmark fixture patch and runner. Use `3585b31` for the baseline and the shared lock schedule for the candidate. [Raw pairs](trials.csv) · [Baseline control](control.csv)
