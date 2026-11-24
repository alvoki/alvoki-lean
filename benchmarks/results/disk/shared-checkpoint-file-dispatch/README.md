# Shared checkpoint file dispatch

The baseline is `d8b6218`. The candidate applies this file-dispatch change to that revision. Both builds used Lean `v4.36.0` on Linux 6.18.57 x86-64, an AMD EPYC 9V74 VM, and the overlay filesystem under `/tmp`. The benchmark driver and its children were pinned to CPU 4.

Build each checkout with `lake build alvoki-disk-checkpoint` from `lean/`. Run `LC_ALL=C taskset -c 4 .lake/build/bin/alvoki-disk-checkpoint 4 32 3` on each side, alternating baseline first and candidate first. Each invocation warms up once and measures three publications of four 32-row runs. The memtable starts empty. Opening the database, checking the installed manifest and reopening to check its data happen outside the timer.

The final 20 pairs gave pooled baseline and candidate medians of 10.097 ms and 9.074 ms. The median of the paired median ratios was 0.940×, with ratios from 0.246× to 1.110×. An initial 12 pairs, before removing the unused private single-path sync helper, gave pooled medians of 8.743 ms and 8.399 ms and a paired median of 0.997×. Timing varied across pairs and rounds. [Final timed samples](trials.csv) · [Initial timed samples](trials-initial.csv)

The generated checkpoint entry point in `DiskTable.c` matched the baseline after normalizing local identifiers. In the specialized step loop the candidate inlines the singleton sync arrays and manifest dispatch that the baseline implements through helper calls. The run-write branch matches. Both candidate builds generated the same checkpoint entry point and specialized step loop after normalization. The benchmark exercises the same writes, syncs and rename.
