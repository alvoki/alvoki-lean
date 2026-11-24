# Write and checkpoint reopen repeat

The original paired slowdown on these two workloads did not recur. Both pinned CPUs measured paired medians below 1.0, while controls using the same binary varied in both directions. The extraction keeps its existing code.

| Workload | Baseline vs extraction | Baseline vs baseline | Extraction vs extraction |
| --- | ---: | ---: | ---: |
| 16 acknowledged writes | 0.988× [0.949, 1.024] | 1.043× [0.970, 1.257] | 0.963× [0.899, 1.059] |
| Reopen 32 checkpoint runs of 128 rows | 0.972× [0.874, 1.038] | 0.996× [0.955, 1.007] | 1.020× [0.863, 1.084] |

The table reports medians of matched ratios with descriptive 95% pair-bootstrap intervals, stratified by CPU. There are 48 A/B pairs and 24 pairs of each identical-binary control per workload across CPUs 1 and 4. Within each CPU we alternate A/B order and interleave one identical-binary control for every A/B pair. Each side uses the median of three timed trials from the existing native benchmark. The CPU load varied on the shared Linux VM and all samples were retained. Candidate/base medians per CPU were 0.988× and 0.990× for writes, and 0.973× and 0.970× for reopen. Reopen varied with pair order. The repeat leaves room for timing differences smaller than its resolution.

Both sources are pinned Lean 4.36.0 release builds. Baseline was `1c2a1d4` and extraction was `920c604`. Each emitted the same generated C as its earlier comparison. Native disassembly of `DiskTable.write` and its checkpoint loader shows one call to the extracted `DiskDirectory.file` in place of two direct string append calls. A diagnostic build marking `DiskDirectory.file` and the private `DiskFile.name` as inline restored both direct appends in those functions. Those diagnostic annotations were left out of the extraction.

To reproduce, build `alvoki-disk-write` and `alvoki-disk-checkpoint` in each checkout. Copy their release binaries to a temporary directory as `base-write`, `base-checkpoint`, `candidate-write`, and `candidate-checkpoint`. Use `compare-repeat.py /path/to/temp/base /path/to/temp/candidate cpu1.csv --cpu 1 --seed 74321` with Python and run the second cohort with `cpu4.csv --cpu 4 --seed 74322`. Pass the resulting files to `python3 summarize-repeat.py cpu1.csv cpu4.csv`.
