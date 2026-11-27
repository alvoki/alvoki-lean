# Scoped builders for packed output

The write gap largely closed when an experimental backend could allocate a private buffer once and fill it directly. At one million input records, the best scoped variant per workload was at most 8% slower than the fastest Rust control across replay, fused merge, dense rewrite, and the packed pipeline in these tests. Stock Lean still has a substantial gap. The prototype uses the pinned Lean runtime ABI and handwritten C lowerings in separate experiment binaries.

## Results

Median milliseconds over nine trials at one million total input records on the pinned VM. Best scoped and best Rust are selected separately from the tested variants for each row. The Rust comparison includes a tuned pointer-cursor control as well as the previous Rust baseline.

| Workload | Stock Lean | Guarded inline | Best scoped | Best Rust |
|---|---:|---:|---:|---:|
| Alternating replay | 7.10 | 3.70 | 0.87 | 1.18 |
| Shuffled replay | 12.36 | 7.72 | 1.08 | 1.29 |
| Update-heavy replay | 6.09 | 4.44 | 0.73 | 0.76 |
| Alternating fused merge | 8.01 | 5.24 | 1.72 | 2.48 |
| Shuffled fused merge | 13.98 | 9.56 | 2.76 | 2.98 |
| Update-heavy fused merge | 6.00 | 3.67 | 1.57 | 1.47 |
| Dense packed rewrite | 5.38 | 5.92 | 0.90 | 1.03 |
| Alternating packed pipeline | 12.44 | 9.32 | 5.75 | 7.15 |
| Clustered packed pipeline | 12.90 | 8.87 | 6.82 | 6.97 |
| Shuffled packed pipeline | 18.27 | 13.18 | 6.86 | 7.61 |
| Update-heavy packed pipeline | 8.33 | 6.01 | 4.20 | 3.94 |

The profiles are synthetic compaction proxies. Alternation is a stress case. Shuffled interleave assigns successive keys independently to either run. Clustered ranges switch sides after runs of 32, 128, 512, or 2,048 records. Update-heavy merges a base run with an update run whose records contain 75% existing keys, yielding 625,000 surviving records at the largest size. Each pipeline includes allocation, fused merge, validation, a full packed scan and 20,000 mixed point lookups.

## What changed

- **Scoped output.** Replay borrows immutable runs and a validated trace, allocates the complete destination once, emits exactly one record per trace byte, and returns the buffer only after it is initialized. Fused merge reserves capacity for both runs and sets the final length after processing collisions. These loops avoid per-record ownership checks and generic slice dispatch.
- **Branching.** The branchless variant selects a source pointer with a conditional move and updates the two cursors arithmetically. On shuffled replay it took 1.08 ms compared with 4.43 ms for the branching scoped kernel. On alternating replay, the branching variant was faster at 0.87 ms versus 1.05 ms. The best timings use a workload-specific choice. No production selection heuristic was tested.
- **Dense writes.** One variant copies the block and patches whole values. The alternate binary fuses the copy and XOR into a single pass across 16-byte records and took 0.90 ms versus 0.97 ms for copy-then-patch. The two variants coincided with the branching and branchless builds. Dense writing uses no winner branches.
- **Matched control.** The tuned Rust builder uses the same prevalidated cursor technique and writes into a fresh allocation. It reduced shuffled fused merge from 6.48 to 2.98 ms and update-heavy fused merge from 2.62 to 1.47 ms. This is the strongest control for distinguishing the algorithm and storage model from the language frontend. Dense rewrite uses the existing Rust copy-and-patch control.

The scoped code closes the gap on these packed algorithms on this machine. Stock Lean's per-record output path still incurs the measured costs. An upstream integration needs a scoped mutable buffer or bulk fill operation whose ownership and capacity facts are available to native code generation, followed by independent validation of the runtime implementation. These benchmarks leave owned record materialization and real compaction traces unmeasured.

## Contract and checks

Stock builds use the Lean bodies. The extra binaries replace three generated entry points at link time. The build checks the View and ReplayPlan fields used by the prototype. A `ReplayPlan` carries an erased proof that the existing validator accepted the immutable trace and both cursor bounds. Fused merge derives extents from previously validated version-1 payloads. Both wrappers borrow input storage and fill a fresh destination. Exact allocation lengths use the runtime's overflow checks.

The C lowering and the matched Rust pointer loops are trusted for their implementation of those contracts. Eight exact fixtures and five malformed traces were checked. All measured writers matched the independent oracle byte for byte and all pipeline checksums agreed. The existing Lean/Verus reproduction and merge-phase fixture suites passed. A full refinement proof of the scoped runtime is open.

```sh
bash scripts/scoped-builder.sh --out /tmp/alvoki-scoped-builder.csv
python3 benchmarks/scoped_builder.py --summarize /tmp/alvoki-scoped-builder.csv
```

- [Raw trials](../../benchmarks/results/packed/scoped-builder-trials.csv)
- [Summary](../../benchmarks/results/packed/scoped-builder-summary.csv)
- [Assembly excerpts](../../benchmarks/results/packed/scoped-builder-codegen.txt)
- [VM environment](../../benchmarks/results/packed/scoped-builder-environment.txt)
