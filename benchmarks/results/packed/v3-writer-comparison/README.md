# V3 writer comparison in mixed execution order

Medians in milliseconds at one million total input rows. Each result uses nine timings from three processes in deterministically shuffled order. Each process discards its first timing. The materialization modes are checked byte for byte against the Python oracle. Every pipeline time includes parsing the output and reading one snapshot, and checks the independent snapshot checksum.

| Workload | Best stock Lean writer | Guarded fixed rows | Stock cursor copy | Scoped C rows | Existing Rust rows | Stock pipeline | Scoped C row pipeline | Existing Rust row pipeline |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Range ingest | 6.026 | 4.262 | 14.850 | 1.978 | 3.094 | 9.185 | 4.635 | 5.969 |
| Hot updates | 6.417 | 5.019 | 15.059 | 2.525 | 3.732 | 8.832 | 4.982 | 6.503 |
| Delete and reinsert | 6.247 | 5.036 | 15.195 | 2.590 | 3.758 | 9.196 | 5.511 | 6.943 |
| Uniform mix | 11.902 | 9.329 | 25.513 | 4.784 | 6.953 | 17.317 | 8.423 | 10.169 |

The cursor uses two selection passes and initializes an exact-sized buffer. The scoped C writer reserves a private allocation and selects and copies in one pass. Its row loop was faster than its span loop and the conditional-move row loop in this cohort. Rust uses the existing reserved `Vec` writer. Some Rust trials had large outliers, so the raw samples are useful for interpreting the ratios. These comparisons concern the tested algorithms and their allocation and runtime choices on this VM. [Raw timing rows](trials.csv) · [Scoped experiment](../scoped-v3) · [Cursor experiment](../stock-v3-cursor)

## Reproduce

The run used CPU 0 on Linux 6.18.57 x86-64 under KVM on an AMD EPYC 9V74. Lean 4.36.0 Release at `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`, bundled Clang 23.1.1, Rust 1.100.0, and Python 3.12.14 were used. The measured scoped and cursor binaries were built from the corresponding experiment patches on `d29eb1a` with the same v3 workload generator.

```sh
bash scripts/scoped-compaction.sh --pipeline-rows
bash scripts/stock-v3-cursor.sh --sizes 1031 --trials 1 --out /tmp/v3-cursor-smoke.csv

lean_bin=lean/.lake/build/bin/alvoki-compaction
rust_bin=rust/target/release/alvoki-compaction
taskset -c 0 python3 benchmarks/results/packed/v3-writer-comparison/compare.py . /tmp/v3-writer-trials.csv \
  --case stock-rows "$lean_bin" rows \
  --case stock-spans "$lean_bin" spans \
  --case stock-pipeline "$lean_bin" pipeline \
  --case fixed-rows "$lean_bin-fixed" rows \
  --case fixed-spans "$lean_bin-fixed" spans \
  --case fixed-pipeline "$lean_bin-fixed" pipeline \
  --case rust-rows "$rust_bin" rows \
  --case rust-spans "$rust_bin" spans \
  --case rust-row-pipeline "$rust_bin" pipeline-rows \
  --case rust-span-pipeline "$rust_bin" pipeline \
  --case scoped-rows "$lean_bin-scoped" rows \
  --case scoped-spans "$lean_bin-scoped" spans \
  --case scoped-row-pipeline "$lean_bin-scoped" pipeline-rows \
  --case scoped-span-pipeline "$lean_bin-scoped" pipeline \
  --case cmov-rows "$lean_bin-scoped-branchless" rows \
  --case cmov-spans "$lean_bin-scoped-branchless" spans \
  --case cmov-row-pipeline "$lean_bin-scoped-branchless" pipeline-rows \
  --case cmov-span-pipeline "$lean_bin-scoped-branchless" pipeline \
  --case cursor-copy "$lean_bin-cursor" cursor-copy \
  --case cursor-store "$lean_bin-cursor" cursor-store \
  --case cursor-pipeline "$lean_bin-cursor" cursor-pipeline
```
