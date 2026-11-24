# Packed writer linearity

The diagnostic build marks the actual destination of each tested writer.
One marker covers each output buffer from its initial allocation through
replay, compaction, or overwrite. Lean 4.36 propagates the marker when
growing a unique scalar array and reports a panic when a mutation copies
a marked buffer because it is shared.
[Lean runtime](https://github.com/leanprover/lean4/blob/v4.36.0/src/runtime/object.cpp#L2596-L2683)

The native controls check unique overwrite and growth. They also keep an
old buffer alive across overwrite and growth to verify that both sharing
cases trigger the diagnostic. Without the flag, the same shared overwrite
preserves the old value and produces the new value.

Four v1 replay modes cover per-record writes, online spans, prepared
spans, and preparing plus writing. The v3 checks exercise row and span
compaction, including the final count patch. The dense rewrite writes
whole value words into a private copy and marks it before the first
overwrite. The existing fixtures and Python oracles check the finished
bytes and relevant snapshot checksums.

The 75 workload and mode combinations completed with exact output bytes
under `LEAN_ABORT_ON_NONLINEAR=1`. The marked destinations triggered no
copy-on-write diagnostic on these paths. All eight replay fixtures,
seven invalid trace fixtures, 15 compaction fixtures, and nine malformed
run fixtures also passed.

The marker tests for copy-on-write after initialization on these exercised
paths. Record copies from the input, capacity growth, the cost of dynamic
ownership checks, and allocations outside the marked buffer are distinct
costs. The command records case outcomes and output lengths.

## Reproduce

Run from the repository root with the pinned Lean toolchain installed.
The command builds a detached snapshot of the selected revision in a
temporary directory and applies the diagnostic patch there.

```sh
ALVOKI_LINEAR_REF=d29eb1a taskset -c 4 \
  bash benchmarks/results/packed/linearity/run.sh --out /tmp/alvoki-linear-cases.csv
```

Use `--sizes` to select input sizes. The recorded run used 1,000,
100,000, and 1,000,000 input records on Linux 6.18.57, AMD EPYC 9V74
under KVM, and Lean 4.36.0 Release at `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`.
[Exact cases](cases.csv) · [Native checks](checks.txt)
