# Fixed-width packed copy

Inlining a checked fixed-width copy cut alternating merge from 8.07 to 4.94 ms on the VM. The same experiment reduced merge followed by validation, a full scan and 20,000 lookups from 12.79 to 9.80 ms. Rust took 2.56 and 7.72 ms respectively.

## Copy-width sweep

The table reports median milliseconds for 1,024,000 output records, from nine timed trials. Each row copies the same bytes in the same order. The trace groups consecutive winners into fixed-size copies within 256-record spans. Allocation and initialization of the unique destination happen outside the timer for this sweep.

| Copy width | Stock Lean | Runtime wrapper | Inlined fast path | Rust |
|---|---:|---:|---:|---:|
| 16 bytes | 7.53 | 4.35 | 4.11 | 0.72 |
| 32 bytes | 3.73 | 2.86 | 2.23 | 0.63 |
| 64 bytes | 1.82 | 1.28 | 1.18 | 0.59 |
| 4,096 bytes | 1.56 | 1.57 | 1.59 | 0.74 |

The 4 KiB control always uses the generic runtime copy. Rust uses a const-generic slice-copy loop. Increasing width from 16 to 64 bytes reduces trace steps and copy calls by four. The widest small copy roughly halves the inlined Lean gap against Rust on a relative basis.

## Alternating runs and packed reads

These workloads choose or replay one winner at a time. Fused merge and replay allocate output within their timed regions. The pipeline includes merge, validation of the resulting block, scanning all records, and the shared mixed lookup batch.

| Workload | Stock Lean | Runtime wrapper | Inlined fast path | Rust |
|---|---:|---:|---:|---:|
| 16-byte replay, pre-sized output | 7.12 | 4.43 | 3.93 | 0.87 |
| 16-byte replay, append to fresh output | 7.30 | 4.85 | 3.56 | 1.29 |
| Fused merge | 8.07 | 6.10 | 4.94 | 2.56 |
| Full packed pipeline | 12.79 | 11.12 | 9.80 | 7.72 |

The wrapper bypasses generic offset conversion, capacity growth, and copy-on-write on in-bounds, unique, sufficiently sized destinations. Clang emits vector loads and stores for the fixed lengths. The generated-code variant additionally inlines the guard and copy into the emitted C of the two relevant Lean modules. The remaining guard includes scalar offset recognition, source bounds, destination capacity, and exclusivity. The timing difference between wrapper and inline includes compiler optimizations enabled by inlining. It does not isolate call latency.

Both experiments use the existing Lean `ByteArray.copySlice` operation and the same Lean application code. The C prototype changes how that existing runtime entry point is compiled for the benchmark binaries. It relies on the pinned Lean runtime representation and is outside the verified source-level model. Stock binaries and the project toolchain use the original entry point. Every unsupported case falls back to it.

The contract tests compare runtime copies to a reference built with Lean array operations. They cover unaligned widths, overwrite, append, growth, shared and aliased destinations, and clipped offsets. All four binaries produced exact output on every measured merge and copy fixture, and every measured pipeline checksum matched the Python oracle. Existing proof and phase reproduction checks also passed. A full runtime refinement proof remains open.

The remaining gap is largest for 16-byte emission. A focused next prototype could establish ownership and bounds once for an entire builder loop, then compare that with the guarded inline path. The 64-byte result gives a practical option when consecutive winners can be batched.

```sh
bash scripts/fixed-copy.sh --out /tmp/alvoki-fixed-copy.csv
python3 benchmarks/fixed_copy.py --summarize /tmp/alvoki-fixed-copy.csv
objdump -d --disassemble=__wrap_lean_byte_array_copy_slice lean/.lake/build/bin/alvoki-merge-phases-fixed
```

- [Raw trials](../benchmarks/results/packed/fixed-copy-trials.csv)
- [Summary](../benchmarks/results/packed/fixed-copy-summary.csv)
- [VM environment](../benchmarks/results/packed/fixed-copy-environment.txt)
- [Stock Lean runtime source](https://github.com/leanprover/lean4/blob/v4.36.0/src/runtime/object.cpp)
