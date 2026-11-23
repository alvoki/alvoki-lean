# Progress

The first VM experiment is implemented and reproducible. The benchmark uses version 1 blocks with sorted unique 64-bit keys and 64-bit values. Both Lean variants and Rust pass the same deterministic oracle checks and reject the malformed fixtures. The initial Lean and Verus proofs cover binary-search properties and Lean additionally proves one packed-word round trip. See the verification status for exact boundaries.

Raw timings, native build output, proof tool output and machine details are in `benchmarks/`. Use `bash scripts/reproduce.sh` to rerun the checks. Adding `--out /tmp/trials.csv` runs the benchmark again.

The next proof dependency is a parser invariant connecting adjacent packed keys to global strict order, plus a block-level codec theorem connecting both record loops. The largest performance gaps are validation and materializing decoded records. Separate scalar reads, managed-object creation, and search callback specialization before changing the format. The independent Lean4Lean binary reported an incompatible olean header. Lean's bundled `leanchecker` rechecked the proof module successfully.

## Native optimization round

The packed read path now has an experimental specialization using machine indices, unrolled proof-carrying reads, and scalar tail-recursive loops. It supports v1 interleaved blocks and a v2 columnar layout in the experiment binaries. The optimized search refines the original lower bound, and the optimized word reader agrees with the original reader on in-bounds inputs. Data, commands, and benchmark limitations are in the [optimization report](optimizations.md).

The main remaining gaps are allocation when materializing owned records and writing packed bytes. Continue refining the parser and view invariants before integrating the experimental path into the original block module.

## Packed ownership and writes

Version-1 packed ownership and 4 KiB chunks now have independent scan and lookup experiments. Direct packed merge passes exact right-biased union fixtures, and nonoverlapping inputs can copy entire payloads. A separate C-backed block encoder came close to Rust while the native indexed encoder retained a large gap. Keep the C code out of the native block paths. Follow up on contiguous spans in overlapping merge and a bulk byte-write API with a checked refinement contract. [Packed experiment results](packed-experiments.md)

## Native SIMD and output builders

Clang vectorizes the simple native Lean scan after an outer extent check. It matches the SIMD Rust scan on this VM. Span copies help longer runs and lose time on perfect alternation. Pair-wise extent checks improve fresh encoding, with a substantial gap still visible. Begin the next native round with short-span emission and eliminating repeated write-side uniqueness checks. [Native experiment results](native-experiments.md)

## Single-record emission and packed updates

The native suite now compares adaptive span gating, cached merge heads and pre-sized record copies. Adaptive gating preserves the mixed-span benefit and avoids most of the eager probe penalty on alternating runs. Copy-and-patch improves packed transforms, with results depending on how many bytes change. General value writes and alternating merge remain the largest measured gaps in these workloads. [Emission experiment results](emission-experiments.md)

## Merge phase isolation

A shared winner trace separates replay writes from online merge selection. At one million input records, Lean selection with checksum is within 18% of Rust, while replaying 16-byte writes takes roughly 4.2–4.6× Rust time. Prioritize a fixed-width emission microbenchmark and compiler or runtime specialization. [Phase isolation results](merge-phases.md)

## Fixed-width copy specialization

A checked runtime wrapper and a generated-code inline variant accelerate constant-width packed copies without changing Lean application code. Inlining reduced the alternating pipeline from 12.79 to 9.80 ms on the VM, with Rust at 7.72 ms. The remaining 16-byte gap motivates amortizing the ownership and extent checks across a builder loop. [Fixed-width copy results](fixed-copy.md)

## Scoped output

A separate runtime lowering fills an exclusively owned packed destination for an entire loop. The best scoped variant per workload was at most 8% slower than the fastest Rust control at one million inputs on all measured write and packed-pipeline cases. Stock Lean retains the write gap. The open engineering work is to expose an equivalent safe builder contract through the standard compiler or runtime and establish refinement. [Scoped builder results](scoped-builder.md)

## Proved stock Lean builder

Stock Lean now builds and checks an append-only packed builder, including exact prefix, source-byte, length, batch and streaming-replay contracts. Online span emission helps clustered traces, while alternating writes still spend one runtime slice-copy call per record and lag the Rust scoped control. The verified builder provides an implementation contract for future standard toolchain optimization. [Proof and benchmark results](stock-builder.md)
