# Progress

The first VM experiment is implemented and reproducible. The benchmark uses version 1 blocks with sorted unique 64-bit keys and 64-bit values. Both Lean variants and Rust pass the same deterministic oracle checks and reject the malformed fixtures. The initial Lean and Verus proofs cover binary-search properties and Lean additionally proves one packed-word round trip. See the verification status for exact boundaries.

Raw timings, native build output, proof tool output and machine details are in `benchmarks/`. Use `bash scripts/reproduce.sh` to rerun the checks. Adding `--out /tmp/trials.csv` runs the benchmark again.

The next proof dependency is a parser invariant connecting adjacent packed keys to global strict order, plus a block-level codec theorem connecting both record loops. The largest performance gaps are validation and materializing decoded records. Separate scalar reads, managed-object creation, and search callback specialization before changing the format. The independent Lean4Lean binary reported an incompatible olean header. Lean's bundled `leanchecker` rechecked the proof module successfully.
