# Where time goes in packed merge

Replaying the same winner decisions into a fresh packed block is about 4.2–4.6× slower in Lean than in Rust at one million input records. Online selection with a checksum is within 18% of Rust on the same workloads. This makes the short packed output path the first target. Custom C is absent from the Lean benchmark binary.

## Timings

Median of nine trials on the pinned KVM guest. Each cell is Lean / Rust in milliseconds for one million total input records. The collision-heavy case has 375,000 shared keys and emits 625,000 records. The other two cases emit one million.

| Input pattern | Select and checksum | Replay and checksum | Replay and write | Fused per-record merge |
|---|---:|---:|---:|---:|
| Perfect alternation | 2.03 / 1.72 | 1.46 / 1.17 | 6.98 / 1.67 | 7.72 / 2.68 |
| Mixed short and long spans | 2.07 / 2.11 | 1.61 / 1.16 | 6.92 / 1.56 | 8.02 / 3.75 |
| Collision-heavy | 1.15 / 1.08 | 0.93 / 0.73 | 4.46 / 0.96 | 4.06 / 2.14 |

The selector compares heads and consumes each winning key and value in a wrapping, order-sensitive checksum. The two replay modes use the same precomputed one-byte-per-output trace. The checksum replay controls for reading the trace and advancing its cursors. The write replay allocates a fresh output, writes the known count, and emits one 16-byte record per decision. The fused merge chooses winners online and can copy the entire remaining input tail in bulk. The fused column uses the simple per-record algorithm for both implementations throughout, including mixed spans.

The phase times are separate workloads. They differ in their memory traffic, output work, and state. In particular, replay writes tail records individually. This explains why Lean replay can exceed the fused collision-heavy time even with precomputed winners. In the first exploratory run, an indirect call survived in Lean's generic replay and moving the vector accumulator through the Rust callback distorted the comparison. The reported runs use separate Lean scalar loops and an in-place, monomorphized Rust replay. Generated Lean C shows a direct copy-slice runtime call per emitted record, without the indirect emitter call.

## Which experiment comes next

1. **Measure fixed-width emission over the same traces.** Add a small 16-byte record-copy benchmark with controlled copy lengths and the same preallocated output in Lean and Rust. Include a 16/32/64-byte width sweep and a bulk-span control. Inspect the native call boundary and repeated runtime checks. If the standard ByteArray API still routes the fast path through generic slice machinery, try a constant-length specialization in the Lean compiler or standard runtime with a byte-level contract. The earlier full-word update results suggest the same effort could help both merge and encoding.
2. **Measure merge followed by real reads once there is a faster emitter.** Compare merge into packed output followed by identical lookups and scans with a pipeline that materializes records. This measures how often the improved writer and existing packed read paths pay off together.
3. **Defer selector tuning.** There is a measurable alternating-input selection gap and a trace-walk gap. Their absolute costs are smaller than the write-replay gap here. Revisit them after shrinking emission cost.

## Correctness and reproduction

The Python sorted-union oracle creates the trace and expected output independently. The trace distinguishes left, right, and collision where the right value wins. Input parsing and trace validation happen outside the timer. The reader checks trace cursor bounds and complete consumption. The benchmark oracle supplies semantic validity, including which collision keys match. Lean checks bounds on reads of the trace and loop termination. No full merge refinement is claimed.

Eleven fixtures check both checksums and exact output bytes, including empty inputs and full-width keys. Five malformed traces are rejected. Each measured workload at each size was also checked byte for byte in both writer modes before timing. The original reproduction and proof checks passed. Raw timings contain 648 samples across three sizes and three input patterns. Process RSS was not collected in this round.

```sh
bash scripts/merge-phases.sh --out /tmp/alvoki-merge-phases.csv
python3 benchmarks/merge_phases.py --summarize /tmp/alvoki-merge-phases.csv
```

- [Raw timings](../benchmarks/merge-phases-trials.csv)
- [Summary](../benchmarks/merge-phases-summary.csv)
- [VM environment](../benchmarks/merge-phases-environment.txt)
