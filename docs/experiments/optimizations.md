# Native Lean optimization results

The optimized Lean path reached approximately the same throughput as the matching Rust implementation for packed random lookups, scans, streaming decode, and validation on this VM. Owned decode and block encoding still have substantial gaps. The optimized path uses Lean and its standard runtime, with Rust as the separate wide-load and wide-store control.

## One million records, interleaved layout

Each value is the median of nine timed trials. The Rust query baseline in this table uses the same strided view as the optimized Lean implementation.

| Workload | Original Lean algorithm | Best Lean variant | Rust | Best Lean / Rust elapsed time |
|---|---:|---:|---:|---:|
| Mixed random lookup | 500 ns | 173 ns | 182 ns | 0.95× |
| Sequential lookup | 325 ns | 46.4 ns | 36.3 ns | 1.28× |
| Small range | 1,089 ns¹ | 283 ns | 298 ns | 0.95× |
| Large range | 36.43 µs¹ | 2.07 µs | 2.15 µs | 0.97× |
| Validate one block | 15.66 ms | 0.447 ms | 0.544 ms | 0.82× |
| Decode and fold, retaining records through the fold | 38.17 ms | 9.97 ms | 1.19 ms | 8.4× |
| Stream and fold | 14.66 ms | 0.919 ms | 0.873 ms | 1.05× |
| Strided unaligned word load and sum | 7.83 ns | 0.457 ns | 0.211 ns | 2.17× |
| Encode one block | 51.91 ms | 14.07 ms | 1.24 ms | 11.4× |

¹ Original Lean range figures are from the first experiment. The Rust and optimized Lean range figures were collected in the same optimization run. At 100,000 records, the optimized Lean short range took 228 ns versus Rust's 196 ns. Treat small wins and losses as VM measurements.

## What each experiment showed

1. **Scalar-field owned records.** The generated C allocates one record with 16 bytes of inline scalar payload. Compared with the original boxed pairs, the representation alone reduced decode and fold from 38.17 ms to 23.56 ms and peak process RSS from 101 to 68 MiB. Machine-sized reads reduced the time to 9.97 ms. Rust's owned path used about 32 MiB.
2. **Streaming decode.** The scalar tail loop decodes and folds directly from the packed block. It ran in 0.919 ms with peak process RSS of 24.5 MiB. Rust performed the same streaming workload in 0.873 ms with about 16.3 MiB of peak process RSS.
3. **Carry the previous key during validation.** Removing the repeated key read reduced the baseline from 15.66 ms to 12.88 ms. Using machine-sized offsets, native word loads, and a scalar tail-recursive loop together reduced it to 0.447 ms.
4. **Specialize search.** For mixed random lookups, the generic Nat search took 500 ns. Specializing the comparator with Nat indices took 368 ns. Machine arithmetic with the legacy reader took 371 ns. Machine arithmetic with the optimized reader took 173 ns. An exploratory imperative loop lowered to managed loop state, so the timed machine-index variant uses terminating tail recursion. With all changes together, mixed random lookups were within 5% of the layout-matched Rust control at 1,000, 100,000, and 1,000,000 records.
5. **Use fixed-offset loads and stores.** Proof-carrying byte loads with explicit offsets compile to a single 64-bit memory instruction on the hot x86-64 path. Benchmarking the fixed-width byte accesses with a scalar loop reduced the unaligned word workload from 7.83 to 0.457 ns per word. For writes, unrolling the append loop yielded 24.82 ms per block. Pre-sizing the output and overwriting its bytes with proven machine indices reduced the result to 14.07 ms. Rust writes contiguous records in 1.24 ms. The indexed Lean encoder includes zero initialization and retains per-byte writes with runtime uniqueness handling. The test oracle checks its full output against the exact version 1 fixture.
6. **Pack the key and value columns separately.** At one million records, this layout moved Lean mixed lookup from 173 to 157 ns and short scans from 283 to 269 ns. Rust also improved, from 182 to 162 ns and 298 to 279 ns. For sequential lookup, Lean's result was 47.1 ns with columns and 46.4 ns interleaved. Both layouts supported near-parity on several packed workloads in this run. The interleaved format remains usable with the optimized path.

## What was measured

The suite pins a CPU, randomizes variant process order with a fixed seed, preloads deterministic inputs, and discards one warm-up per process. Query units are queries. Bulk-work units in the CSV summary are records. Whole-block values above multiply by one million. RSS is Linux process high-water memory, including runtime and buffers. The validation timer reads the Lean input through an IO reference on each iteration to prevent reusing an earlier pure result. An exploratory measurement without this control was discarded.

Both language implementations check both layouts against a Python oracle that covers full-width keys, empty and singleton blocks, invalid headers and lengths, out-of-order and duplicate keys, and three range widths. The fixture checks cover the individual experimental paths and compare the new encoders' bytes exactly. The prior benchmark and proof suite also passed. Lean's bundled checker rechecked the fixed-width lower-bound refinement and in-bounds word equivalence. The layout parser and indexed full-block encoder still need end-to-end refinement proofs.

The large-range Rust control folds over the layout view directly. Its 2.15 µs result is the matched comparison for the optimized Lean fold. The original Rust binary took 5.02 µs on the same workload. Neither allocator event counts nor hardware counters are recorded here. The remaining priorities are an owned packed or chunked representation and a bulk byte-writing primitive with a refinement contract.

```sh
bash scripts/optimize.sh --out /tmp/alvoki-opt-trials.csv --trials 9
python3 benchmarks/optimize.py --summarize /tmp/alvoki-opt-trials.csv
rg -n 'lean_ctor_set_uint64|lean_byte_array_uget' lean/.lake/build/ir/Alvoki/Experiments/Packed/Optimizations.c
objdump -d --disassemble=lp_alvoki_Alvoki_Opt_View_readUnaligned lean/.lake/build/bin/alvoki-opt
```

- [Raw measurements](../../benchmarks/results/packed/optimization-trials.csv)
- [Summary](../../benchmarks/results/packed/optimization-summary.csv)
- [VM environment](../../benchmarks/results/packed/optimization-environment.txt)
- [Verification scope](../verification-status.md#optimized-reader-and-search)
