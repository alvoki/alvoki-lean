# Proved packed builder on stock Lean

The append-only builder and replay integration compile on the pinned, unmodified Lean 4.36.0 toolchain. The experiment links the normal Lean runtime. It uses the stock `ByteArray.copySlice` primitive, and batches contiguous source spans to amortize that primitive where the input permits it.

## Byte contract

`ScopedBytes.Slice` carries proof that its start and length fit in the source. The builder holds its destination privately while clients append, and returns an ordinary immutable `ByteArray` in `finish`. The capacity parameter is a hint. The API allows the usual Lean value semantics, including using a shared prefix, so it does not assert exclusive runtime ownership.

- `append_refines`, `append_keeps_byte`, and `append_source_byte` establish exact source bytes, prefix preservation, and byte position. `append_size` establishes the resulting length.
- `appendAll_refines` identifies the finished bytes as the original prefix followed by the concatenation of the slices in order. `adjacent_model` proves that combining adjacent source extents preserves their concatenated bytes.
- `replayWrite_refines` covers the executable streaming writer from header through its final bytes. The payload model follows the supplied winner trace. Correct trace generation from the sorted runs is a separate property.
- `prepared_write_refines` covers the prepared writer for its supplied slices. `prepared_payload_size` establishes the total payload length from the prepared plan's checked length invariant. The planner and online coalescer were tested against the independent byte oracle. An end-to-end proof that their slices match the winner trace remains open.

These proofs check the Lean source and rely on the usual implementation of stock Lean primitives. The axiom audit found only standard Lean axioms. The separate `leanchecker` run passed.

## Performance

Medians at one million total input records on the pinned VM, nine trials per case. Timing includes writing the output but excludes loading and validating runs and the trace. Prepared emission excludes building its array of span descriptors. The prepare-and-emit variant measures that cost as well. All durations are in milliseconds.

| Input profile | Spans | Lean per-record | Lean online coalescing | Lean prepared emit | Lean prepare and emit | Rust scoped control |
|---|---:|---:|---:|---:|---:|---:|
| Alternating | 1,000,000 | 6.94 | 7.60 | 6.64 | 40.57 | 1.26 |
| Clustered ranges | 1,399 | 7.48 | 1.55 | 0.76 | 9.73 | 1.19 |
| Shuffled interleave | 500,245 | 11.28 | 13.98 | 5.38 | 32.87 | 1.19 |
| Update-heavy | 187,673 | 6.75 | 4.84 | 2.06 | 14.79 | 0.82 |

The clustered case benefits most. Online coalescing is 4.8× faster than emitting records individually and takes about 30% longer than the tuned Rust per-record control. Prepared emission uses just 1,399 copies, so it beats that per-record Rust control once the plan exists. Counting plan construction reverses the result. The Rust control was not supplied a matching coalesced plan.

Online coalescing avoids allocating a separate plan array. It checks the next winner before constructing span state, which keeps singleton-heavy inputs from paying for a descriptor on every record. It still incurs trace checks, and the shuffled profile remains faster with plain streaming unless the spans are already prepared. These are synthetic workload profiles with precomputed winner traces. They measure record emission, not fused online merge selection.

The generated C passes the builder's underlying byte array directly and calls the stock `lean_byte_array_copy_slice` for every emitted record or span. Even proofs that erase in native code leave the stock runtime's dynamic ownership and capacity path in place. On alternating inputs the best stock emitter took 5.3× the tuned Rust control. Closing that gap still calls for a standard-runtime or compiler specialization that can exploit a private destination across many writes. The current API and byte-level proof provide the reference contract for such work.

## Reproduce

```sh
bash scripts/stock-builder.sh --out /tmp/alvoki-stock-builder.csv
python3 benchmarks/stock_builder.py --summarize /tmp/alvoki-stock-builder.csv
```

Eight exact output fixtures, five malformed trace fixtures, and exact comparisons on all benchmark inputs passed. Existing reproduction, Verus, merge-phase, and prior runtime experiment fixture suites also passed.

- [Raw runs](../benchmarks/stock-builder-trials.csv)
- [Summary](../benchmarks/stock-builder-summary.csv)
- [VM environment](../benchmarks/stock-builder-environment.txt)
