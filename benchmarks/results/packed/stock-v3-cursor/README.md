# Exact-size v3 cursors on stock Lean

The exact-size cursor sped up fresh v3 encoding by 4.59–5.27× over append encoding at 666,666 input rows. Exact-size compaction was slower than either one-pass append or span coalescing. Both variants run on the pinned stock Lean compiler and runtime.

## Fresh encoding

All three encoders start with owned decoded rows. The harness decodes and validates the input outside the timer. Lean uses an Array of v3 records and Rust uses a Vec of four-word arrays. The compared output includes the count and version header and 32-byte rows. The cursor times include allocating and initializing the full destination. It widens the initialized length using a separate shared 4 KiB zero chunk, then overwrites the header and rows. The machine-index loop derives four word extents from a single row bound and the exact initial size. The append baseline uses the existing `appendV3Row` codec. Rust reserves capacity and appends the four words. [Cursor executable](../../../../lean/Alvoki/Bench/Compaction/CompactionCursorMain.lean) · [Existing codec](../../../../lean/Alvoki/Compaction/Codec.lean) · [Rust control](../../../../rust/src/bin/alvoki-compaction.rs)

Medians in milliseconds for the left input of the one-million-row compaction datasets.

| Dataset | Lean append | Lean cursor | Rust | Cursor / Rust |
|---|---:|---:|---:|---:|
| Range ingest | 38.892 | 8.480 | 1.854 | 4.57× |
| Hot updates | 38.510 | 8.325 | 1.909 | 4.36× |
| Delete and reinsert | 44.320 | 8.513 | 1.955 | 4.35× |
| Uniform mix | 45.259 | 8.594 | 3.018 | 2.85× |

The generated C uses 32 scalar `uset` calls per row. Clang inlines those calls and the native loop contains 32 static call sites on its copy-on-write slow paths. The smaller gap than append includes the avoided per-byte size and capacity growth work. The call sites describe possible copies when the buffer is shared. [Code generation](codegen.txt)

### Encoding from a list

The paired Lean follow-up starts with a prebuilt `List RawEntry`. Both variants count its length inside the timer. The append control reserves the full capacity. The cursor initializes the exact destination, writes the header and traverses the list with the same bounds-checked row writer. Production flush starts from an encoded header and grows the buffer as it converts logical entries to v3 fields. It then validates the encoded run. [Flush path](../../../../lean/Alvoki/Storage/Table/CompactionRead.lean)

Medians in milliseconds at 666,666 rows.

| Dataset | List append | List cursor | Speedup |
|---|---:|---:|---:|
| Range ingest | 34.766 | 10.341 | 3.36× |
| Hot updates | 35.399 | 9.538 | 3.71× |
| Delete and reinsert | 34.707 | 9.525 | 3.64× |
| Uniform mix | 34.905 | 9.985 | 3.50× |

In emitted C both encode entry points call `List.lengthTR` before their allocation and writing loops. The same exact-output fixtures, truncated input check and timed dataset checks passed for both encoders. [List samples](list-trials.csv) · [List summary](list-summary.txt)

## Compaction and the full pipeline

Both cursor compactors use the existing selector to count the retained rows and use it again to emit. Every time includes the count, allocation, destination initialization, header and emission. One candidate uses indexed `copySlice` to copy whole packed rows. The other stores the four words in a row after a shared destination extent check. The existing span writer serves as the fallback if the exact extent exceeds the machine cursor range or emission ends at an unexpected cursor. The full pipeline uses the copy candidate and includes validating and scanning the output.

| Dataset | Best stock Lean compaction | Cursor copy | Cursor stores | Best Rust compaction | Lean span pipeline | Cursor copy pipeline | Rust span pipeline |
|---|---:|---:|---:|---:|---:|---:|---:|
| Range ingest | 6.456 | 15.840 | 35.154 | 3.101 | 9.569 | 18.166 | 7.072 |
| Hot updates | 6.160 | 15.499 | 29.962 | 4.603 | 8.729 | 17.392 | 7.145 |
| Delete and reinsert | 7.555 | 16.295 | 32.280 | 3.884 | 11.096 | 17.903 | 8.942 |
| Uniform mix | 11.924 | 23.918 | 39.202 | 10.102 | 17.594 | 27.135 | 14.071 |

The exact-size approach fits encoding with a known row count. The compactor pays for a second selection pass and initializes the output before copying rows already available as bytes. It lands at 2.01–2.52× the best stock Lean writer here. Those aggregate times combine the three costs.

Lean checks the cursor's byte bounds, destination size invariants, and termination. Differential checks cover complete output equality on the 15 edge fixtures and every timed dataset plus snapshot scan totals and truncated input rejection. The existing codec proofs specify the bytes. Full equality of the experimental cursor with the codec remains a separate proof obligation. [Raw timings](trials.csv) · [Summary](summary.txt) · [Reproduction](environment.txt)
