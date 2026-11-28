# Recursive coarse Bloom filters and validated residency

The benchmark makes a second ALVSST06 tree for each data table. Its keys
are the inclusive upper fences of coarse partitions. Each value carries
the partition's first row ordinal and count, an optional exclusive lower
fence, and the packed Bloom mask. The companion writer buffers up to 16,384
keys and the preceding fence. It discards row values from that buffer and
builds the mask with the [proved-equivalent word constructor](../../lean/Alvoki/Checks/Benchmarks/BloomWord.lean).
The mask therefore includes keys of tombstones.

## Shared recursive structure

The companion uses the same builder, serialized references, page
promotion, checked open, extent and checksum validation, and lower-bound
descent as the data table. Its index reference ordinals count companion
entries. The base-table row range is metadata in the selected value.
There is no need for a Bloom caller to expose row-index routing. This
representation reuses the original `TreeInImage` as a tree over companion
entries. Decoding the value and proving mask coverage form an additional
leaf interpretation.

Both roots are already resident in the benchmark's open handles. A shared
physical directory could store one typed root address, height, extent and
identity for each independent tree and supply both roots from one
validated footer schedule. With a small companion, a flat directory of
coarse ranges can also keep one root permanently resident. With large
companions, a recursive directory has bounded fanout and supports the
same streaming promotion. A shared-file format still needs a proof that
the directory is emitted from the two actual roots, regions cover the
admitted input, and neither tree aliases another packet extent. The
experiment uses separate checked files so it can compare those read paths
before changing the format.

## Cache admission and reuse

A cache miss uses the ordinary checked recursive lookup to obtain the
packet and selected entry. The mask decoder checks the row extent, mask
length and lexical interval. A packed resident mask retains the entry
payload and byte offset and tests bits in place. A decoded mask retains
a copied mask slice. Both retain the already decoded fences. Once a
cached interval covers a query, the filter test carries out neither
positional I/O nor recursive packet validation. A positive filter result
continues through the base lookup API. A missing optional mask falls back
to ordinary lookup.

The latest policy keeps at most one mask within a caller-provided
payload budget. The eager policy traverses every companion packet once at
open and retains masks only within its budget. A budget excess aborts
that benchmark open. Both policies scope resident masks to the session
that holds the two read descriptions. For eager small tables, retaining
whole validated mask values saves an additional lookup and avoids
repeated CRC work. For large tables, the latest mask shows the gain
from reuse when multiple probes share a partition. The upper and leaf
index pages still take part in a cold companion lookup. Keeping checked
upper references could save the first nonresident index request and use
a relatively small additional budget. Keeping whole leaf packets helps
repeated accesses to different masks in that leaf. Mask residency can
skip the whole companion descent when its decoded interval matches.

## Four-table measurements

The release benchmark uses 64-bit fixed-width keys and values under Lean
4.36.0 on Linux 6.18.57, x86-64 AMD EPYC 9V74, overlayfs and GCC 14.2.0.
CPU 2 was pinned. The data index target is 1 KiB, and the data target is
4 KiB in both trees. Each workload probes four immutable tables newest
first, stopping on the first hit. Tables carry interleaved disjoint keys.
Every seventh stored value is a tombstone marker, which also stops the
probe. We measure the first query after opening, then 4,095 follow-ups.
Repeated misses use the same in-range key. Uniform misses sample the
whole key range. Recent and oldest hits measure one and four table probes,
respectively.

```sh
(cd lean && lake build coarseFilterCheck Alvoki.Checks.Benchmarks.CoarseFilterProofs)
(cd lean && lake env leanchecker Alvoki.Checks.Benchmarks.CoarseFilterProofs)
taskset -c 2 lean/.lake/build/bin/coarseFilterCheck 32769
taskset -c 2 lean/.lake/build/bin/coarseFilterCheck 1048577
```

| Rows/table | Mode | Startup | First repeat-miss key | Later repeated miss | Uniform miss | Oldest hit | Recent hit | Resident bytes |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 32,769 | plain | 8 | 8 | 8 | 8 | 8 | 2 | 0 |
| 32,769 | no-cache | 16 | 4 | 4 | 4.063 | 6.047 | 3 | 0 |
| 32,769 | decoded-latest | 16 | 4 | 0 | 1.960 | 3.944 | 2.474 | 81,952 |
| 32,769 | decoded-eager | 28 | 0 | 0 | 0.063 | 2.047 | 2 | 164,032 |
| 1,048,577 | plain | 8 | 12 | 12 | 12 | 12 | 3 | 0 |
| 1,048,577 | no-cache | 16 | 8 | 8 | 8.100 | 11.075 | 5 | 0 |
| 1,048,577 | decoded-latest | 16 | 8 | 0 | 7.951 | 10.927 | 4.963 | 81,984 |

Read counts add both trees' positional requests. Opening each tree
already loads and validates its root. The benchmark retains the
requested lengths and separates startup from query time. The native
captured timings include instrumentation and warm filesystem pages.
Amounts retained count mask bytes and fences across the four tables,
excluding Lean object headers and the two trees' resident roots.
[Three raw trials per size](coarse-filter-cache.csv)

The table reports median timings across the three trials. Startup and
first-miss times are single observations per trial, and follow-up
times are means per query within each trial.

| Rows/table | Mode | Startup (µs) | First miss (µs) | Repeated miss (µs) | Uniform miss (µs) | Recent hit (µs) |
| ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 32,769 | plain | 33.339 | 42.623 | 39.550 | 27.721 | 14.362 |
| 32,769 | no-cache | 82.593 | 52.629 | 26.259 | 35.013 | 16.521 |
| 32,769 | packed-latest | 78.075 | 59.408 | 4.554 | 19.718 | 11.455 |
| 32,769 | decoded-latest | 86.358 | 40.510 | 5.556 | 17.868 | 13.942 |
| 32,769 | packed-eager | 149.692 | 5.288 | 2.904 | 3.352 | 6.931 |
| 32,769 | decoded-eager | 137.414 | 7.030 | 2.582 | 3.485 | 9.732 |
| 1,048,577 | plain | 39.258 | 59.739 | 53.189 | 71.322 | 10.718 |
| 1,048,577 | no-cache | 104.715 | 132.246 | 45.930 | 57.143 | 29.672 |
| 1,048,577 | packed-latest | 79.858 | 82.303 | 4.717 | 65.945 | 23.655 |
| 1,048,577 | decoded-latest | 79.047 | 96.043 | 3.153 | 74.166 | 26.051 |

At 32,769 rows per table, the primary build took 0.262 µs per input row and the separate companion build took 0.914 µs per input row.
At 1,048,577 rows per table, the primary build took 0.370 µs per input row and the separate companion build took 1.030 µs per input row.

These build timings include independent supplier generation, tree
construction, writes and flushes. The benchmark omits fsync and does
not model the cost of a single admitted supplier feeding both trees.

Recent hits are sensitive to misses in the filter cache. In the large
case the latest policy still adds 1.963 companion reads per uniformly
distributed recent hit. Uniform negative probes avoid almost all primary
reads, but most still need both companion reads. Coarse placement is
most effective when a cacheable range is probed repeatedly. Packed
residency avoids a copy during admission and saves the same reads on
the repeat path as decoded residency. The samples do not establish a
consistent lookup-latency winner between the two representations.

## Proof boundary and integration

The kernel checks the serialized mask roundtrip, exact row-slice
binding and equivalence of packed-region bit tests to the ordinary
Bloom query. `load_checked` starts with the existing recursive
`Handle.Observes` for the companion image and retains the physical
reference, exact serialized row and decoded mask reached by lower-bound
routing. `openSession_latest_observes` initializes the session invariant
from the two checked source images and the wire contract.
`Session.Observes.probe` composes cold admission, base fallback and
resident lookup with the primary image. Each successful probe returns
the primary lookup for the same rows and preserves both source handles,
the session invariant and the byte budget. An interval mismatch is returned as an error.
The resident negative path is pure and retains the session. Separate
state-model theorems preserve the returned error and reached state of
a failed cold load or a failed primary lookup on any path that calls it.
Native fixtures exercise zero companion reads on a hit of an admitted
mask, correct tombstone lookup, rejection of a different table ID, and
propagation of injected positional-read and corruption errors.
[Kernel proofs](../../lean/Alvoki/Checks/Benchmarks/CoarseFilterProofs.lean)

The benchmark opens two copies of a deterministic streaming fixture.
The checked open compares table IDs and validates the separate images.
Equal IDs alone do not establish common origin for arbitrary native
files. The absence of false negatives is conditional on the exact
serialised mask and row-range binding to the primary writer's input,
including tombstone keys. Production still needs a general paired
producer proof establishing that binding from a single admitted
stream and preserving both roots at their durable locations. The eager
traversal has runtime coverage and uses the same checked value decoder.
Its whole-cache admission proof is a further step. A shared physical
directory and any production migration require separate review.
