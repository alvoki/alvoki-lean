# ALVSST06 Bloom placement experiment

The experiment starts at `40a19ddf`. It uses Lean 4.36.0 in release mode, Linux
6.18.57, x86-64 AMD EPYC 9V74, overlayfs and GCC 14.2.0. CPU 2 was pinned.
The fixture generates ordered keys and values with the sizes from the
[original filter benchmark](bloom.md). Every seventh fixture value contains
a zero tombstone marker. The lookup oracle requires that value to be returned
on a hit. Each isolated mask build also checks every inserted key.

```sh
(cd lean && lake build bloomPlacementCheck)
(cd lean && lake env leanchecker Alvoki.Checks.Benchmarks.BloomWord)
taskset -c 2 lean/.lake/build/bin/bloomPlacementCheck --placements 65537
taskset -c 2 lean/.lake/build/bin/bloomPlacementCheck --placements 1048577
taskset -c 2 lean/.lake/build/bin/bloomPlacementCheck --profile 12
```

## Complete table probes

The fixture runs 4,096 hits, 4,096 uniformly distributed in-range misses and
4,096 in-range misses in runs of 64 probes to one coarse partition. Query
results are checked across every placement. The two baseline placements
read native ALVSST06 files and call their current lookup APIs. The other
placements use the same base table and Bloom algorithm. The leaf placement
projects an appended mask onto each leaf packet, counts its bytes and checks
that the enlarged packet fits a single request. Its reader still reads the
original leaf and consults the fixture's mask. The coarse and table placements
read a temporary sidecar of checksummed filter packets through positional
I/O. Their directory is preassembled and retained. The CSV includes the
estimated bytes of serializing that directory with ALVSST06 references.
The sidecar loader must return the checksum or positional-read error when
injected at the mask for a known tombstone.

The counts below include all positional requests after open for each miss.
Open requests are reported separately in the raw data. Bytes are requested
lengths, including projected attached mask bytes. Leaf packing, decoding cost,
cache policy and full lookup latency require measurements on any future
physical implementation.
[65,537-row samples](bloom-placement-small.csv) ·
[1,048,577-row samples](bloom-placement-large.csv)

| Rows | Layout | Data / index target | Height | No filter | Data-block packet | Leaf attached | 16K rows on disk | 16K rows one cached | 16K rows all cached | Table cached |
| ---: | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 65,537 | Fixed / fixed | 4 / 1 KiB | 2 | 2.000 | 2.008 | 1.008 | 1.015 | 0.750 | 0.015 | 0.022 |
| 65,537 | Fixed / fixed | 16 / 16 KiB | 1 | 1.000 | 1.010 | 0.011 | 1.007 | 0.742 | 0.007 | 0.011 |
| 65,537 | Variable / variable | 4 / 1 KiB | 3 | 3.000 | 3.008 | 2.009 | 1.031 | 0.766 | 0.031 | 0.029 |
| 65,537 | Variable / variable | 16 / 16 KiB | 1 | 1.000 | 1.005 | 0.010 | 1.010 | 0.745 | 0.010 | 0.010 |
| 1,048,577 | Fixed / fixed | 4 / 1 KiB | 3 | 3.000 | 3.009 | 2.007 | 1.016 | 0.998 | 0.016 | 0.026 |
| 1,048,577 | Fixed / fixed | 16 / 16 KiB | 2 | 2.000 | 2.007 | 1.007 | 1.011 | 0.992 | 0.011 | 0.017 |
| 1,048,577 | Variable / variable | 4 / 1 KiB | 4 | 4.000 | 4.007 | 3.009 | 1.019 | 1.000 | 0.019 | 0.047 |
| 1,048,577 | Variable / variable | 16 / 16 KiB | 2 | 2.000 | 2.007 | 1.008 | 1.009 | 0.991 | 0.009 | 0.023 |

- The current block mask reduces bytes per miss by replacing a data packet
  with a smaller filter packet. A false positive follows the filter read
  with the original data read, increasing the average number of requests.
  Each hit adds one read.
- The attached mask avoids the data read on a negative and adds no hit
  request. With a one-level index the mask is loaded with the root at open.
  On the million-row fixed-width default case, the number of miss reads
  falls from 2.000 to 1.007 while requested bytes rise from 31.95 to
  441.18 KiB. Counting mask bytes against the packet target in a format
  would change packing and could change index height.
- A separate on-demand 16,384-row mask rejects before index descent.
  Its miss transfer is about 20 KiB and hits add one read. This saves
  bytes on the million-row default cases, where the base miss reads
  about 32 KiB. With 4 / 1 KiB targets, the base reads about 6–7 KiB
  at that table size.
- Keeping the latest checked coarse mask uses up to 20 KiB of mask payload.
  In the million-row fixture it issues 4,020 mask reads for 4,096 uniform
  queries and 64 for 4,096 clustered misses. Including index and data
  requests, clustered misses use 0.034–0.053 reads each across the four
  million-row cases. The directory and cache objects occupy additional space.
- Eager table-level and coarse masks both retain about 80 KiB for 65,537
  rows and about 1.25 MiB for 1,048,577 rows. The latter adds one mask read
  at open for table-level placement and 65 for coarse placement, with
  similar bytes. Hits keep the base table's request count after open.
  Opening a table solely for a few negative probes can cost more than
  probing it without any filter.

## Construction profile

Each phase measures three runs of 12 rounds on 65,536 keys. The timer
for a completed mask includes a small checksum. The benchmark fetches its
input through an effect each round to keep pure work inside the timer.
Probe planning and preplanned updates are isolated measurements with
different memory traffic. Their times should be read as diagnostics.
The prototype compares exact hash values, probe positions and mask bytes
against the existing implementation on all fixture keys.
[Raw profile samples](bloom-construction-profile.csv)

The current generated C materializes an `Array` from each packed key
through `lean_byte_array_data`. It also converts each full-width hash to
`Nat` before modulo, allocating for hashes outside the scalar range, and
builds a list of seven positions per inserted key. The profile tries a
packed byte fold and moving the remainder ahead of the conversion.
The packed-word build also iterates the seven probes without collecting
a separate list. It still updates the mask with the existing bitset
primitive. These are experiments with the current hash and encoding.

Median nanoseconds per inserted key.

| Layout | Rows per mask | Hash from copied array | Hash from packed bytes | Current probe planning | Word probe planning | Preplanned bitset | Current complete mask | Packed-word mask |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Fixed / fixed | 128 | 28 | 12 | 824 | 104 | 413 | 1103 | 422 |
| Fixed / fixed | 16,384 | 28 | 12 | 613 | 102 | 400 | 1081 | 443 |
| Variable / variable | 128 | 35 | 14 | 636 | 110 | 402 | 1057 | 420 |
| Variable / variable | 16,384 | 34 | 14 | 618 | 109 | 403 | 1029 | 417 |

The native construction samples include streaming append and flush and
exclude fsync. The supplier takes entries from a pregenerated array.
In these single samples, unfiltered construction took 0.10–0.21 µs per row
and the current block-filter build took 1.13–1.50 µs. Alternative placement
samples took 1.02–1.13 µs per row to construct masks and
for the sidecar, compute CRCs, write and flush. They use fixture slices with
known lengths. They establish neither the memory cost of a production
streaming supplier of unknown size nor the end-to-end build latency of
a proposed format.

## Production proof boundary

The measurements support trying bounded machine-word probe arithmetic
before changing the membership algorithm. The experimental
`packedWordBuild_eq` proves equal serialized mask bytes for any input with
a fitting modulus. The proof composes the byte-fold equality, bounded
modulo equality and fused insertion fold. `packedWordBuild_covers` then
inherits the absence of false negatives for every row in that input.
The optimized constructor runs in the benchmark. The placement
measurements use the current constructor and checked packet reader.
[Lean mask equivalence](../../lean/Alvoki/Checks/Benchmarks/BloomWord.lean)

A table-level mask fits well for repeated negative probes at a small
table size. A coarse cache bounds mask memory per retained partition and
depends on access locality. Selecting a runtime placement needs a mixed
lookup workload and a budget for startup, retained bytes and cache lifetime.

For any selected placement the writer must establish the exact serialized
mask alongside the range of rows admitted from the streaming supplier.
The certificate needs to bind table identity, offsets and range metadata
to the same durable image that supplies the recursive references.
Coverage for all admitted entries includes tombstones. Lookup may skip
descent on a negative result only when the selected checked mask witness
covers the relevant range. A mask missing by design permits an ordinary
lookup. An advertised mask with a failed read or integrity check must
propagate that error. Cached masks require this same checked identity
on admission and retain it for the immutable descriptor lifetime.
These obligations extend the general recursive writer refinement.
[Recursive format and current filter obligations](../../docs/design/sstable-recursive.md)
