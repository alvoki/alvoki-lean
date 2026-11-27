# Owned packed records, merge, and bulk writes

Retaining a validated packed block keeps Lean point lookups competitive. Copying packed bytes costs much less than materializing one object per record. A block-level C writer brought encoding from existing scalar records close to Rust on this VM. Direct native Lean merge is competitive for nonoverlapping runs when it can copy whole payloads. Overlapping runs still pay for per-record work.

## One million records

Medians of nine trials on the pinned KVM guest. Point lookup is a batch of 20,000 mixed queries. Merge consumes one million total input records, with the right value winning duplicate keys.

| Workload | Lean | Rust control |
|---|---:|---:|
| Retain packed buffer and scan | 0.831 ms | 0.220 ms |
| Copy packed buffer and scan | 1.781 ms | 1.110 ms |
| Materialize scalar records and scan | 9.659 ms | 1.152 ms |
| Build 4 KiB chunks and scan | 3.119 ms | 1.728 ms |
| Scan prebuilt 4 KiB chunks | 1.189 ms | 0.223 ms |
| Packed lookup batch | 3.319 ms | 3.528 ms |
| Alternating-run merge | 7.862 ms | 2.011 ms |
| Overlapping runs with collisions | 4.100 ms | 1.347 ms |
| Disjoint runs, bulk copy | 0.685 ms | 0.754 ms |

Merge times in the table use the same disjoint fast path in both languages and fall back to two-pointer merge on overlap. The alternating case is nearly 4× slower in Lean. Inspecting the implementations shows that Lean invokes the generic `ByteArray.copySlice` for each winning record. Rust's slice append is inlined. The disjoint Lean fast path calls `copySlice` twice and patches the count. Its corresponding per-record variant took 4.285 ms.

Rust's fixed-stride scan control uses SIMD instructions in generated code. This is a tighter comparison for sequential scans than the dynamic-stride Rust control in the previous experiment. The two-level Lean chunk lookup took 4.674 ms compared with 4.821 ms for searching a flat index over chunks. Both are slower than a single packed buffer in this workload. The chunk variants copy records from an existing packed block into one allocation per chunk and maintain an array of chunk references. They do not measure chunk splitting or mutation.

Process peak RSS for Lean was about 24 MiB for retaining the packed input, 40 MiB for copying it, 58 MiB for building chunks and scanning them, and 68 MiB for materializing scalar records. The retained case reuses an already-loaded, validated buffer.

## Words and batches

Each encoder starts with materialized records. The Rust control uses inline tuples in a contiguous vector. Lean's array points to individual scalar-field records.

| Operation | Lean native | Lean with C prototype | Rust |
|---|---:|---:|---:|
| Allocate and initialize zero buffer | 0.874 ms | 0.179 ms | 0.183 ms |
| Fill a preallocated buffer | 11.741 ms | 10.261 ms per-record call, 1.512 ms batched | 0.732 ms |
| Encode, including destination allocation | 13.429 ms | 8.929 ms per-record call, 1.510 ms batched | 1.361 ms |

Allocation and initialization are in the timed section for encoding and outside the timed section for filling. The batch encoder allocates once and writes every output byte before returning. Its preallocated counterpart checks size and handles copy-on-write once for the whole block. The per-record prototype performs those checks and crosses the language boundary once per record. Its assembly contains two 64-bit stores. The batched result shows that wide stores alone leave much of the overhead in place. The two C implementations also differ in whose loop traverses the records, so their difference is not a standalone estimate of call overhead.

The zero-buffer workload explicitly initializes the buffer in Lean and C. The Rust allocator can provide zero pages lazily. The initialization number is useful alongside the full encode and fill measurements and is not a hardware write-throughput comparison. Input parsing, record preparation, and benchmark output inspection are outside the timed sections. Process RSS includes those costs.

## Interface and verification boundary

- The pair-write reference function replaces exactly `[offset, offset+16)` with the little-endian key followed by the little-endian value. The buffer length and all other bytes are preserved. If the span does not fit, the whole buffer is returned unchanged.
- The batch-fill reference changes the full buffer into a version-1 block when its length is exactly `16 + 16*n`. A wrong-sized buffer is preserved. The batch encoder returns a new version-1 block. The encoders expect sorted unique keys when producing a valid block.
- The C prototypes use handwritten implementations of these Lean reference definitions. Tests exercise unaligned writes, alias preservation, out-of-bounds offsets including the largest machine index, and exact bytes from both encoders. The batched C code depends on the pinned compiler placing the two scalar fields at offsets 0 and 8 within the constructor's scalar payload. Generated C confirms that layout. The kernel does not verify the C implementation or those ABI assumptions.
- A merge returns the sorted union with the right-hand value at every collision. Tests compare complete files against a Python oracle for empty, disjoint, overlapping, fully overlapping, and randomized inputs. Lean checks termination of the native merge and scan loops. Full merge, chunking, and encoder refinement are open.

The most direct native work is to batch contiguous winner spans during overlapping merge and to explore a bounds-checked bulk write API that retains a Lean byte-level contract. Keep the packed representation through reads and compaction when callers need no independently allocated records.

```sh
bash scripts/packed.sh --out /tmp/alvoki-packed.csv
python3 benchmarks/packed.py --summarize /tmp/alvoki-packed.csv
objdump -d --disassemble=alvoki_write_pair lean/.lake/build/bin/alvoki-packed
objdump -d --disassemble=alvoki_encode_batch lean/.lake/build/bin/alvoki-packed
```

- [Raw measurements](../../benchmarks/results/packed/packed-trials.csv)
- [Summary](../../benchmarks/results/packed/packed-summary.csv)
- [VM environment](../../benchmarks/results/packed/packed-environment.txt)
