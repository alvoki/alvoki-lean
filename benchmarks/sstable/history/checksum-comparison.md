# Historical Lean checksum comparison

The comparison ran at `adb8e7c8` with GCC, zlib headers and `taskset` on Linux x86-64. To reproduce it, check out that revision and run the original benchmark from the repository root with the pinned Lean toolchain.

```sh
BENCH_CPU=4 bash benchmarks/sstable/run-checksums.sh
```

Set `BENCH_CPU` to an allowed CPU. By default the runner picks the first CPU in its affinity mask. The runner fetches pinned Google CRC32C 1.1.2 and lean-zlib commit `270c2da`. Set `CRC32C_DIR` or `LEAN_ZLIB_DIR` to reuse clean checkouts at those revisions. It builds the pinned upstream `Zlib.Checksum` module and its C shim against the installed libz.

The two native Lean calls use the same loop over eight deterministically generated, reused byte arrays per size. Each trial hashes 64 MiB after 1,000 warmup calls, and the seven trials alternate backend order. The CRC calls start from zero and a checksum sum is retained for every trial. Timing includes the shared Lean loop and FFI call overhead. Separate checks exercise each polynomial's known test vector, incremental convention and empty input. The Google backend is also compared against the portable Lean CRC32C definition across the timed inputs and two initial CRCs.

| Bytes per call | Google CRC32C median ns/call | lean-zlib CRC32 median ns/call | zlib/Google |
| ---: | ---: | ---: | ---: |
| 32 | 7.14 | 40.99 | 5.74× |
| 256 | 12.48 | 125.63 | 10.06× |
| 1,024 | 35.32 | 241.94 | 6.85× |
| 4,096 | 123.75 | 641.08 | 5.18× |
| 16,384 | 469.14 | 2,332.25 | 4.97× |

Measured on CPU 4 of an AMD EPYC 9V45 with SSE4.2 exposed, Linux 6.18.57, Debian 13, GCC 14.2.0 with `-O3 -DNDEBUG`, system zlib 1.3.1 and Lean 4.36.0. These are warm-buffer checksum timings. CRC32C and zlib's IEEE CRC32 use different polynomials, so changing backends between those algorithms changes wire checksums. [Raw timings](checksum-trials.csv)
