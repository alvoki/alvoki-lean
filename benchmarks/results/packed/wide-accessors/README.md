# Wide ByteArray accessors

This experiment compares four versions of the 64-bit little-endian machine-offset accessors proposed in Lean PR #14053. It also runs the same Lean benchmark against the actual upstream PR toolchain. The backport isolates the load and store bodies from broader toolchain differences. [Lean PR #14053](https://github.com/leanprover/lean4/pull/14053) · [CompPoly ablation proposal](https://github.com/leanprover/lean4/pull/14053#issuecomment-6064160815)

| Variant | Load and store | Post-store ownership information |
|---|---|---|
| Shifts | PR's byte-wise shift assembly | As in the PR |
| Shifts + assume | Same shifts | Clang assumes the returned header has `m_rc == 1` |
| Memcpy | Fixed-size unaligned `memcpy` with endian adaptation | As in the PR |
| Memcpy + assume | Same fixed-size `memcpy` | Clang assumes the returned header has `m_rc == 1` |

All four call `lean_sarray_ensure_exclusive` before writing. The assumption follows the in-bounds store into that returned exclusive array. All four recompile the same generated Lean C with the same release flags. The benchmark-only externs and the assumption form a native trust boundary. The complete output bytes were checked independently on every measured input. Fixtures additionally exercise empty output, an odd final record, tombstones, full-width keys, invalid extents, and an unaligned final-word write and read with the old alias retained. [Accessor implementations](../../../../lean/runtime-experiment/wide-accessors/accessors.h) · [Native driver](../../../../lean/runtime-experiment/wide-accessors/WideAccessorBench.lean) · [Python oracle](../../../wide_accessors.py)

## Workloads and timing

- **Packed repack** reads and writes each v3 word into a new output. Stock Lean uses `wordMachine` and the eight-byte indexed `storeWord`.
- **Owned encode** reads already decoded entries and writes them into a new v3 block. Lean holds an array of `Model.Entry (UInt64 × UInt64)` values, and Rust holds a contiguous array of `[u64; 4]`. Both prepare all entries outside the timer. The Lean cursor is a native `USize` parameter in the recursive loop.
- **Dense rewrite** copies a packed v3 block and flips every bit selected by the mask in each live value. Tombstones keep their canonical zero value.
- **Alternating replay** emits an already selected sequence of alternating v3 rows. Stock Lean issues one 32-byte `copySlice` per row. The four accessor variants load and write four 64-bit words per row. The Rust control copies one 32-byte slice per row.

Full timing includes output allocation and initialization. Kernel timing starts with the output already allocated and initialized, including the baseline copy for dense rewriting. The Rust kernel control explicitly touches the fresh output before starting to avoid counting first-touch pages in the writes. Lean and Rust allocate their full-scope outputs differently. The full-scope ratios include that difference. Both scopes time the same emission code. Input parsing, owned-row materialization and output verification are outside both timers. Each case uses nine interleaved trials in deterministic randomized order, with one warm-up per subprocess. [Rust control](../../../../lean/runtime-experiment/wide-accessors/control.rs) · [Raw trials](trials.csv)

## Results

Median milliseconds at one million records. The raw archive and summary also include 100,000-record workloads.

| Workload | Scope | Stock Lean | Original PR | Shifts | Shifts + assume | Memcpy | Memcpy + assume | Rust |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| Packed repack | Full | 19.130 | 5.775 | 5.888 | 5.959 | 5.403 | 5.322 | 10.978 |
| Packed repack | Kernel | 15.918 | 2.498 | 2.506 | 2.485 | 2.144 | 2.027 | 2.412 |
| Owned encode | Full | 18.065 | 7.659 | 7.803 | 7.606 | 7.480 | 7.536 | 11.168 |
| Owned encode | Kernel | 14.651 | 4.127 | 4.204 | 4.083 | 4.102 | 4.111 | 2.539 |
| Dense rewrite | Full | 5.304 | 3.451 | 3.437 | 3.261 | 3.305 | 3.321 | 13.079 |
| Dense rewrite | Kernel | 3.658 | 1.770 | 1.634 | 1.691 | 1.664 | 1.672 | 2.088 |
| Alternating replay | Full | 8.973 | 6.854 | 7.010 | 6.928 | 5.479 | 5.466 | 9.753 |
| Alternating replay | Kernel | 5.876 | 3.469 | 3.518 | 3.449 | 2.091 | 2.300 | 2.417 |

The original PR's wide accessors cut the resident packed repack kernel from 15.918 to 2.498 ms and owned encoding from 14.651 to 4.127 ms. Within the backport's same-toolchain ablation, fixed-size memcpy reduced alternating replay from 3.518 to 2.091 ms and packed repack from 2.506 to 2.144 ms. Dense rewriting and owned encoding changed much less under that ablation. [All medians](summary.txt)

For this Clang build, the assumption reduces several static ownership slow-path sites. The timing changes vary by workload and scope. For example, the memcpy alternating body has 12 sites without the assumption and 9 with it, while the resident replay median rises from 2.091 to 2.300 ms. Each measured loop retains a path for checking ownership. The alternating control holds row selection fixed, and the owned comparison still includes Lean's boxed row layout versus contiguous Rust words. [Code generation](codegen.txt)

## Reproduce

The four-way backport and stock control use Lean 4.36.0 (`611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`) and its bundled Clang 23.1.1 (`6dfe1677ab8dffbc6ec13d53a1e0215d75147689`). Rust is 1.100.0 (`0ef1bc386`), Python is 3.12.14, and the pinned CPU is 1 on a Linux 6.18.57 x86-64 VM with AMD EPYC 9V74.

```sh
taskset -c 1 bash scripts/wide-accessors.sh --out /tmp/wide.csv
python3 benchmarks/wide_accessors.py --summarize /tmp/wide.csv
```

To include the original PR, extract its Linux x86-64 archive in a separate directory and build this benchmark in a separate checkout. Remove the `moreLeancArgs = ["-include", "runtime-experiment/wide-accessors/accessors.h"]` line of the experimental target in that checkout, and run `lake build alvoki-wide-accessors` using the extracted toolchain's `bin` directory first on `PATH`. Lean should report `4.36.0-pre` at `ae6bd28905559939c42cb1f89d24a930fdd834e2`. Pass its executable as `--upstream /absolute/path/to/alvoki-wide-accessors` to the main experiment command. The archived Linux build has SHA-256 `e6e5c1916ec0c562bd847c82ede3ca65c606c6fddc341a8e02b9dc0aa4ce6d68`. [Upstream toolchain archive](https://github.com/leanprover/lean4-pr-releases/releases/download/pr-release-14053/lean-4.36.0-pre-linux.tar.zst)
