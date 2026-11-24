# Published Lean toolchains on Alvoki's packed writers

The same Alvoki source at `d29eb1ab05f4e2923f91a278a1909a9f13144442` builds the v1 merge-phase and v3 compaction executables on all three Lean toolchains. Every executable passes the existing exact-byte and checksum fixtures, including 11 v1 merge cases and 7 invalid traces, plus 15 v3 compaction cases and 9 malformed runs. The Python oracle also checks the output of each timed workload. These builds use the existing `ByteArray.copySlice` code. The explicit use of the proposed word accessors is measured in the [wide-accessor experiment](../wide-accessors).

The first run covers all existing modes at 100,000 and 1,000,000 records, with nine samples per case. Some initial batches had substantial variation, so the follow-up shuffles the order of the four binaries with a fixed seed on each of nine rounds. Each process warms up once and then contributes three timings. The table gives medians of these 27 timings at one million records, in milliseconds.

| Workload and timed operation | Lean 4.36.0 | Lean 4.38 nightly | PR #14053 build | Rust 1.100 |
|---|---:|---:|---:|---:|
| v1 alternating replay write | 6.765 | 6.716 | 6.897 | 1.539 |
| v1 collision-heavy replay write | 5.624 | 4.205 | 5.969 | 0.742 |
| v3 range-ingest row compaction | 7.918 | 7.544 | 7.821 | 3.871 |
| v3 hot-updates row compaction | 7.773 | 7.303 | 7.432 | 3.821 |
| v3 range-ingest pipeline | 9.497 | 9.333 | 9.612 | 6.757 |
| v3 hot-updates pipeline | 9.361 | 8.785 | 9.242 | 8.755 |
| v3 delete-reinsert pipeline | 9.760 | 9.790 | 9.738 | 8.251 |
| v3 uniform-mix pipeline | 17.621 | 17.417 | 17.626 | 12.010 |

The nightly changed alternating replay time by less than 1%. It improved both repeated v3 row compactions by 5–6%, compared with about 20% in the initial batches. It changed the four v3 pipelines by 0–6%. In collision-heavy replay, the nightly stayed close to 4.2 ms on both runs. The stock and PR samples each show groups around 4.2 ms and 6 ms in the repeat, and the stock batch stayed around 4.2 ms in the first run. The collision-heavy figures reflect run-to-run variability on this VM. Both newer toolchains still call the generic slice-copy routine on these paths. The comparison measures each distribution with its bundled compiler and runtime.

[v1 full matrix](v1-merge-trials.csv) · [v3 full matrix](v3-compaction-trials.csv) · [Interleaved repeat](interleaved-trials.csv)

## Toolchains and environment

| Build | Lean commit | Bundled Clang |
|---|---|---|
| `v4.36.0` | `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9` | 23.1.1 (`6dfe1677ab8d`) |
| `nightly-2026-11-23` | `231ef9a28b27a9a7ebabdbfa40c84cfb22744c24` | 23.1.3 (`0d261d1ca552`) |
| `pr-release-14053` (`4.36.0-pre`) | `ae6bd28905559939c42cb1f89d24a930fdd834e2` | 23.1.1 (`6dfe1677ab8d`) |

The nightly was the newest published Linux x86-64 artifact when queried on 24 November 2026. The PR artifact reports the exact open draft's head. Timings used one pinned CPU (CPU 4) on Linux 6.18.57, Debian 13, glibc 2.41, AMD EPYC 9V74 under KVM and Python 3.12.14. Rust used the repository's pinned 1.100.0 release build at `0ef1bc386`. Distributed Lean binaries and their runtime libraries were used as released.

| Linux x86-64 release archive | SHA-256 |
|---|---|
| [Lean nightly](https://github.com/leanprover/lean4-nightly/releases/tag/nightly-2026-11-23) | `c9fdbee6dbfa25db813527fdcb98849e6c8802bb48ce6edece639ecfdcaa0d93` |
| [Lean PR build](https://github.com/leanprover/lean4-pr-releases/releases/tag/pr-release-14053) | `e6e5c1916ec0c562bd847c82ede3ca65c606c6fddc341a8e02b9dc0aa4ce6d68` |

The [Lean FRO roadmap](https://lean-lang.org/fro/roadmap/y4-1/#compiler) calls out improved array manipulation, uniqueness annotations and stack allocation. It sets the design phase for September 2026 to February 2027 and says implementation should start at the beginning of 2027.

## Reproduce

Extract each toolchain into its own directory. Use a separate Lean source snapshot for each one so build products and the pinned project installation stay isolated. Put the chosen toolchain's `bin` directory first in `PATH` for the build. Repeat the command for all three toolchains.

```sh
snapshot=$(mktemp -d)
git archive d29eb1a lean | tar -x -C "$snapshot"
(cd "$snapshot/lean" && PATH="/path/to/toolchain/bin:$PATH" \
  lake build alvoki-compaction alvoki-merge-phases)
```

Build the Rust controls with the pinned Rust compiler using `(cd rust && cargo build --release)`. Supply the resulting binary directories to the runner below. Repeat it with `--focused --sizes 1000000` for the interleaved measurement.

```sh
taskset -c 4 python3 benchmarks/results/packed/upstream-toolchains/compare.py \
  --out /tmp/alvoki-upstream-results \
  --toolchain stock /path/to/stock/lean/.lake/build/bin \
  --toolchain nightly /path/to/nightly/lean/.lake/build/bin \
  --toolchain pr14053 /path/to/pr/lean/.lake/build/bin \
  --toolchain rust rust/target/release
```

To build the wide-accessor benchmark with the official PR header, copy `WideAccessorBench.lean` from the [wide-accessor benchmark directory](../../../../lean/runtime-experiment/wide-accessors) into `lean/runtime-experiment/wide-accessors` under the PR source snapshot. Add the executable below to the snapshot's `lean/lakefile.toml`, then build `alvoki-wide-accessors` on the PR toolchain and pass the resulting executable to the wide-accessor driver with `--upstream`.

```toml
[[lean_exe]]
name = "alvoki-wide-accessors"
root = "WideAccessorBench"
srcDir = "runtime-experiment/wide-accessors"
```
