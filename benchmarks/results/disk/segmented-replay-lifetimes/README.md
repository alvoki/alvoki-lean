# Native WAL replay buffer lifetimes

The experiment measures marked preparation under a held directory lock on the pinned Lean 4.36.0 release toolchain. Each workload has 600,000 descending-key frames. A v2 checkpoint with an empty run set covers the first 17 deletion frames. The keeper contains an unselected tail. Elapsed time covers preparation through the exact table and repair plan. Peak RSS is the Linux child process maximum returned by `wait4`. [Environment](environment.txt)

The baseline uses bounded preparation at `d46f492`. Its bounded reader and replay implementation also appear in `8631590`. The `early` mode moves keeper extraction ahead of vector replay. Generated C still borrows the full input list during concatenation and replay, so the caller releases it after recovery returns. The per-segment modes release each sealed payload before the next read. They keep the current table, one segment's events and the returned keeper prefix. [Experiment source](ReplayLifetimes.lean)

| Segments | Vector RSS | Early keeper extraction RSS | Deferred per-segment RSS |
| --- | ---: | ---: | ---: |
| 1 | 86.47 MiB | 86.43 MiB | 86.47 MiB |
| 8 | 116.54 MiB | 116.34 MiB | 66.55 MiB |
| 32 | 116.38 MiB | 116.45 MiB | 60.38 MiB |

Each overview median uses three timed samples per mode on CPU 1. A separate 12-pair comparison measured 116.46 to 66.46 MiB with eight segments and 116.47 to 60.42 MiB with 32. Its preparation medians were 173.49 to 155.38 ms and 161.05 to 151.96 ms, with ratios of medians of 0.896 and 0.944. The descriptive 95% paired bootstrap ranges were 0.830–0.993 and 0.908–0.974. To reproduce a range, sort the pair labels numerically and initialize Python's `random.Random(20261125)` for each segment count. Draw 12 whole pairs with `choices` for each of 3,000 replicates, take the deferred median divided by the vector median, and take zero-based entries 75 and 2924 of the sorted ratios. The three-sample overview put 32-segment deferred replay at 184.56 ms against 154.01 ms for the vector. Treat the RSS savings as the reliable result of this experiment. [Overview samples](overview.csv) · [Paired samples](paired.csv)

The correctness checks compare exact snapshot ranges, pins' floor, keeper start, selected keeper bytes and later names. The layouts include a checkpoint inside a sealed span, one at a segment boundary and a zero-length selected keeper. Error checks cover checksum and ordinal corruption in checkpoint-covered frames, wrong sealed lengths, and combinations with later corruption, a short keeper or denied read access. The eager serial mode reports the earlier checksum error when a later segment also has an invalid span. The deferred mode preserves the baseline diagnostic precedence in all exercised cases. [Comparison driver](compare.py)

The deferred mode performs the ordered reads through the keeper and retains the first decoder error and first replay error separately. It reports a global span error first, then the decoder error, then the replay error. Read failures and the keeper's physical coverage check take precedence. Production adoption requires Lean equivalence of the ordered reads, span fold and decoder/replay result for every admitted report, with exact error precedence. Prove the per-file decoder fold using aligned byte concatenation and the replay fold using checkpoint-prefix removal and the successive absolute ordinals. The effect proof can then pass the same exact keeper and physical size to the bounded repair worker.

Builds use a temporary Lake package with the checked-out repository as a dependency. Run from the repository root with the pinned toolchains installed.

```sh
bash benchmarks/results/disk/segmented-replay-lifetimes/run.sh --checks-only
bash benchmarks/results/disk/segmented-replay-lifetimes/run.sh --out /tmp/alvoki-overview.csv
bash benchmarks/results/disk/segmented-replay-lifetimes/run.sh --paired --out /tmp/alvoki-paired.csv
```
