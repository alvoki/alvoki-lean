# Bounded keeper replay

The baseline `5297220` reads the whole keeper. Candidate `6154dc8` requests only the marker-selected keeper bytes. The bounded runtime is integrated through `4bde9c4` and the matching benchmark probe through `159dee0`. Both measured binaries use that probe and the pinned stock Lean release toolchain. [Environment](environment.txt) · [Raw final resource samples](resources-cpu1.csv)

Both arms reopen 2,048 ascending frames with no checkpoint on CPU 1. The segment layouts contain the exact same frames and absolute marker. Each keeper's uncommitted tail is zero-filled. The numbers below are medians of three runs per side. Linux process peak RSS is sampled from `VmHWM` immediately after open, before the row checker. A separate fresh copy runs under `strace` to count bytes returned by WAL segment read syscalls. This measures kernel-to-process bytes, including runtime read-ahead. [Probe](../../../../lean/Alvoki/Bench/Disk/DiskReplayBench.lean) · [Driver](../../../disk_replay_resources.py)

| Segments | Keeper tail | Before WAL read bytes | After WAL read bytes | Before peak RSS, KiB | After peak RSS, KiB |
|---:|---:|---:|---:|---:|---:|
| 1 | 0 B | 98,304 | 98,304 | 10,868 | 10,992 |
| 1 | 11 B | 98,315 | 98,304 | 10,968 | 10,896 |
| 1 | 8 MiB | 8,486,912 | 98,304 | 21,212 | 10,908 |
| 1 | 32 MiB | 33,652,736 | 98,304 | 45,700 | 10,972 |
| 8 | 0 B | 98,304 | 98,304 | 10,920 | 10,980 |
| 8 | 11 B | 98,315 | 98,304 | 10,876 | 10,916 |
| 8 | 8 MiB | 8,486,912 | 98,304 | 19,168 | 10,900 |
| 8 | 32 MiB | 33,652,736 | 98,304 | 45,700 | 10,992 |
| 32 | 0 B | 98,304 | 98,304 | 14,960 | 15,072 |
| 32 | 11 B | 98,315 | 98,315 | 14,972 | 14,996 |
| 32 | 8 MiB | 8,486,912 | 99,328 | 21,164 | 14,988 |
| 32 | 32 MiB | 33,652,736 | 99,328 | 49,784 | 15,084 |

The 32 MiB tail adds about 34 MiB to peak RSS in the whole-keeper build. With the bounded read, measured RSS stays near the aligned case. The 32-segment layout has a 3,072-byte committed keeper, so libc's 4 KiB buffer can return 1,024 extra bytes or the entire 11-byte tail. The candidate still gives replay exactly 98,304 selected bytes. Every run checks the recovered rows, absolute watermark, and file bytes after reopen.

The preliminary CPU 4 resource run on `3c7fd10` returned the same read-byte counts in every case. [Preliminary resource samples](resources-cpu4.csv)

## Reopen latency

The timed run uses the regular replay harness with one untimed warmup and two timed opens per invocation. Each workload uses 12 balanced randomized pairs. Both binaries use the segmented layout. Repair timings use the ordinary 11-byte tail. The larger tails above exercise memory and read volume.

| Final CPU 1 case | Before, ms | After, ms | Ratio | 95% paired interval |
|---|---:|---:|---:|---:|
| 32 ascending, aligned | 2.381 | 2.318 | 0.974× | 0.834–1.033× |
| 32 ascending, torn tail | 5.818 | 5.377 | 0.924× | 0.882–0.998× |
| 2,048 ascending, aligned | 15.751 | 17.218 | 1.093× | 0.845–1.310× |
| 2,048 ascending, torn tail | 21.701 | 22.815 | 1.051× | 0.824–1.143× |

The small aligned comparison and both larger comparisons have intervals spanning parity. The preliminary CPU 4 run has wide intervals, including in identical-binary controls. The consistent gain across cohorts is lower read volume and peak memory with large tails. [Final timings](timing-cpu1.csv) · [Preliminary timings and controls](timing-cpu4.csv)

## Reproduce

Build each revision with the pinned release toolchain, applying the same [benchmark probe](../../../../lean/Alvoki/Bench/Disk/DiskReplayBench.lean) to both. Build `alvoki-disk-replay` for the resource run and `alvoki-disk-checkpoint` for the timed matrix.

```sh
python3 benchmarks/disk_replay_resources.py \
  --base BASE_BIN_DIR/alvoki-disk-replay --candidate CANDIDATE_BIN_DIR/alvoki-disk-replay \
  --cpu 1 --out /tmp/alvoki-bounded-resources.csv

PYTHONPATH=benchmarks python3 benchmarks/results/disk/native-segmented-wal/compare.py \
  --base BASE_BIN_DIR --candidate CANDIDATE_BIN_DIR --base-layout segmented \
  --without-write --cpu 1 --out /tmp/alvoki-bounded-timings.csv
```

For the preliminary CPU 4 run, build candidate `3c7fd10`, also build `alvoki-disk-write` on both sides, select CPU 4, and omit `--without-write` for timing. The existing timing report describes the paired resampling statistic. [Timing method](../native-segmented-wal)
