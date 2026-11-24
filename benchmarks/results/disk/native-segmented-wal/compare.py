"""Interleave release opens on matching marked WAL fixtures and record raw samples."""

import argparse
from collections import defaultdict
import csv
import os
from pathlib import Path
import random
import statistics
import subprocess
import tempfile

from disk_replay import seed_segments


def timed(binary_dir, layout, case, trials):
    mode, records, workload, segments = case
    if mode == "write":
        lines = subprocess.check_output([
            binary_dir / "alvoki-disk-write", str(records), str(trials),
        ], text=True).splitlines()
        samples = [int(line.rsplit(",", 1)[-1]) for line in lines[1:]]
    elif mode == "checkpoint":
        lines = subprocess.check_output([
            binary_dir / "alvoki-disk-checkpoint", str(segments), str(records), str(trials), "--reopen",
        ], text=True).splitlines()
        samples = [int(line.rsplit(",", 1)[-1]) for line in lines[1:]]
    else:
        with tempfile.TemporaryDirectory(prefix="alvoki-segmented-bench-") as tmp:
            database = Path(tmp)
            first, keeper = seed_segments(database, records, workload, segments)
            if layout == "single":
                assert segments == 1
                keeper = keeper.rename(database / "WAL")
            command = [binary_dir / "alvoki-disk-replay", database, str(records), str(trials)]
            if mode == "repair":
                with keeper.open("ab") as wal:
                    wal.write(b"ALVOWAL1\x00\x00\x00")
                command.append("--repair-tail")
                if layout != "single":
                    command.append(str(first))
            samples = [int(line) for line in subprocess.check_output(command, text=True).splitlines()]
    if len(samples) != trials or min(samples) < 1:
        raise ValueError((case, samples))
    return samples


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", required=True, type=Path)
    parser.add_argument("--candidate", required=True, type=Path)
    parser.add_argument("--base-layout", choices=("single", "segmented"), default="single")
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--pairs", type=int, default=12)
    parser.add_argument("--trials", type=int, default=2)
    parser.add_argument("--without-write", action="store_true", help="reproduce the earlier reopen-only cohort")
    parser.add_argument("--cpu", type=int, default=min(os.sched_getaffinity(0)))
    args = parser.parse_args()
    if args.pairs < 2 or args.pairs % 2 or args.trials < 1:
        parser.error("use an even pair count and a positive number of trials")
    os.sched_setaffinity(0, {args.cpu})
    rng = random.Random(20261126)
    before = args.base.resolve()
    after = args.candidate.resolve()
    cases = [
        (mode, rows, workload, 1)
        for rows, workload in ((32, "ascending"), (2048, "ascending"), (20000, "descending"))
        for mode in ("aligned", "repair")
    ] + [("checkpoint", 128, "-", runs) for runs in (4, 32)]
    controls = [("aligned", 32, "ascending", 1), ("repair", 2048, "ascending", 1)]
    if not args.without_write:
        write = ("write", 40, "-", 1)
        cases.append(write)
        controls.append(write)
    groups = [
        ("baseline", case, [(before, args.base_layout, case), (after, "segmented", case)])
        for case in cases
    ]
    for case in controls:
        groups.append(("control", case, [(after, "segmented", case)] * 2))
    for mode in ("aligned", "repair"):
        for count in (8,32):
            case = (mode, 2048, "ascending", count)
            groups.append(("segment-count", case, [
                (after, "segmented", (mode, 2048, "ascending", 1)), (after, "segmented", case),
            ]))
    orders = []
    for _ in groups:
        order = [0, 1] * (args.pairs // 2)
        rng.shuffle(order)
        orders.append(order)

    rows = defaultdict(list)
    with args.out.open("w", newline="") as f:
        writer = csv.writer(f, lineterminator="\n")
        writer.writerow(("cohort", "mode", "records", "workload", "segments", "pair", "order", "arm", "trial", "ns", "cpu"))
        for pair in range(args.pairs):
            group_order = list(enumerate(groups))
            rng.shuffle(group_order)
            for index, (cohort, case, variants) in group_order:
                first = orders[index][pair]
                for position, arm in enumerate([first, 1 - first], 1):
                    samples = timed(*variants[arm], args.trials)
                    writer.writerows((cohort, *case, pair + 1, position, arm, trial, ns, args.cpu)
                                     for trial, ns in enumerate(samples, 1))
                    f.flush()
                    rows[index, arm].append(samples)
    boot = random.Random(20261127)
    for index, (cohort, case, _) in enumerate(groups):
        a, b = rows[index, 0], rows[index, 1]
        def med(arm, indices):
            return statistics.median(ns for pair in indices for ns in arm[pair])
        pair_ids = list(range(args.pairs))
        old, new = med(a, pair_ids), med(b, pair_ids)
        draws = [boot.choices(pair_ids, k=args.pairs) for _ in range(3000)]
        ratios = sorted(med(b, draw) / med(a, draw) for draw in draws)
        divisor = 1e6 * (case[1] if case[0] == "write" else 1)
        print(f"{cohort} {case}: {old / divisor:.3f} to {new / divisor:.3f} ms, "
              f"{new / old:.3f}x ({ratios[75]:.3f}–{ratios[2924]:.3f})")


if __name__ == "__main__":
    main()
