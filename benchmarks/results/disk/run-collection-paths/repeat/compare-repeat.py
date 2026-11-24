import argparse
import csv
import os
from pathlib import Path
import random
from statistics import median
import subprocess

cli = argparse.ArgumentParser()
cli.add_argument("base", type=Path, help="prefix of the baseline release binaries")
cli.add_argument("candidate", type=Path, help="prefix of the candidate release binaries")
cli.add_argument("output", type=Path)
cli.add_argument("--cpu", type=int, required=True)
cli.add_argument("--pairs", type=int, default=24)
cli.add_argument("--seed", type=int, default=74321)
args = cli.parse_args()

if args.pairs < 2 or args.pairs % 2:
    cli.error("pairs must be positive and even")
if args.cpu not in os.sched_getaffinity(0):
    cli.error("chosen CPU is not available")
os.sched_setaffinity(0, {args.cpu})

cases = {
    "write-16": ("write", ["16", "3"]),
    "reopen-32x128": ("checkpoint", ["32", "128", "3", "--reopen"]),
}
prefixes = {"base": args.base, "candidate": args.candidate}
comparisons = {
    "AB": ("base", "candidate"),
    "AA": ("base", "base"),
    "BB": ("candidate", "candidate"),
}
ratios = {(case, kind): [] for case in cases for kind in comparisons}
randomizer = random.Random(args.seed)

with args.output.open("w", newline="") as handle:
    writer = csv.writer(handle, lineterminator="\n")
    writer.writerow(("cpu", "case", "kind", "pair", "position", "side", "binary", "trial", "ns"))
    for pair in range(1, args.pairs + 1):
        control = "AA" if pair % 2 else "BB"
        queue = [(case, kind) for case in cases for kind in ("AB", control)]
        randomizer.shuffle(queue)
        for case, kind in queue:
            target, command = cases[case]
            binaries = comparisons[kind]
            values = {}
            reverse = pair % 2 == 0 if kind == "AB" else (pair // 2) % 2 != 0
            order = (1, 0) if reverse else (0, 1)
            for position, side in enumerate(order, 1):
                variant = binaries[side]
                executable = f"{prefixes[variant]}-{target}"
                result = subprocess.check_output([executable, *command], text=True)
                samples = [int(row["ns"]) for row in csv.DictReader(result.splitlines())]
                if len(samples) != 3 or min(samples) <= 0:
                    raise RuntimeError(f"{case} emitted invalid samples")
                for trial, ns in enumerate(samples, 1):
                    writer.writerow((args.cpu, case, kind, pair, position, side, variant, trial, ns))
                values[side] = median(samples)
            ratios[case, kind].append(values[1] / values[0])
            handle.flush()

for (case, kind), times in ratios.items():
    print(f"CPU {args.cpu}, {case}, {kind} ({len(times)} pairs): {median(times):.3f}x")
