#!/usr/bin/env python3
"""Interleave stock Lean binaries from two builds on the same packed workloads."""

import argparse
import csv
import os
from pathlib import Path
import random
import subprocess
import tempfile

from support import ROOT, compactions, mixed_spans, split_spans
from generate import block, columnar, dataset


def jobs(records):
    for profile, (left, right) in compactions(records):
        a, b = block(left), block(right)
        for mode in ("adaptive-merge", "fused-merge", "direct-scan"):
            yield f"{profile}-{mode}", "alvoki-fused-merge", mode, a, b
    yield "validate-v1", "alvoki-opt", "validate-machine", block(records), block([])
    yield "validate-v2", "alvoki-opt", "validate-machine", columnar(records), block([])
    yield "mixed-spans-copy-into", "alvoki-native", "merge-copy-into", *map(block, mixed_spans(records))
    yield "span-16-spans", "alvoki-native", "merge-spans", *map(block, split_spans(records, 16))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline-bin", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--size", type=int, default=1_000_000)
    parser.add_argument("--rounds", type=int, default=12)
    args = parser.parse_args()
    if args.rounds < 1 or args.size < 1:
        parser.error("size and rounds must be positive")

    builds = [("before", args.baseline_bin.resolve()), ("after", ROOT / "lean/.lake/build/bin")]
    cpu = min(os.sched_getaffinity(0))
    os.sched_setaffinity(0, {cpu})
    rng = random.Random(891)
    env = {key: val for key, val in os.environ.items() if key != "ALVOKI_RSS"}
    with tempfile.TemporaryDirectory() as directory, args.out.open("w", newline="") as stream:
        left, right, aux, output = (Path(directory) / name for name in ("left", "right", "aux", "output"))
        aux.write_bytes(block([]))
        writer = csv.writer(stream, lineterminator="\n")
        writer.writerow(("records", "workload", "revision", "round", "trial", "ns", "checksum", "cpu"))
        for workload, exe, mode, a, b in jobs(dataset(args.size)):
            left.write_bytes(a)
            right.write_bytes(b)
            if exe == "alvoki-opt":
                command = [mode, left, right, "0", "4"]
            elif exe == "alvoki-fused-merge":
                command = [mode, left, right, aux, output, "4"]
            else:
                command = [mode, left, right, output, "4"]
            checksums = set()
            for round_index in range(1, args.rounds + 1):
                order = builds[:]
                rng.shuffle(order)
                for label, bin_dir in order:
                    lines = subprocess.check_output([bin_dir / exe, *command], text=True, env=env).splitlines()
                    assert len(lines) == 4, (workload, label)
                    for trial, line in enumerate(lines[1:], 1):
                        elapsed, checksum = map(int, line.split())
                        checksums.add(checksum)
                        writer.writerow((args.size, workload, label, round_index, trial, elapsed, checksum, cpu))
            assert len(checksums) == 1, (workload, checksums)


if __name__ == "__main__":
    main()
