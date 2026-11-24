"""Pair checkpoint publication and reopen across two native releases."""

import argparse
import csv
import os
from statistics import median
import subprocess


parser = argparse.ArgumentParser()
parser.add_argument("baseline")
parser.add_argument("candidate")
parser.add_argument("output")
parser.add_argument("--cpu", type=int, required=True)
parser.add_argument("--pairs", type=int, default=12)
args = parser.parse_args()
if args.pairs < 2 or args.pairs % 2:
    parser.error("pairs must be a positive even number")
os.sched_setaffinity(0, {args.cpu})

builds = [("v1", args.baseline), ("v2", args.candidate)]
workloads = {
    "publish": ["4", "8192", "3"],
    "reopen": ["4", "8192", "3", "--reopen"],
}
with open(args.output, "w", newline="") as output:
    writer = csv.writer(output, lineterminator="\n")
    writer.writerow(("cpu", "workload", "pair", "position", "format", "trial", "ns"))
    for workload, command in workloads.items():
        samples = {"v1": [], "v2": []}
        ratios = []
        for pair in range(1, args.pairs + 1):
            order = builds if pair % 2 else reversed(builds)
            times = {}
            for position, (version, binary) in enumerate(order, 1):
                stdout = subprocess.check_output([binary, *command], text=True)
                rows = list(csv.DictReader(stdout.splitlines()))
                values = [int(row["ns"]) for row in rows]
                if len(values) != 3 or min(values) <= 0:
                    raise RuntimeError(f"invalid {version} {workload} timings")
                for row in rows:
                    writer.writerow((args.cpu, workload, pair, position, version, row["trial"], row["ns"]))
                samples[version].extend(values)
                times[version] = median(values)
            ratios.append(times["v2"] / times["v1"])
            output.flush()
        print(f"CPU {args.cpu}, {workload}: {median(samples['v1']) / 1e6:.3f} ms v1, "
              f"{median(samples['v2']) / 1e6:.3f} ms v2, {median(ratios):.3f}× paired")
