#!/usr/bin/env python3
"""Run paired native mixed and maintenance workloads with individually durable writes."""

import argparse
import csv
from collections import defaultdict
import io
import json
from math import ceil
import os
from pathlib import Path
import platform
from statistics import median
import subprocess
import tempfile

from disk_replay import ROOT

MODES = ("mixed", "maintenance")


def parse_samples(stdout, operations):
    rows = []
    primary = []
    for row in csv.DictReader(io.StringIO(stdout)):
        op, kind, value = int(row["op"]), row["kind"], int(row["ns"])
        if not 1 <= op <= operations or value < 0:
            raise ValueError(f"invalid sample: {row}")
        rows.append((op, kind, value))
        if kind in ("put", "get"):
            primary.append((op, kind))
    expected = [(op, "put" if op % 2 else "get") for op in range(1, operations + 1)]
    totals = [(op, value) for op, kind, value in rows if kind == "total"]
    if primary != expected or len(totals) != 1 or totals[0][0] != operations or totals[0][1] == 0:
        raise ValueError("runner did not emit exactly the requested operations and one total")
    return rows


def percentile99(samples):
    ordered = sorted(samples)
    return ordered[ceil(0.99 * len(ordered)) - 1]


def run_trial(binary, root, mode, args):
    with tempfile.TemporaryDirectory(prefix="engine-workload-", dir=root) as directory:
        completed = subprocess.run(
            [str(binary), directory, mode, str(args.operations), str(args.keys),
             str(args.interval), str(args.seed)],
            text=True, capture_output=True, check=False,
        )
        if completed.returncode:
            raise RuntimeError(f"{binary} failed ({completed.returncode}): {completed.stderr.strip()}")
        return parse_samples(completed.stdout, args.operations)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path, default=ROOT / "lean/.lake/build/bin/alvoki-disk-workload")
    parser.add_argument("--rocks-bin", required=True, type=Path)
    parser.add_argument("--operations", type=int, default=8000)
    parser.add_argument("--keys", type=int, default=256)
    parser.add_argument("--interval", type=int, default=1000)
    parser.add_argument("--trials", type=int, default=5)
    parser.add_argument("--seed", type=int, default=1847)
    parser.add_argument("--cpu", type=int)
    parser.add_argument("--db-root", type=Path, default=Path(tempfile.gettempdir()))
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()
    if (
        args.operations % 2 or args.operations < 4 * args.interval or
        min(args.interval, args.keys, args.trials) < 1 or not 0 <= args.seed < 2**64
    ):
        parser.error("use an even operation count, at least four intervals, positive sizes, and a UInt64 seed")
    cpu = min(os.sched_getaffinity(0)) if args.cpu is None else args.cpu
    os.sched_setaffinity(0, {cpu})
    env = {
        "cpu": cpu, "platform": platform.platform(), "db_root": str(args.db_root.resolve()),
        "operations": args.operations, "keys": args.keys, "interval": args.interval,
        "trials": args.trials, "seed": args.seed, "protocol": "closed-loop; single foreground caller",
        "rocksdb": subprocess.check_output([args.rocks_bin.resolve(), "--version"], text=True).strip(),
        "revision": subprocess.check_output(["git", "-C", ROOT, "rev-parse", "HEAD"], text=True).strip(),
    }

    summaries = defaultdict(list)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.with_suffix(".json").write_text(json.dumps(env, indent=2) + "\n")
    with args.out.open("w", newline="") as file:
        writer = csv.writer(file, lineterminator="\n")
        writer.writerow(("engine", "scenario", "trial", "op", "kind", "value", "unit"))
        for mode in MODES:
            engines = (("alvoki", args.lean_bin.resolve()), ("rocksdb", args.rocks_bin.resolve()))
            for trial in range(args.trials):
                for engine, binary in (engines if trial % 2 == 0 else reversed(engines)):
                    # Each engine gets its own fresh untimed warm-up database.
                    if trial == 0:
                        run_trial(binary, args.db_root, mode, args)
                    rows = run_trial(binary, args.db_root, mode, args)
                    samples = defaultdict(list)
                    for op, kind, value in rows:
                        unit = "bytes" if kind in ("db_bytes", "process_write_bytes") else "ns"
                        writer.writerow((engine, mode, trial + 1, op, kind, value, unit))
                        samples[kind].append(value)
                    file.flush()
                    summaries[mode, engine].append((
                        args.operations * 10**9 / samples["total"][0],
                        percentile99(samples["get"]) / 10**6,
                        percentile99(samples["put"]) / 10**6,
                        sum(samples["put"]) / (len(samples["put"]) * 10**6),
                    ))

    print("scenario     engine      ops/s   read p99 ms   write p99 ms   mean write ms")
    for (mode, engine), rows in summaries.items():
        throughput, read_p99, write_p99, write_avg = map(median, zip(*rows))
        print(f"{mode:12} {engine:8} {throughput:8.1f} {read_p99:13.4f} {write_p99:14.4f} {write_avg:15.4f}")


if __name__ == "__main__":
    main()
