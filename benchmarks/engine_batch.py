#!/usr/bin/env python3
"""Compare closed-loop, atomically durable write batches of equal logical size."""

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


def parse_samples(stdout, rows, batch_size):
    samples = [
        (int(row["rows"]), row["kind"], int(row["ns"]))
        for row in csv.DictReader(io.StringIO(stdout))
    ]
    expected = [(done, "batch") for done in range(batch_size, rows + 1, batch_size)]
    expected.append((rows, "total"))
    if [(done, kind) for done, kind, _ in samples] != expected:
        raise ValueError("runner did not return one sample per batch followed by a total")
    if any(ns <= 0 for _, _, ns in samples):
        raise ValueError("runner returned a nonpositive duration")
    return samples


def run_trial(binary, args, batch_size):
    with tempfile.TemporaryDirectory(prefix="engine-batch-", dir=args.db_root) as directory:
        command = [str(binary), directory, str(args.rows), str(batch_size)]
        result = subprocess.run(command, text=True, capture_output=True, check=False)
        if result.returncode:
            raise RuntimeError(f"{binary} failed ({result.returncode}): {result.stderr.strip()}")
        return parse_samples(result.stdout, args.rows, batch_size)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path, default=ROOT / "lean/.lake/build/bin/alvoki-disk-batch")
    parser.add_argument("--rocks-bin", type=Path, required=True)
    parser.add_argument("--rows", type=int, default=4096)
    parser.add_argument("--batch-sizes", type=int, nargs="+", default=[1, 8, 32])
    parser.add_argument("--trials", type=int, default=5)
    parser.add_argument("--cpu", type=int)
    parser.add_argument("--db-root", type=Path, default=Path(tempfile.gettempdir()))
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if (
        not 0 < args.rows < 2**64 or args.trials < 1
        or len(set(args.batch_sizes)) != len(args.batch_sizes)
        or any(size < 1 or args.rows % size for size in args.batch_sizes)
    ):
        parser.error("use positive trials, distinct positive batch sizes, and a UInt64 row count divisible by each size")

    cpu = min(os.sched_getaffinity(0)) if args.cpu is None else args.cpu
    os.sched_setaffinity(0, {cpu})
    lean = args.lean_bin.resolve()
    rocks = args.rocks_bin.resolve()
    metadata = {
        "cpu": cpu,
        "platform": platform.platform(),
        "db_root": str(args.db_root.resolve()),
        "rows": args.rows,
        "batch_sizes": args.batch_sizes,
        "trials": args.trials,
        "alvoki_binary": str(lean),
        "rocksdb_binary": str(rocks),
        "rocksdb_version": subprocess.check_output([rocks, "--version"], text=True).strip(),
        "revision": subprocess.check_output(["git", "-C", ROOT, "rev-parse", "HEAD"], text=True).strip(),
        "protocol": "one synchronous submission at a time, fresh database per trial",
    }

    engines = (("alvoki", lean), ("rocksdb", rocks))
    summaries = defaultdict(list)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.with_suffix(".json").write_text(json.dumps(metadata, indent=2) + "\n")
    with args.out.open("w", newline="") as file:
        writer = csv.writer(file, lineterminator="\n")
        writer.writerow(("engine", "batch_size", "trial", "rows", "kind", "ns"))
        for batch_size in args.batch_sizes:
            for trial in range(args.trials):
                for engine, binary in (engines if trial % 2 == 0 else reversed(engines)):
                    if trial == 0:
                        run_trial(binary, args, batch_size)
                    samples = run_trial(binary, args, batch_size)
                    writer.writerows(
                        (engine, batch_size, trial + 1, rows, kind, ns) for rows, kind, ns in samples
                    )
                    file.flush()
                    batch_ns = sorted(ns for _, _, ns in samples[:-1])
                    summaries[batch_size, engine].append((
                        args.rows * 1e9 / samples[-1][2],
                        median(batch_ns) / 1e3,
                        batch_ns[ceil(0.99 * len(batch_ns)) - 1] / 1e3,
                    ))

    print("batch   engine      rows/s   batch p50 us   batch p99 us")
    for (batch_size, engine), trials in summaries.items():
        rate, p50, p99 = map(median, zip(*trials))
        print(f"{batch_size:5d}   {engine:8} {rate:9.1f} {p50:14.3f} {p99:14.3f}")


if __name__ == "__main__":
    main()
