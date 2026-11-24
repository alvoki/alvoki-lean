#!/usr/bin/env python3
"""Measure native DiskTable.open on independently encoded WAL fixtures."""

import argparse
import csv
from math import isfinite
import os
from pathlib import Path
import random
from statistics import median
from struct import Struct
import subprocess
import tempfile

from support import MASK, ROOT, WORD_MASK

BINARY = ROOT / "lean/.lake/build/bin/alvoki-disk-replay"
FIELDS = Struct("<5Q")
MARKER_FIELDS = Struct("<2Q")
CHECKSUM = Struct("<Q")
WORKLOADS = ("ascending", "descending", "shuffled")


def with_checksum(fields):
    checksum = 14695981039346656037
    for byte in fields:
        checksum = ((checksum ^ byte) * 1099511628211) & WORD_MASK
    return fields + CHECKSUM.pack(checksum)


def write_wal(path, records, workload):
    keys = range(records)
    if workload == "descending":
        keys = reversed(keys)
    elif workload == "shuffled":
        keys = list(keys)
        random.Random(1847).shuffle(keys)
    with path.open("wb") as wal:
        for sequence, key in enumerate(keys, 1):
            fields = FIELDS.pack(0x314C41574F564C41, sequence, key, 0, key ^ MASK)
            wal.write(with_checksum(fields))


def load_baseline(path):
    groups = {}
    with path.open(newline="") as source:
        for row in csv.DictReader(source):
            key = (int(row["records"]), row["workload"])
            ns = int(row["ns"])
            if ns <= 0:
                raise ValueError("baseline contains a nonpositive time")
            groups.setdefault(key, []).append(ns)
    return {key: median(times) for key, times in groups.items()}


def run(out, cases, trials, repair_tail):
    cpu = min(os.sched_getaffinity(0))
    os.sched_setaffinity(0, {cpu})
    order = list(cases)
    random.Random(41).shuffle(order)
    medians = {}
    with tempfile.TemporaryDirectory() as scratch, out.open("w", newline="") as output:
        writer = csv.writer(output, lineterminator="\n")
        writer.writerow(("records", "workload", "trial", "ns", "cpu"))
        for records, workload in order:
            database = Path(scratch) / f"{records}-{workload}"
            database.mkdir()
            wal_path = database / "WAL"
            write_wal(wal_path, records, workload.removesuffix("-repair"))
            # The marker covers complete frames before any repair tail is added.
            marker = MARKER_FIELDS.pack(0x31544D434F564C41, wal_path.stat().st_size)
            (database / "WAL.commit").write_bytes(with_checksum(marker))
            command = [BINARY, database, str(records), str(trials)]
            if repair_tail:
                with wal_path.open("ab") as wal:
                    wal.write(b"ALVOWAL1\x00\x00\x00")
                command.append("--repair-tail")
            result = subprocess.run(command,
                                    stdout=subprocess.PIPE, text=True, check=True)
            samples = [int(line) for line in result.stdout.splitlines()]
            if len(samples) != trials or min(samples) <= 0:
                raise RuntimeError(f"invalid timing samples for {records} {workload}")
            writer.writerows((records, workload, trial, ns, cpu)
                             for trial, ns in enumerate(samples, 1))
            output.flush()
            medians[records, workload] = median(samples)
    return medians


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--out", required=True, type=Path, help="write raw timing samples to this CSV")
    cli.add_argument("--sizes", type=int, nargs="+", default=[5000, 10000, 20000])
    cli.add_argument("--trials", type=int, default=5)
    cli.add_argument("--repair-tail", action="store_true", help="repair a torn tail on every sample")
    cli.add_argument("--baseline", type=Path, help="compare medians with a prior run")
    cli.add_argument("--max-slowdown", type=float, help="fail if any median exceeds this baseline ratio")
    args = cli.parse_args()
    if min(args.sizes) < 1 or args.trials < 1 or len(args.sizes) != len(set(args.sizes)):
        cli.error("use positive, distinct sizes and a positive trial count")
    if args.max_slowdown is not None and (args.baseline is None or not isfinite(args.max_slowdown)
                                         or args.max_slowdown < 1):
        cli.error("--max-slowdown requires --baseline and a finite ratio of at least 1")
    workloads = tuple(f"{name}-repair" if args.repair_tail else name for name in WORKLOADS)
    cases = [(size, workload) for size in sorted(args.sizes) for workload in workloads]
    baseline = None
    if args.baseline:
        if args.baseline.resolve() == args.out.resolve():
            cli.error("write results to a different path than --baseline")
        try:
            baseline = load_baseline(args.baseline)
        except (OSError, KeyError, ValueError) as error:
            cli.error(f"invalid baseline: {error}")
        missing = set(cases) - baseline.keys()
        if missing:
            cli.error(f"baseline is missing cases: {sorted(missing)}")
    medians = run(args.out, cases, args.trials, args.repair_tail)
    print("records workload median_ms ns_per_record" + (" baseline_ratio" if baseline else ""))
    regressed = []
    for records, workload in cases:
        ns = medians[records, workload]
        ratio = ns / baseline[records, workload] if baseline else None
        comparison = f" {ratio:.3f}x" if ratio is not None else ""
        print(f"{records:7d} {workload:10s} {ns / 1e6:9.3f} {ns / records:13.1f}{comparison}")
        if args.max_slowdown is not None and ratio > args.max_slowdown:
            regressed.append(f"{records} {workload} ({ratio:.3f}x)")
    if regressed:
        raise SystemExit("Replay exceeded the requested slowdown: " + ", ".join(regressed))


if __name__ == "__main__":
    main()
