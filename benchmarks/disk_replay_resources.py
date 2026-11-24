#!/usr/bin/env python3
"""Measure native reopen's process peak RSS and WAL read bytes in separate opens."""

import argparse
from collections import Counter
import csv
import os
from pathlib import Path
import random
import re
from shutil import copytree, which
import subprocess
import tempfile

from disk_replay import FRAME_SIZE, WORKLOADS, seed_segments


READ_SYSCALLS = ("read", "pread64", "readv", "preadv", "preadv2")
READ_CALL = re.compile(
    rf"^\s*(\d+)(?:\s+)({'|'.join(READ_SYSCALLS)})\(\d+<([^>]+)>,"
)
RESUMED_CALL = re.compile(r"^\s*(\d+)\s+<\.\.\. (\w+) resumed>")
READ_RESULT = re.compile(r"\s+=\s+(-?\d+)(?:\s|$)")
RSS_LINE = re.compile(r"VmHWM:\s+(\d+)\s+kB\s*")


def wal_reads(trace, directory):
    """Count successful read results by canonical WAL filename."""
    wal_path = re.compile(re.escape(str(directory.resolve())) + r"/WAL-segment-(?:0|[1-9][0-9]*)$")
    byte_counts = Counter()
    call_counts = Counter()
    pending = {}
    with trace.open() as stream:
        for line in stream:
            call = READ_CALL.match(line)
            resumed = RESUMED_CALL.match(line)
            if call and wal_path.fullmatch(call[3]):
                issue = (call[1], call[2])
                name = Path(call[3]).name
                if line.rstrip().endswith("<unfinished ...>"):
                    pending[issue] = name
                    continue
            elif resumed and (resumed[1], resumed[2]) in pending:
                name = pending.pop((resumed[1], resumed[2]))
            else:
                continue
            result = READ_RESULT.search(line)
            if not result:
                raise ValueError(f"cannot parse segment read result: {line.rstrip()}")
            count = int(result[1])
            if count >= 0:
                byte_counts[name] += count
                call_counts[name] += 1
    if pending:
        raise ValueError("trace ended with an unfinished segment read")
    return byte_counts, call_counts


def measure(binary, template, keeper, tail_bytes, records, trace):
    with tempfile.TemporaryDirectory(dir=template.parent) as scratch:
        directory = Path(scratch) / "db"
        copytree(template, directory)
        keeper_path = directory / keeper
        # Zeros beyond the marker represent arbitrary uncommitted bytes.
        with keeper_path.open("r+b") as stream:
            stream.truncate((template / keeper).stat().st_size + tail_bytes)
        command = [binary, directory, str(records), "--rss-once"]
        trace_path = Path(scratch) / "reads"
        if trace:
            command = ["strace", "-f", "-qq", "-yy", "-s", "0", "-e",
                       "trace=" + ",".join(READ_SYSCALLS), "-o", trace_path, *command]
        output = subprocess.check_output(command, text=True)
        rss = RSS_LINE.fullmatch(output)
        if not rss or int(rss[1]) <= 0:
            raise ValueError(f"invalid native RSS output: {output!r}")
        for source in template.iterdir():
            if source.read_bytes() != (directory / source.name).read_bytes():
                raise ValueError(f"reopen changed selected bytes in {source.name}")
        return wal_reads(trace_path, directory) if trace else int(rss[1])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", required=True, type=Path, help="before alvoki-disk-replay executable")
    parser.add_argument("--candidate", required=True, type=Path, help="after alvoki-disk-replay executable")
    parser.add_argument("--out", required=True, type=Path, help="write raw measurements to this CSV")
    parser.add_argument("--records", type=int, default=2048)
    parser.add_argument("--workload", choices=WORKLOADS, default="ascending")
    parser.add_argument("--segments", type=int, nargs="+", default=[1, 8, 32])
    parser.add_argument("--tail-bytes", type=int, nargs="+", default=[0, 11, 8 << 20, 32 << 20])
    parser.add_argument("--trials", type=int, default=3)
    parser.add_argument("--cpu", type=int, default=min(os.sched_getaffinity(0)))
    args = parser.parse_args()
    if args.trials < 1 or min(args.segments) < 1 or max(args.segments) > args.records:
        parser.error("use positive trials and segment counts no greater than the record count")
    if min(args.tail_bytes) < 0 or len(args.tail_bytes) != len(set(args.tail_bytes)):
        parser.error("use distinct nonnegative tail byte counts")
    if len(args.segments) != len(set(args.segments)):
        parser.error("use distinct segment counts")
    if which("strace") is None:
        parser.error("strace is required to count returned WAL bytes")
    os.sched_setaffinity(0, {args.cpu})
    binaries = (args.base.resolve(), args.candidate.resolve())
    cases = [(segments, tail) for segments in args.segments for tail in args.tail_bytes]
    rng = random.Random(20261127)
    with tempfile.TemporaryDirectory(prefix="alvoki-replay-resources-") as scratch, args.out.open(
            "w", newline="") as output:
        writer = csv.writer(output, lineterminator="\n")
        writer.writerow(("records", "workload", "segments", "tail_bytes", "pair", "order", "arm", "cpu",
                         "peak_rss_kib", "wal_read_bytes", "keeper_read_bytes", "wal_read_calls"))
        for pair in range(1, args.trials + 1):
            rng.shuffle(cases)
            for segments, tail in cases:
                with tempfile.TemporaryDirectory(dir=scratch) as template:
                    fixture = Path(template)
                    _, keeper = seed_segments(fixture, args.records, args.workload, segments)
                    committed = args.records * FRAME_SIZE
                    arms = [0, 1]
                    rng.shuffle(arms)
                    for order, arm in enumerate(arms, 1):
                        rss = measure(binaries[arm], fixture, keeper.name, tail, args.records, trace=False)
                        reads, calls = measure(binaries[arm], fixture, keeper.name, tail, args.records, trace=True)
                        total = sum(reads.values())
                        if total < committed:
                            raise ValueError(f"counted {total} WAL read bytes for {committed} committed bytes")
                        writer.writerow((args.records, args.workload, segments, tail, pair, order,
                                         ("base", "candidate")[arm], args.cpu, rss, total, reads[keeper.name],
                                         sum(calls.values())))
                        output.flush()


if __name__ == "__main__":
    main()
