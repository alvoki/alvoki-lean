#!/usr/bin/env python3
import argparse
import bisect
import csv
import os
from pathlib import Path
import random
from statistics import median
import subprocess
import sys
import tempfile

from support import BLOCK_BINARIES as BINARIES
from support import ROOT, measured
from generate import WORD_MASK, block, columnar, dataset, workloads

LEAN = ROOT / "lean/.lake/build/bin/alvoki-opt"
RUST = ROOT / "rust/target/release/alvoki-opt"
CHECKED = BINARIES["rust"]
MATERIALIZE = [(LEAN, "decode-pair"), (LEAN, "decode-scalar"), (LEAN, "decode-machine"), (RUST, "decode-pair")]
STREAM = [(LEAN, "decode-stream"), (LEAN, "stream-machine"), (RUST, "stream-machine")]
VALIDATE = [(LEAN, "validate-base"), (LEAN, "validate-carry"),
            (LEAN, "validate-machine"), (RUST, "validate-machine")]
POINT = [(CHECKED, "point"), (LEAN, "point-base"), (LEAN, "point-nat"),
         (LEAN, "point-usize"), (LEAN, "point-machine"), (RUST, "point-machine")]
RANGE = [(CHECKED, "range"), (LEAN, "range-machine"), (RUST, "range-machine")]
READ = [(LEAN, "read-checked"), (LEAN, "read-guarded"),
        (LEAN, "read-machine"), (RUST, "read-wide")]
WRITE = [(LEAN, "write-loop"), (LEAN, "write-unrolled"), (LEAN, "write-scalar"), (LEAN, "write-indexed"), (RUST, "write-wide")]


def label(binary, mode):
    return f"{'lean' if binary == LEAN else 'rust'}-{mode}"


def check(directory):
    rng = random.Random(721)
    data, queries = directory / "data", directory / "queries"
    cases = [[], [(0, 0)], [(0, WORD_MASK), (WORD_MASK, 1)]]
    for size in (7, 31, 128, 1024):
        keys = sorted(rng.sample(range(size * 4), size))
        cases.append([(key, rng.getrandbits(64)) for key in keys])
    for records in cases:
        keys = [key for key, _ in records]
        targets = [0, 1, WORD_MASK - 4, WORD_MASK, *keys]
        targets += [rng.randrange(max(1, len(records) * 4)) for _ in range(128)]
        queries.write_bytes(block(list(enumerate(targets))))
        values = dict(records)
        point_sum = sum(values.get(key, 0) for key in targets) & WORD_MASK
        stream_sum = sum(k ^ v for k, v in records) & WORD_MASK
        for layout in (block, columnar):
            encoded = layout(records)
            data.write_bytes(encoded)
            encoded_output = directory / "encoded"
            for mode in ("check-write", "check-indexed"):
                subprocess.run([LEAN, mode, data, queries, encoded_output, "1"], check=True)
                assert encoded_output.read_bytes() == block(records), (layout, mode)
            for width in (0, 8, WORD_MASK):
                expected = []
                for key in targets:
                    lo = bisect.bisect_left(keys, key)
                    hi = bisect.bisect_left(keys, min(key + width, WORD_MASK))
                    scan = sum(k ^ v for k, v in records[lo:hi]) & WORD_MASK
                    expected.append(f"{values.get(key, '-')} {lo} {hi} {scan}")
                for binary in (LEAN, RUST):
                    actual = subprocess.check_output([binary, "check", data, queries, str(width), "1"], text=True)
                    assert actual.splitlines() == expected, (binary, layout, width)
            wide_sum = sum(int.from_bytes(encoded[i:i + 8], "little")
                           for i in range(17, len(encoded), 16)) & WORD_MASK
            jobs = ([(POINT[-2:], point_sum), (STREAM[-2:], stream_sum),
                     (VALIDATE[-2:], len(records)), (READ[-2:], wide_sum)])
            if layout == block:
                jobs = [(POINT, point_sum), (MATERIALIZE + STREAM, stream_sum),
                        (VALIDATE, len(records)), (READ, wide_sum), (WRITE, 1)]
            for modes, expected_checksum in jobs:
                for binary, mode in modes:
                    samples, _, _ = measured(label(binary, mode), binary, mode, data, queries, 8, 1)
                    assert int(samples[0].split()[1]) == expected_checksum, (binary, mode, records)
    malformed_count = 0
    for layout in (block, columnar):
        valid = layout([(0, 1)])
        malformed = [
            valid[:15], valid[:-1], valid + b"\x00", b"\xff" * 8 + valid[8:],
            layout([(8, 1), (7, 2)]), layout([(8, 1), (8, 2)]),
            valid[:8] + (3).to_bytes(8, "little") + valid[16:],
        ]
        for invalid in malformed:
            data.write_bytes(invalid)
            malformed_count += 1
            for binary in (LEAN, RUST):
                result = subprocess.run([binary, "validate-machine", data, queries, "0", "1"],
                                        capture_output=True)
                assert result.returncode != 0, binary
    print(f"Passed {len(cases) * 2} valid and {malformed_count} malformed layout fixtures.")


def run(directory, destination, sizes, trials):
    cpu = min(os.sched_getaffinity(0))
    os.sched_setaffinity(0, {cpu})
    rng = random.Random(7124)
    data, columns, queries = (directory / p for p in ("data", "columns", "queries"))
    with destination.open("w", newline="") as out:
        writer = csv.writer(out, lineterminator="\n")
        writer.writerow(("records", "workload", "layout", "variant", "trial", "ns",
                         "operations", "checksum", "cpu", "peak_rss_kib"))
        for size in sizes:
            records = dataset(size)
            data.write_bytes(block(records))
            columns.write_bytes(columnar(records))
            targets = workloads(size)
            jobs = [(name, POINT, query_keys, 0) for name, query_keys in targets.items() if name != "large"]
            jobs += [
                ("small_range", RANGE, targets["mixed"], 8),
                ("large_range", RANGE, targets["large"], 4096),
                ("validate", VALIDATE, [], 0), ("decode_consume", MATERIALIZE + STREAM, [], 0),
                ("read_unaligned", READ, [], 0), ("encode", WRITE, [], 0),
            ]
            for workload, variants, keys, width in jobs:
                queries.write_bytes(block(list(enumerate(keys))))
                options = [(data, binary, mode) for binary, mode in variants]
                if workload in ("mixed", "sequential", "small_range", "large_range", "validate", "decode_consume"):
                    options += [(columns, binary, mode) for binary, mode in variants
                                if binary != CHECKED and mode.endswith("-machine")]
                rng.shuffle(options)
                checksums = set()
                for fixture, binary, mode in options:
                    name = label(binary, mode)
                    samples, rss, _ = measured(name, binary, mode, fixture, queries, width, trials + 1)
                    assert len(samples) == trials + 1, (name, workload)
                    for trial, line in enumerate(samples[1:], 1):
                        ns, checksum = map(int, line.split())
                        checksums.add(checksum)
                        writer.writerow((size, workload, "interleaved" if fixture == data else "columns",
                                         name, trial, ns, len(keys) or size, checksum, cpu, rss))
                assert len(checksums) == 1, (size, workload, checksums)
                out.flush()


def summarize(path):
    groups = {}
    with path.open() as source:
        for row in csv.DictReader(source):
            key = tuple(row[name] for name in ("records", "workload", "layout", "variant"))
            groups.setdefault(key, []).append(row)
    writer = csv.writer(sys.stdout, lineterminator="\n")
    writer.writerow(("records", "workload", "layout", "variant", "trials", "min_ns_per_unit",
                     "median_ns_per_unit", "max_ns_per_unit", "peak_rss_kib"))
    for group, rows in sorted(groups.items(), key=lambda pair: (int(pair[0][0]), *pair[0][1:])):
        times = [int(row["ns"]) / int(row["operations"]) for row in rows]
        writer.writerow((*group, len(rows), f"{min(times):.3f}", f"{median(times):.3f}",
                         f"{max(times):.3f}", rows[0]["peak_rss_kib"]))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path)
    parser.add_argument("--summarize", type=Path)
    parser.add_argument("--sizes", nargs="+", type=int, default=[1000, 100_000, 1_000_000])
    parser.add_argument("--trials", type=int, default=7)
    args = parser.parse_args()
    if args.summarize:
        summarize(args.summarize)
        return
    if min(args.sizes) < 1 or args.trials < 1:
        parser.error("positive sizes and trial count are required")
    with tempfile.TemporaryDirectory() as temp:
        directory = Path(temp)
        check(directory)
        if args.out:
            run(directory, args.out, args.sizes, args.trials)


if __name__ == "__main__":
    main()
