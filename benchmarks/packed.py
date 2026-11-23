#!/usr/bin/env python3
import argparse
import csv
import os
from pathlib import Path
import random
from statistics import median
import subprocess
import sys
import tempfile

from run import ROOT, measured
from generate import WORD_MASK, block, dataset, workloads

LEAN = ROOT / "lean/.lake/build/bin/alvoki-packed"
RUST = ROOT / "rust/target/release/alvoki-packed"
SCAN = [(binary, mode) for binary in (LEAN, RUST) for mode in
        ("retain-scan", "copy-scan", "owned-scan", "chunk-build-scan", "chunk-scan")]
LOOKUP = [(LEAN, "lookup-packed"), (LEAN, "lookup-chunked"), (LEAN, "lookup-chunk-within"), (RUST, "lookup-packed")]
MERGE = [(binary, mode) for binary in (LEAN, RUST) for mode in ("merge", "fast-merge")]
ENCODE = [(LEAN, "encode-indexed"), (LEAN, "encode-c"), (LEAN, "encode-batch-c"), (RUST, "encode")]
FILL = [(LEAN, "fill-indexed"), (LEAN, "fill-c"), (LEAN, "fill-batch-c"), (RUST, "fill")]
INIT = [(LEAN, "init-lean"), (LEAN, "init-c"), (RUST, "init")]


def name(binary, mode):
    return f"{'lean' if binary == LEAN else 'rust'}-{mode}"


def run_once(binary, mode, data, aux, output):
    subprocess.run([binary, mode, data, aux, output, "1"], check=True,
                   env={key: value for key, value in os.environ.items() if key != "ALVOKI_RSS"})


def merged_records(left, right):
    return sorted((dict(left) | dict(right)).items())


def checksum(records):
    return sum(k ^ v for k, v in records) & WORD_MASK


def check(directory):
    data, aux, output = (directory / label for label in ("data", "aux", "output"))
    rng = random.Random(223)
    cases = [[], [(0, WORD_MASK)], [(0, 0), (WORD_MASK, 42)]]
    for size in (31, 255, 256, 257, 1025):
        keys = sorted(rng.sample(range(size * 4), size))
        cases.append([(key, rng.getrandbits(64)) for key in keys])
    for records in cases:
        fixture = block(records)
        data.write_bytes(fixture)
        for mode in ("check-copy", "check-chunks", "check-c", "check-indexed",
                     "check-fill-indexed", "check-batch-c", "check-fill-batch-c", "check-ffi"):
            run_once(LEAN, mode, data, aux, output)
            assert output.read_bytes() == fixture, (mode, len(records))
        expected = checksum(records)
        for binary, mode in SCAN:
            samples, _, _ = measured(name(binary, mode), binary, mode, data, aux, 0, 1)
            assert int(samples[0].split()[1]) == expected, (binary, mode, len(records))
        targets = [0, 1, WORD_MASK, *dict(records)]
        targets += [rng.randrange(0, max(1, len(records) * 4)) for _ in range(64)]
        aux.write_bytes(block(list(enumerate(targets))))
        expected = sum(dict(records).get(key, 0) for key in targets) & WORD_MASK
        for binary, mode in LOOKUP:
            samples, _, _ = measured(name(binary, mode), binary, mode, data, aux, 0, 1)
            assert int(samples[0].split()[1]) == expected, (mode, len(records))
    merge_cases = [
        ([], []), ([], cases[-1]), (cases[-1], []), (cases[2], cases[1]),
        (cases[-1], cases[-2]), (cases[-2], cases[-1]),
        (cases[-2], [(k, WORD_MASK ^ v) for k, v in cases[-2]]),
        ([(0, 1), (1, 2)], [(2, 3), (WORD_MASK, 4)]),
        ([(2, 3), (WORD_MASK, 4)], [(0, 1), (1, 2)]),
    ]
    for left, right in merge_cases:
        data.write_bytes(block(left))
        aux.write_bytes(block(right))
        for binary, mode in MERGE:
            run_once(binary, "check-" + mode, data, aux, output)
            assert output.read_bytes() == block(merged_records(left, right)), binary
    print(f"Passed {len(cases)} storage fixtures and {len(merge_cases)} exact merge fixtures.")


def merge_inputs(size, order):
    half = size // 2
    records = dataset(size)
    if order == "alternating":
        return records[::2], records[1::2]
    if order == "disjoint":
        return records[:half], records[half:]
    # The right side overwrites keys shared with the last quarter of the left side.
    return records[:half], [(k, v ^ WORD_MASK) for k, v in records[size // 4:size // 4 + size - half]]


def run(directory, out, sizes, trials):
    cpu = min(os.sched_getaffinity(0))
    os.sched_setaffinity(0, {cpu})
    rng = random.Random(834)
    data, aux = (directory / label for label in ("data", "aux"))
    with out.open("w", newline="") as result:
        writer = csv.writer(result, lineterminator="\n")
        writer.writerow(("records", "workload", "variant", "trial", "ns", "operations",
                         "checksum", "cpu", "peak_rss_kib"))
        for size in sizes:
            records = dataset(size)
            data.write_bytes(block(records))
            targets = workloads(size)["mixed"]
            aux.write_bytes(block(list(enumerate(targets))))
            jobs = [("scan", SCAN, size), ("point", LOOKUP, len(targets)),
                    ("encode", ENCODE, size), ("fill", FILL, size), ("init", INIT, size),
                    *(("merge-" + order, MERGE, size)
                      for order in ("alternating", "overlap", "disjoint"))]
            for workload, variants, units in jobs:
                if workload.startswith("merge-"):
                    left, right = merge_inputs(size, workload.removeprefix("merge-"))
                    assert len(left) + len(right) == size
                    data.write_bytes(block(left))
                    aux.write_bytes(block(right))
                options = list(variants)
                rng.shuffle(options)
                checksums = set()
                for binary, mode in options:
                    label = name(binary, mode)
                    samples, rss, _ = measured(label, binary, mode, data, aux, 0, trials + 1)
                    assert len(samples) == trials + 1, (label, workload)
                    for trial, line in enumerate(samples[1:], 1):
                        ns, tag = map(int, line.split())
                        checksums.add(tag)
                        writer.writerow((size, workload, label, trial, ns, units, tag, cpu, rss))
                assert len(checksums) == 1, (size, workload, checksums)
                result.flush()


def summarize(path):
    groups = {}
    with path.open() as source:
        for row in csv.DictReader(source):
            key = tuple(row[name] for name in ("records", "workload", "variant"))
            groups.setdefault(key, []).append(row)
    writer = csv.writer(sys.stdout, lineterminator="\n")
    writer.writerow(("records", "workload", "variant", "trials", "min_ms", "median_ms", "max_ms",
                     "median_ns_per_unit", "peak_rss_kib"))
    for group, rows in sorted(groups.items(), key=lambda pair: (int(pair[0][0]), *pair[0][1:])):
        times = [int(row["ns"]) for row in rows]
        writer.writerow((*group, len(rows), f"{min(times) / 1e6:.6f}", f"{median(times) / 1e6:.6f}",
                         f"{max(times) / 1e6:.6f}", f"{median(times) / int(rows[0]['operations']):.3f}",
                         rows[0]["peak_rss_kib"]))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path)
    parser.add_argument("--summarize", type=Path)
    parser.add_argument("--sizes", nargs="+", type=int, default=[1000, 100_000, 1_000_000])
    parser.add_argument("--trials", type=int, default=9)
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
