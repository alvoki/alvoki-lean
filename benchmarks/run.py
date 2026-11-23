#!/usr/bin/env python3
import argparse
import bisect
import csv
import os
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "fixtures"))
from generate import WORD_MASK, block, dataset, workloads

BINARIES = {
    "rust": ROOT / "rust/target/release/alvoki-block",
    "lean-fast": ROOT / "lean/.lake/build/bin/alvoki",
    "lean": ROOT / "lean/.lake/build/bin/alvoki",
}


def invoke(label, binary, mode, data, queries, param, repeats, **kwargs):
    env = dict(os.environ, ALVOKI_FAST="1" if label == "lean-fast" else "0")
    env.pop("ALVOKI_RSS", None)
    return subprocess.run(
        [binary, mode, data, queries, str(param), str(repeats)],
        text=True, capture_output=True, env=env, **kwargs,
    )


def measured(label, binary, mode, data, queries, param, repeats):
    env = dict(os.environ, ALVOKI_FAST="1" if label == "lean-fast" else "0", ALVOKI_RSS="1")
    command = [binary, mode, data, queries, str(param), str(repeats)]
    start = time.perf_counter_ns()
    output = subprocess.run(command, text=True, capture_output=True, env=env, check=True)
    elapsed = time.perf_counter_ns() - start
    *samples, rss = output.stdout.splitlines()
    header, amount, unit = rss.split()
    assert (header, unit) == ("VmHWM:", "kB")
    return samples, int(amount), elapsed


def check(directory):
    rng = random.Random(918)
    cases = [[], [(0, 0)], [(1, 0), (WORD_MASK, WORD_MASK)]]
    for size in (2, 7, 16, 31, 128, 1024):
        keys = sorted(rng.sample(range(size * 4), size))
        cases.append([(key, rng.getrandbits(64)) for key in keys])
    data, queries, output = [directory / name for name in ("data", "queries", "encoded")]
    for records in cases:
        expected_bytes = block(records)
        data.write_bytes(expected_bytes)
        keys = [key for key, _ in records]
        values = dict(records)
        targets = [0, 1, WORD_MASK - 4, WORD_MASK, *keys]
        targets.extend(rng.randrange(max(1, len(keys) * 4)) for _ in range(128))
        queries.write_bytes(block(list(enumerate(targets))))
        expected = []
        for key in targets:
            lo = bisect.bisect_left(keys, key)
            hi = bisect.bisect_left(keys, min(key + 8, WORD_MASK))
            checksum = sum(k ^ v for k, v in records[lo:hi]) & WORD_MASK
            expected.append(f"{values.get(key, '-')} {lo} {hi} {checksum}")
        for label, binary in BINARIES.items():
            result = invoke(label, binary, "check", data, queries, output, 1, check=True)
            assert result.stdout.splitlines() == expected, (label, len(records))
            assert output.read_bytes() == expected_bytes, (label, len(records))
    invalid = [
        b"", b"\x00" * 15, b"\x00" * 16, block([]) + b"\x00",
        block([(1, 2)])[:-16], block([(2, 3), (1, 4)]),
        block([(1, 2), (1, 3)]), b"\xff" * 8 + block([])[8:],
    ]
    for malformed in invalid:
        data.write_bytes(malformed)
        for label, binary in BINARIES.items():
            assert invoke(label, binary, "validate", data, queries, 0, 1).returncode != 0, label
    print(f"Passed {len(cases)} valid and {len(invalid)} malformed fixtures across {len(BINARIES)} binaries.")


def run(directory, results, sizes, trials):
    data, queries = directory / "data", directory / "queries"
    cpu = min(os.sched_getaffinity(0))
    os.sched_setaffinity(0, {cpu})
    rng = random.Random(41)
    with results.open("w", newline="") as output:
        writer = csv.writer(output, lineterminator="\n")
        writer.writerow(("records", "workload", "language", "trial", "ns", "operations", "checksum", "cpu",
                         "process_peak_rss_kib", "process_wall_ns"))
        for size in sizes:
            data.write_bytes(block(dataset(size)))
            targets = workloads(size)
            jobs = [(name, "point", targets[name], 0) for name in ("hit", "miss", "mixed", "sequential")]
            jobs += [
                ("small_range", "range", targets["mixed"], 8),
                ("large_range", "range", targets["large"], 4096),
                *((name, name, [], 0) for name in ("encode", "decode", "validate", "load")),
            ]
            for name, mode, keys, width in jobs:
                queries.write_bytes(block(list(enumerate(keys))))
                order = list(BINARIES.items())
                rng.shuffle(order)
                checksums = set()
                for label, binary in order:
                    samples, rss, elapsed = measured(
                        label, binary, mode, data, queries, width, trials + 1
                    )
                    assert len(samples) == trials + 1
                    for trial, line in enumerate(samples[1:], 1):
                        ns, checksum = map(int, line.split())
                        checksums.add(checksum)
                        writer.writerow((size, name, label, trial, ns, len(keys) or 1, checksum, cpu, rss, elapsed))
                assert len(checksums) == 1, (size, name, checksums)
                output.flush()


def main():
    cli = argparse.ArgumentParser()
    cli.add_argument("--out", type=Path)
    cli.add_argument("--sizes", type=int, nargs="+", default=[1000, 100_000, 1_000_000])
    cli.add_argument("--trials", type=int, default=7)
    args = cli.parse_args()
    with tempfile.TemporaryDirectory() as scratch:
        directory = Path(scratch)
        check(directory)
        if args.out:
            run(directory, args.out, args.sizes, args.trials)


if __name__ == "__main__":
    main()
