#!/usr/bin/env python3
"""Compare exact-size v3 cursor writers with the stock compaction controls."""

import argparse
import csv
import os
from pathlib import Path
import random
from statistics import median
import tempfile

import compaction as suite

CURSOR = suite.ROOT / "lean/.lake/build/bin/alvoki-compaction-cursor"
LEAN = suite.BINARIES["lean"]
RUST = suite.BINARIES["rust"]

WRITERS = {
    "lean-rows": (LEAN, "rows"),
    "lean-spans": (LEAN, "spans"),
    "rust-rows": (RUST, "rows"),
    "rust-spans": (RUST, "spans"),
    "cursor-copy": (CURSOR, "cursor-copy"),
    "cursor-store": (CURSOR, "cursor-store"),
}
PIPELINES = {
    "lean-pipeline": (LEAN, "pipeline"),
    "rust-pipeline": (RUST, "pipeline"),
    "cursor-pipeline": (CURSOR, "cursor-pipeline"),
}
ENCODERS = {
    "encode-append": (CURSOR, "encode-append"),
    "encode-cursor": (CURSOR, "encode-cursor"),
    "encode-rust": (RUST, "encode"),
}
LIST_ENCODERS = {
    "encode-list-append": (CURSOR, "encode-list-append"),
    "encode-list-cursor": (CURSOR, "encode-list-cursor"),
}


def check_output(variants, expected, paths, floor, snapshot):
    for name, (executable, mode) in variants.items():
        paths[2].unlink(missing_ok=True)
        suite.invoke(executable, "check-" + mode, paths, floor, snapshot)
        if paths[2].read_bytes() != expected:
            raise RuntimeError(f"{name} output differs from the v3 oracle")


def check_variants(paths, left, right, floor, snapshot, list_input):
    left_bytes = suite.encoded(left)
    paths[0].write_bytes(left_bytes)
    paths[1].write_bytes(suite.encoded(right))
    retained, checksum, _, _, _ = suite.oracle(left, right, floor, snapshot)
    if list_input:
        check_output(LIST_ENCODERS, left_bytes, paths, floor, snapshot)
        return dict.fromkeys(LIST_ENCODERS, suite.tag(left_bytes)), len(retained)
    expected = suite.encoded(retained)
    check_output(WRITERS, expected, paths, floor, snapshot)
    check_output(ENCODERS, left_bytes, paths, floor, snapshot)
    for name, (executable, mode) in PIPELINES.items():
        result = suite.invoke(executable, mode, paths, floor, snapshot)
        if int(result.stdout.split()[1]) != checksum:
            raise RuntimeError(f"{name} visible rows differ from the v3 oracle")
    return {
        **dict.fromkeys(WRITERS, suite.tag(expected)),
        **dict.fromkeys(ENCODERS, suite.tag(left_bytes)),
        **dict.fromkeys(PIPELINES, checksum),
    }, len(retained)


def fixtures(paths, list_input):
    high = (1 << 64) - 1
    left = [(0, 19, 1, 0), (0, 8, 0, 2), (0, 3, 0, 90), (2, 12, 0, 3), (high, high, 0, 25)]
    right = [(0, 21, 0, 4), (0, 8, 1, 0), (1, 10, 1, 0), (1, 1, 0, 8), (2, 14, 1, 0), (high, high, 1, 0)]
    cases = [([], [], 0, 0), (left, [], 5, 10), ([], right, 0, 9)]
    cases += [(left, right, 7, snapshot) for snapshot in (7, 8, 10, 12, 14, 19, 21, high)]
    cases += [(a, b, floor, snapshot) for _, a, b, floor, snapshot in suite.workloads(1031)]
    for a, b, floor, snapshot in cases:
        check_variants(paths, a, b, floor, snapshot, list_input)
    paths[0].write_bytes(suite.HEADER.pack(1, 3))
    paths[1].write_bytes(suite.encoded([]))
    modes = LIST_ENCODERS if list_input else ("cursor-copy", "cursor-store", "cursor-pipeline", "encode-cursor")
    for mode in modes:
        result = suite.invoke(CURSOR, mode, paths, 0, 0, check=False)
        if result.returncode == 0:
            raise RuntimeError(f"{mode} accepted a truncated v3 input")
    print(f"Passed {len(cases)} exact cursor fixtures and rejected truncated input.")


def run(paths, output, sizes, batches, trials, list_input):
    cpu = min(os.sched_getaffinity(0))
    os.sched_setaffinity(0, {cpu})
    rng = random.Random(443)
    variants = LIST_ENCODERS if list_input else WRITERS | PIPELINES | ENCODERS
    with output.open("w", newline="") as stream:
        writer = csv.writer(stream, lineterminator="\n")
        writer.writerow(("records", "profile", "retained", "left_records", "variant",
                         "batch", "position", "trial", "ns", "checksum", "cpu"))
        for size in sizes:
            for profile, left, right, floor, snapshot in suite.workloads(size):
                expected, retained = check_variants(paths, left, right, floor, snapshot, list_input)
                for batch in range(1, batches + 1):
                    order = list(variants)
                    rng.shuffle(order)
                    for position, name in enumerate(order, 1):
                        executable, mode = variants[name]
                        result = suite.invoke(executable, mode, paths, floor, snapshot, trials + 1)
                        rows = result.stdout.splitlines()
                        if len(rows) != trials + 1:
                            raise RuntimeError(f"{name} produced {len(rows)} timings")
                        for trial, row in enumerate(rows[1:], 1):
                            ns, checksum = map(int, row.split())
                            if ns <= 0 or checksum != expected[name]:
                                raise RuntimeError(f"{name} produced an invalid timing or result")
                            writer.writerow((size, profile, retained, len(left), name,
                                             batch, position, trial, ns, checksum, cpu))
                    stream.flush()
                print(f"Measured {size} {profile} on CPU {cpu}.", flush=True)


def summarize(path):
    groups = {}
    with path.open() as stream:
        for row in csv.DictReader(stream):
            key = tuple(row[k] for k in ("records", "profile", "variant"))
            groups.setdefault(key, []).append(int(row["ns"]))
    for (records, profile, variant), times in sorted(groups.items()):
        print(f"{records:>8} {profile:>16} {variant:>17} {median(times) / 1e6:8.3f} ms")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path)
    parser.add_argument("--summarize", type=Path)
    parser.add_argument("--sizes", nargs="+", type=int, default=[100_000, 1_000_000])
    parser.add_argument("--batches", type=int, default=3)
    parser.add_argument("--trials", type=int, default=3)
    parser.add_argument("--list-input", action="store_true", help="measure the two Lean List encoders")
    args = parser.parse_args()
    if args.summarize:
        summarize(args.summarize)
        return
    if min(*args.sizes, args.batches, args.trials) < 1:
        parser.error("sizes, batches and trials must be positive")
    with tempfile.TemporaryDirectory() as scratch:
        paths = tuple(Path(scratch) / name for name in ("left", "right", "output"))
        fixtures(paths, args.list_input)
        if args.out:
            run(paths, args.out, args.sizes, args.batches, args.trials, args.list_input)


if __name__ == "__main__":
    main()
