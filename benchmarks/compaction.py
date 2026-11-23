#!/usr/bin/env python3
"""Versioned compaction fixtures and deterministic storage workload proxies."""

import argparse
import csv
from itertools import groupby
import os
from pathlib import Path
import random
from statistics import median
from struct import Struct
import subprocess
import tempfile

from support import ROOT, tag
from generate import WORD_MASK

HEADER = Struct("<QQ")
ROW = Struct("<QQQQ")
BINARIES = {
    "lean": ROOT / "lean/.lake/build/bin/alvoki-compaction",
    "rust": ROOT / "rust/target/release/alvoki-compaction",
}
PROFILES = ("range-ingest", "hot-updates", "delete-reinsert", "uniform-mix")


def encoded(rows):
    return HEADER.pack(len(rows), 3) + b"".join(ROW.pack(*row) for row in rows)


def workloads(size):
    for n, profile in enumerate(PROFILES):
        rng = random.Random(1847 + n)
        base = size * 2 // 3
        left = [(2 * i, i + 1, 0, rng.getrandbits(64)) for i in range(base)]
        right = []
        for i in range(size - base):
            deleted = False
            if profile == "range-ingest":
                key = 2 * (base + i) if i % 4096 < 3072 else 2 * ((i * 31) % max(base, 1))
            elif profile == "uniform-mix":
                key = rng.randrange(max(2 * base, 1))
            else:
                # Repeated changes within a small hot set, with a colder tail.
                hot = max(base // 50, 1)
                width = hot if rng.random() < 0.85 else max(base, 1)
                key = 2 * rng.randrange(width)
                deleted = profile == "delete-reinsert" and rng.random() < 0.35
            right.append((key, base + i + 1, int(deleted), 0 if deleted else rng.getrandbits(64)))
        right.sort(key=lambda row: (row[0], -row[1]))
        floor = size - (size - base) // 4
        snapshot = floor if profile == "delete-reinsert" else size
        yield profile, left, right, floor, snapshot


def oracle(left, right, floor, snapshot):
    entries = {}
    for side, rows in enumerate((left, right)):
        for index, row in enumerate(rows):
            entries[row[:2]] = (row, side, index)
    ordered = sorted(entries.values(), key=lambda item: (item[0][0], -item[0][1]))
    kept, visible = [], []
    for _, history in groupby(ordered, key=lambda item: item[0][0]):
        covered = False
        seen = False
        for item in history:
            row, _, _ = item
            if not covered:
                kept.append(item)
                covered = row[1] <= floor
            if not seen and row[1] <= snapshot:
                seen = True
                if row[2] == 0:
                    visible.append(row)
    spans = []
    for _, side, index in kept:
        if spans and (side, index) == spans[-1][:2]:
            spans[-1] = (side, index + 1, spans[-1][2] + 1)
        else:
            spans.append((side, index + 1, 1))
    return (
        [row for row, _, _ in kept],
        sum(key ^ value for key, _, _, value in visible) & WORD_MASK,
        len(visible), len(spans), sum(length == 1 for _, _, length in spans),
    )


def invoke(binary, mode, paths, floor, snapshot, reps=1, check=True):
    left, right, output = paths
    return subprocess.run(
        [binary, mode, left, right, str(floor), str(snapshot), output, str(reps)],
        text=True, capture_output=True, check=check,
    )


def check_case(paths, left, right, floor, snapshot):
    paths[0].write_bytes(encoded(left))
    paths[1].write_bytes(encoded(right))
    kept, checksum, visible, spans, singleton = oracle(left, right, floor, snapshot)
    expected = encoded(kept)
    for binary in BINARIES.values():
        for mode in ("rows", "spans"):
            invoke(binary, "check-" + mode, paths, floor, snapshot)
            assert paths[2].read_bytes() == expected, (binary, mode, floor)
        for mode in ("direct", "pipeline"):
            measured = int(invoke(binary, mode, paths, floor, snapshot).stdout.split()[1])
            assert measured == checksum, (binary, mode, floor, snapshot)
    return expected, checksum, visible, spans, singleton


def checks(paths):
    l = [(0, 19, 1, 0), (0, 8, 0, 2), (0, 3, 0, 90),
         (2, 12, 0, 3), (WORD_MASK, WORD_MASK, 0, 25)]
    r = [(0, 21, 0, 4), (0, 8, 1, 0), (1, 10, 1, 0), (1, 1, 0, 8),
         (2, 14, 1, 0), (WORD_MASK, WORD_MASK, 1, 0)]
    cases = [([], [], 0, 0), (l, [], 5, 10), ([], r, 0, 9)]
    cases += [(l, r, 7, snapshot) for snapshot in (7, 8, 10, 12, 14, 19, 21, WORD_MASK)]
    cases += [(a, b, floor, snapshot) for _, a, b, floor, snapshot in workloads(1031)]
    for a, b, floor, snapshot in cases:
        check_case(paths, a, b, floor, snapshot)
    paths[1].write_bytes(encoded([]))
    bad = [
        b"", encoded([]) + b"\x00", HEADER.pack(1, 3), HEADER.pack(0, 1),
        encoded([(1, 1, 2, 0)]), encoded([(1, 1, 1, 1)]),
        encoded([(2, 1, 0, 0), (1, 1, 0, 0)]),
        encoded([(1, 1, 0, 0), (1, 1, 1, 0)]),
        encoded([(1, 1, 0, 0), (1, 2, 0, 0)]),
    ]
    for invalid in bad:
        paths[0].write_bytes(invalid)
        for binary in BINARIES.values():
            assert invoke(binary, "rows", paths, 0, 0, check=False).returncode != 0, binary
    paths[0].write_bytes(encoded([]))
    for binary in BINARIES.values():
        assert invoke(binary, "direct", paths, 1, 0, check=False).returncode != 0, binary
        assert invoke(binary, "direct", paths, 0, WORD_MASK + 1, check=False).returncode != 0, binary
    print(f"Passed {len(cases)} versioned compaction fixtures and {len(bad)} malformed runs.")


def run(paths, out, sizes, trials):
    cpu = min(os.sched_getaffinity(0))
    os.sched_setaffinity(0, {cpu})
    rng = random.Random(443)
    with out.open("w", newline="") as stream:
        writer = csv.writer(stream, lineterminator="\n")
        writer.writerow(("records", "workload", "variant", "trial", "ns", "checksum", "cpu",
                         "floor", "snapshot", "retained", "visible", "spans", "singletons"))
        for size in sizes:
            for profile, left, right, floor, snapshot in workloads(size):
                expected, checksum, visible, spans, singleton = check_case(
                    paths, left, right, floor, snapshot)
                retained = (len(expected) - HEADER.size) // ROW.size
                compacted = paths[0].with_name("compacted")
                empty = paths[0].with_name("empty")
                compacted.write_bytes(expected)
                empty.write_bytes(encoded([]))
                jobs = [(lang, mode) for lang in BINARIES for mode in ("rows", "spans", "direct", "pipeline")]
                jobs += [(lang, "read") for lang in BINARIES if lang != "lean-fixed"]
                rng.shuffle(jobs)
                for lang, mode in jobs:
                    args = ("direct", (compacted, empty, paths[2])) if mode == "read" else (mode, paths)
                    result = invoke(BINARIES[lang], *args, floor, snapshot, trials + 1)
                    lines = result.stdout.splitlines()
                    assert len(lines) == trials + 1, (lang, mode)
                    wanted = checksum if mode in ("direct", "pipeline", "read") else tag(expected)
                    for index, line in enumerate(lines[1:], 1):
                        ns, seen = map(int, line.split())
                        assert seen == wanted, (profile, lang, mode)
                        writer.writerow((size, profile, f"{lang}-{mode}", index, ns, seen, cpu,
                                         floor, snapshot, retained, visible, spans, singleton))
                stream.flush()


def summarize(path):
    groups = {}
    with path.open() as stream:
        for row in csv.DictReader(stream):
            key = tuple(row[k] for k in ("records", "workload", "variant"))
            groups.setdefault(key, []).append(int(row["ns"]))
    for (records, workload, variant), times in sorted(groups.items()):
        print(f"{records:>8} {workload:>16} {variant:>18} {median(times) / 1e6:8.3f} ms")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path)
    parser.add_argument("--fixed-copy", action="store_true")
    parser.add_argument("--summarize", type=Path)
    parser.add_argument("--sizes", nargs="+", type=int, default=[100_000, 1_000_000])
    parser.add_argument("--trials", type=int, default=9)
    args = parser.parse_args()
    if args.summarize:
        summarize(args.summarize)
        return
    if min(args.sizes) < 1 or args.trials < 1:
        parser.error("sizes and trials must be positive")
    if args.fixed_copy:
        BINARIES["lean-fixed"] = ROOT / "lean/.lake/build/bin/alvoki-compaction-fixed"
    with tempfile.TemporaryDirectory() as runner:
        paths = tuple(Path(runner) / name for name in ("left", "right", "out"))
        checks(paths)
        if args.out:
            run(paths, args.out, args.sizes, args.trials)


if __name__ == "__main__":
    main()
