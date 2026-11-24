#!/usr/bin/env python3
"""Compare four native wide accessors and matched stock Lean and Rust controls."""

import argparse
import csv
import os
from pathlib import Path
import random
from statistics import median
from struct import Struct
import subprocess
from tempfile import TemporaryDirectory

from support import ROOT, tag

HEADER = Struct("<QQ")
ROW = Struct("<QQQQ")
WORD = Struct("<Q")
MASK = 0xFEDCBA9876543210
VARIANTS = ("shifts", "shifts-assume", "memcpy", "memcpy-assume")


def fixture(count, seed):
    random_values = random.Random(seed)
    left_count = (count + 1) // 2
    right_count = count // 2
    block = bytearray(HEADER.size + ROW.size * count)
    changed = bytearray(len(block))
    left = bytearray(HEADER.size + ROW.size * left_count)
    right = bytearray(HEADER.size + ROW.size * right_count)
    for data, rows in ((block, count), (changed, count), (left, left_count), (right, right_count)):
        HEADER.pack_into(data, 0, rows, 3)
    for i in range(count):
        kind = int(i % 11 == 5)
        key = i if i + 1 != count else (1 << 64) - 1
        value = 0 if kind else random_values.getrandbits(64)
        offset = HEADER.size + ROW.size * i
        ROW.pack_into(block, offset, key, count - i, kind, value)
        ROW.pack_into(changed, offset, key, count - i, kind, 0 if kind else value ^ MASK)
        target = left if i % 2 == 0 else right
        ROW.pack_into(target, HEADER.size + ROW.size * (i // 2), key, count - i, kind, value)
    return block, changed, left, right


def invoke(binary, mode, left, right, output, trials, *, check=True):
    return subprocess.run(
        [binary, mode, left, right, output, str(trials)], check=check,
        text=True, capture_output=True,
    )


def prepare_fixture(directory, count):
    block, changed, left, right = fixture(count, 40429)
    paths = {name: directory / name for name in ("source", "left", "right", "out")}
    for name, data in (("source", block), ("left", left), ("right", right)):
        paths[name].write_bytes(data)
    return (
        ("fresh", paths["source"], "-", block),
        ("owned", paths["source"], "-", block),
        ("dense", paths["source"], "-", changed),
        ("alternating", paths["left"], paths["right"], block),
    ), paths["out"]


def checked_trials(binary, mode, left, right, output, repetitions, expected):
    result = invoke(binary, mode, left, right, output, repetitions)
    samples = [tuple(map(int, line.split())) for line in result.stdout.splitlines()]
    expected_tag = tag(expected)
    if len(samples) != repetitions or any(ns <= 0 or value != expected_tag for ns, value in samples):
        raise ValueError(f"{binary} {mode} returned unexpected timing or tag")
    if output != "-" and output.read_bytes() != expected:
        raise ValueError(f"{binary} {mode} produced different bytes")
    return samples


def check_fixtures(binaries, directory):
    for count in (0, 1, 7, 20, 1031):
        cases, output = prepare_fixture(directory, count)
        for variant, (binary, prefix) in binaries.items():
            for mode, left, right, expected in cases:
                for scope in ("", "kernel-"):
                    checked_trials(binary, scope + prefix + mode, left, right, output, 1, expected)
    for variant, (binary, prefix) in binaries.items():
        if variant in ("stock", "rust"):
            continue
        alias = directory / "alias"
        for n in (8, 17, 41):
            data = bytes(range(n))
            alias.write_bytes(data)
            expected = data + data[:-8] + WORD.pack(MASK) + WORD.pack(MASK)
            checked_trials(binary, "alias", alias, "-", output, 1, expected)
        corrupt = directory / "truncated"
        corrupt.write_bytes((directory / "source").read_bytes()[:-1])
        if invoke(binary, "fresh", corrupt, "-", "-", 1, check=False).returncode == 0:
            raise ValueError(f"{binary} accepted a truncated run")
        alias.write_bytes(b"short")
        if invoke(binary, "alias", alias, "-", "-", 1, check=False).returncode == 0:
            raise ValueError(f"{binary} accepted a short wide-store window")
        if invoke(binary, "alternating", directory / "right", directory / "left",
                  "-", 1, check=False).returncode == 0:
            raise ValueError(f"{binary} accepted an incompatible alternating split")
    print(f"Passed byte-exact v3, shared unaligned write, and malformed-input fixtures ({len(binaries)} binaries).")


def measure(binaries, directory, out, sizes, pairs, scopes, cpu):
    order = random.Random(15917)
    with out.open("w", newline="") as stream:
        writer = csv.writer(stream, lineterminator="\n")
        writer.writerow(("records", "mode", "scope", "variant", "pair", "position", "ns", "tag", "cpu"))
        for count in sizes:
            cases, output = prepare_fixture(directory, count)
            for mode, left, right, expected in cases:
                for scope in scopes:
                    scope_prefix = "kernel-" if scope == "kernel" else ""
                    for binary, prefix in binaries.values():
                        checked_trials(binary, scope_prefix + prefix + mode, left, right, output, 1, expected)
                    for pair in range(1, pairs + 1):
                        choices = list(binaries.items())
                        order.shuffle(choices)
                        for position, (variant, (binary, prefix)) in enumerate(choices, 1):
                            test_mode = scope_prefix + prefix + mode
                            _, (ns, value) = checked_trials(binary, test_mode, left, right, "-", 2, expected)
                            writer.writerow((count, mode, scope, variant, pair, position, ns, value, cpu))
                    stream.flush()


def summarize(path):
    groups = {}
    with path.open() as stream:
        for row in csv.DictReader(stream):
            key = tuple(row[name] for name in ("records", "mode", "scope", "variant"))
            groups.setdefault(key, []).append(int(row["ns"]))
    for (records, mode, scope, variant), times in sorted(groups.items()):
        print(f"{records:>8} {mode:>12} {scope:>7} {variant:>14} {median(times) / 1e6:8.3f} ms")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path)
    parser.add_argument("--sizes", type=int, nargs="+", default=[100_000, 1_000_000])
    parser.add_argument("--trials", type=int, default=9)
    parser.add_argument("--scopes", nargs="+", choices=("full", "kernel"), default=("full", "kernel"))
    parser.add_argument("--upstream", type=Path, help="same Lean driver built against the original PR toolchain")
    parser.add_argument("--summarize", type=Path)
    args = parser.parse_args()
    if args.summarize:
        summarize(args.summarize)
        return
    if min(args.sizes) < 1 or args.trials < 1:
        parser.error("sizes and trials must be positive")
    build = ROOT / "lean/.lake/wide-accessors"
    binaries = {variant: (build / variant, "") for variant in VARIANTS}
    binaries["stock"] = (build / "shifts", "stock-")
    binaries["rust"] = (build / "rust", "")
    if args.upstream:
        binaries["upstream-pr"] = (args.upstream.resolve(), "")
    cpu = min(os.sched_getaffinity(0))
    os.sched_setaffinity(0, {cpu})
    with TemporaryDirectory() as scratch:
        directory = Path(scratch)
        check_fixtures(binaries, directory)
        if args.out:
            measure(binaries, directory, args.out, args.sizes, args.trials, args.scopes, cpu)
            summarize(args.out)


if __name__ == "__main__":
    main()
