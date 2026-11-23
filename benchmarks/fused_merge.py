#!/usr/bin/env python3
import argparse
import csv
import os
from pathlib import Path
import random
import subprocess
import tempfile

from merge_phases import BINARIES, decisions, tag
from packed import merged_records, summarize
from scoped_builder import compactions
from run import ROOT
from generate import WORD_MASK, block, dataset, workloads

LEAN = ROOT / "lean/.lake/build/bin/alvoki-fused-merge"
RUST = BINARIES["rust"]
MERGE = [(f"lean-{mode}", LEAN, f"{mode}-merge") for mode in ("plain", "adaptive", "fused")]
MERGE += [("rust", RUST, "merge"), ("rust-scoped", RUST, "builder-merge")]
SCAN = [(f"lean-{mode}", LEAN, f"{mode}-scan") for mode in ("plain", "adaptive", "fused", "direct", "selected")]
SCAN += [("rust", RUST, "merge-scan"), ("rust-scoped", RUST, "builder-merge-scan"),
         ("rust-direct", RUST, "direct-scan"), ("rust-selected", RUST, "selected-scan")]
PIPELINE = [("lean-adaptive", LEAN, "adaptive-pipeline"), ("lean-fused", LEAN, "fused-pipeline"),
            ("rust", RUST, "pipeline"), ("rust-scoped", RUST, "builder-pipeline")]


def invoke(binary, mode, paths, output, reps=1, rss=False):
    env = dict(os.environ)
    env.pop("ALVOKI_RSS", None)
    if rss:
        env["ALVOKI_RSS"] = "1"
    lines = subprocess.check_output([binary, mode, *paths, output, str(reps)], text=True, env=env).splitlines()
    rss_kib = int(lines.pop().split()[1]) if rss else None
    return [tuple(map(int, line.split())) for line in lines], rss_kib


def check_merge(binary, mode, paths, output, expected):
    if mode.startswith("builder-"):
        checked = "builder-check-" + mode.removeprefix("builder-")
    else:
        checked = "check-" + mode
    invoke(binary, checked, paths, output)
    assert output.read_bytes() == expected, (binary, mode)


def scan_checksum(records):
    return sum(key ^ value for key, value in records) & WORD_MASK


def check(directory):
    paths = tuple(directory / name for name in ("left", "right", "aux"))
    output = directory / "output"
    extremes = [(0, WORD_MASK), (WORD_MASK, 1)]
    fixtures = [([], []), (extremes, []), ([], extremes),
                (extremes, [(0, 1), (1, 2), (WORD_MASK, 3)])]
    for n in (7, 8, 9, 255, 256, 257, 2_047):
        left = [(i * 2, i + 3) for i in range(n + 3)]
        right = [(n * 2 - 1, 3), (n * 2, WORD_MASK), (WORD_MASK, 8)]
        fixtures.append((left, right))
        fixtures.append((right, left))
    fixtures.extend(pair for _, pair in compactions(dataset(1027)))
    for left, right in fixtures:
        paths[0].write_bytes(block(left))
        paths[1].write_bytes(block(right))
        paths[2].write_bytes(decisions(left, right))
        expected = merged_records(left, right)
        for _, binary, mode in MERGE:
            check_merge(binary, mode, paths, output, block(expected))
        for _, binary, mode in SCAN:
            samples, _ = invoke(binary, mode, paths, output)
            assert samples[0][1] == scan_checksum(expected), (binary, mode, left, right)
        keys = [0, 1, 42, WORD_MASK]
        paths[2].write_bytes(block(list(enumerate(keys))))
        values = dict(expected)
        expected_sum = (scan_checksum(expected) + sum(values.get(k, 0) for k in keys)) & WORD_MASK
        for _, binary, mode in PIPELINE:
            samples, _ = invoke(binary, mode, paths, output)
            assert samples[0][1] == expected_sum, (binary, mode)
    print(f"Passed {len(fixtures)} exact-output, scan, and pipeline fixtures.")


def run(directory, destination, sizes, trials):
    cpu = min(os.sched_getaffinity(0))
    os.sched_setaffinity(0, {cpu})
    rng = random.Random(361)
    paths = tuple(directory / name for name in ("left", "right", "aux"))
    output = directory / "output"
    with destination.open("w", newline="") as stream:
        writer = csv.writer(stream, lineterminator="\n")
        writer.writerow(("records", "workload", "variant", "trial", "ns", "operations",
                         "checksum", "cpu", "peak_rss_kib", "input_bytes", "output_bytes"))
        for size in sizes:
            records = dataset(size)
            for profile, (left, right) in compactions(records):
                a, b = block(left), block(right)
                expected = merged_records(left, right)
                encoded = block(expected)
                checksum = scan_checksum(expected)
                paths[0].write_bytes(a)
                paths[1].write_bytes(b)
                targets = workloads(size)["mixed"]
                values = dict(expected)
                pipeline_checksum = (checksum + sum(values.get(key, 0) for key in targets)) & WORD_MASK
                jobs = [("merge", MERGE, tag(encoded)), ("scan", SCAN, checksum),
                        ("pipeline", PIPELINE, pipeline_checksum)]
                for task, variants, wanted in jobs:
                    # Legacy Rust merge requires a valid trace. New stock Lean
                    # experiments never read this auxiliary file in these modes.
                    paths[2].write_bytes(block(list(enumerate(targets))) if task == "pipeline"
                                         else decisions(left, right))
                    options = list(variants)
                    rng.shuffle(options)
                    for label, binary, mode in options:
                        if task == "merge":
                            check_merge(binary, mode, paths, output, encoded)
                        samples, rss = invoke(binary, mode, paths, output, trials + 1, rss=True)
                        assert len(samples) == trials + 1
                        assert all(seen == wanted for _, seen in samples), (label, profile, task)
                        for trial, (ns, seen) in enumerate(samples[1:], 1):
                            writer.writerow((size, f"{profile}-{task}", label, trial, ns, size,
                                             seen, cpu, rss, len(a) + len(b), len(encoded)))
                stream.flush()


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
        parser.error("positive sizes and trial count required")
    with tempfile.TemporaryDirectory() as directory:
        check(Path(directory))
        if args.out:
            run(Path(directory), args.out, args.sizes, args.trials)


if __name__ == "__main__":
    main()
