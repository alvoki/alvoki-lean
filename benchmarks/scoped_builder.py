#!/usr/bin/env python3
import argparse
import csv
import os
from pathlib import Path
import random
import tempfile

from support import (
    INVALID_TRACES, MASK, ROOT, TRACE_FIXTURE, compactions, merged_records, native_mode, set_inputs, summarize, tag,
)
from support import invoke_replay as invoke
from generate import WORD_MASK, block, dataset, workloads

LEAN = ROOT / "lean/.lake/build/bin"
BINARIES = {
    "stock": LEAN / "alvoki-merge-phases",
    "inline": LEAN / "alvoki-merge-phases-inline",
    "scoped": LEAN / "alvoki-merge-phases-scoped",
    "scoped-branchless": LEAN / "alvoki-merge-phases-scoped-branchless",
    "rust": ROOT / "rust/target/release/alvoki-merge-phases",
    "rust-scoped": ROOT / "rust/target/release/alvoki-merge-phases",
}


def check(directory):
    paths = tuple(directory / item for item in ("left", "right", "trace"))
    output = directory / "output"
    extremes = [(0, WORD_MASK), (WORD_MASK, 0)]
    fixtures = [([], []), ([], extremes), (extremes, []), (extremes, [(0, 0), (WORD_MASK, WORD_MASK)])]
    fixtures.extend(pair for _, pair in compactions(dataset(1027)))
    for left, right in fixtures:
        set_inputs(paths, left, right)
        expect = block(merged_records(left, right))
        for variant, binary in BINARIES.items():
            for mode in ("merge", "replay-write"):
                invoke(binary, native_mode(variant, f"check-{mode}"), paths, output)
                assert output.read_bytes() == expect, (variant, mode)
            invoke(binary, native_mode(variant, "check-dense"), paths, output)
            assert output.read_bytes() == block([(k, v ^ MASK) for k, v in left]), variant

    set_inputs(paths, *TRACE_FIXTURE)
    for malformed in INVALID_TRACES:
        paths[2].write_bytes(malformed)
        for variant, binary in BINARIES.items():
            result = invoke(binary, native_mode(variant, "replay-write"), paths, output, check=False)
            assert result.returncode != 0 and "invalid replay trace" in result.stderr, variant
    print(f"Passed {len(fixtures)} exact builder fixtures and {len(INVALID_TRACES)} invalid trace fixtures.")


def sample(writer, rng, paths, output, size, label, mode, trials, cpu, expected_bytes=None, checksum=None):
    variants = [(key, path) for key, path in BINARIES.items()
                if not (mode == "dense" and key == "rust-scoped")]
    rng.shuffle(variants)
    for variant, binary in variants:
        if expected_bytes is not None:
            invoke(binary, native_mode(variant, f"check-{mode}"), paths, output)
            assert output.read_bytes() == expected_bytes, (label, mode, variant)
        samples = invoke(binary, native_mode(variant, mode), paths, output, trials + 1)
        expected_tag = checksum if expected_bytes is None else tag(expected_bytes)
        assert len(samples) == trials + 1 and all(result == expected_tag for _, result in samples)
        for trial, (elapsed, result) in enumerate(samples[1:], 1):
            writer.writerow((size, f"{label}-{mode}", variant, trial, elapsed, size, result, cpu, ""))


def run(directory, out, sizes, trials):
    cpu = min(os.sched_getaffinity(0))
    os.sched_setaffinity(0, {cpu})
    rng = random.Random(455)
    paths = tuple(directory / item for item in ("left", "right", "trace"))
    output = directory / "output"
    with out.open("w", newline="") as stream:
        writer = csv.writer(stream, lineterminator="\n")
        writer.writerow(("records", "workload", "variant", "trial", "ns", "operations",
                         "checksum", "cpu", "peak_rss_kib"))
        for size in sizes:
            records = dataset(size)
            for label, (left, right) in compactions(records):
                assert len(left) + len(right) == size
                set_inputs(paths, left, right)
                merged = merged_records(left, right)
                expected = block(merged)
                for mode in ("replay-write", "merge"):
                    sample(writer, rng, paths, output, size, label, mode, trials, cpu, expected_bytes=expected)
                targets = workloads(size)["mixed"]
                paths[2].write_bytes(block(list(enumerate(targets))))
                values = dict(merged)
                checksum = (sum(k ^ v for k, v in merged) +
                            sum(values.get(k, 0) for k in targets)) & WORD_MASK
                sample(writer, rng, paths, output, size, label, "pipeline", trials, cpu, checksum=checksum)
                stream.flush()

            set_inputs(paths, records, [])
            expected = block([(k, v ^ MASK) for k, v in records])
            sample(writer, rng, paths, output, size, "rewrite", "dense", trials, cpu, expected_bytes=expected)
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
        parser.error("positive sizes and trial count are required")
    with tempfile.TemporaryDirectory() as temp:
        directory = Path(temp)
        check(directory)
        if args.out:
            run(directory, args.out, args.sizes, args.trials)


if __name__ == "__main__":
    main()
