#!/usr/bin/env python3
import argparse
import csv
import os
from pathlib import Path
import random
import tempfile

from merge_phases import BINARIES, invoke, set_inputs, tag
from packed import merged_records, summarize
from scoped_builder import compactions, native_mode
from generate import WORD_MASK, block, dataset

MODES = [
    ("lean-stream", BINARIES["lean"], "replay-write"),
    ("lean-online-spans", BINARIES["lean"], "replay-spans"),
    ("lean-prepared", BINARIES["lean"], "replay-prepared"),
    ("lean-prepare-and-write", BINARIES["lean"], "replay-prepare-and-write"),
    ("rust", BINARIES["rust"], "replay-write"),
    ("rust-scoped", BINARIES["rust"], "replay-write"),
]


def cases(directory):
    paths = tuple(directory / name for name in ("left", "right", "trace"))
    output = directory / "output"
    extrema = [(0, 17), (WORD_MASK, WORD_MASK)]
    fixtures = [([], []), (extrema, []), ([], extrema),
                (extrema, [(0, 0), (17, 1), (WORD_MASK, 2)])]
    fixtures.extend(pair for _, pair in compactions(dataset(1027)))
    for left, right in fixtures:
        set_inputs(paths, left, right)
        expected = block(merged_records(left, right))
        for label, binary, mode in MODES:
            invoke(binary, native_mode(label, f"check-{mode}"), paths, output)
            assert output.read_bytes() == expected, (label, len(left), len(right))
    set_inputs(paths, [(0, 1)], [(1, 2)])
    for malformed in (b"", b"\x00", b"\x00\x00", b"\xff\x01", b"\x02\x01"):
        paths[2].write_bytes(malformed)
        for label, binary, mode in MODES:
            result = invoke(binary, native_mode(label, mode), paths, output, check=False)
            assert result.returncode and "invalid replay trace" in result.stderr, label
    print(f"Passed {len(fixtures)} exact byte fixtures and 5 malformed traces.")


def run(directory, out, sizes, trials):
    cpu = min(os.sched_getaffinity(0))
    os.sched_setaffinity(0, {cpu})
    rng = random.Random(550)
    paths = tuple(directory / name for name in ("left", "right", "trace"))
    output = directory / "output"
    with out.open("w", newline="") as stream:
        writer = csv.writer(stream, lineterminator="\n")
        writer.writerow(("records", "workload", "variant", "trial", "ns", "operations",
                         "checksum", "cpu", "peak_rss_kib", "output_records", "spans"))
        for size in sizes:
            for workload, (left, right) in compactions(dataset(size)):
                set_inputs(paths, left, right)
                expected = block(merged_records(left, right))
                trace = paths[2].read_bytes()
                spans = bool(trace) + sum((a == 0) != (b == 0) for a, b in zip(trace, trace[1:]))
                order = list(MODES)
                rng.shuffle(order)
                for label, binary, mode in order:
                    invoke(binary, native_mode(label, f"check-{mode}"), paths, output)
                    assert output.read_bytes() == expected, (label, workload, size)
                    samples = invoke(binary, native_mode(label, mode), paths, output, trials + 1)
                    assert len(samples) == trials + 1
                    assert all(seen == tag(expected) for _, seen in samples), (label, workload)
                    for trial, (ns, seen) in enumerate(samples[1:], 1):
                        writer.writerow((size, workload, label, trial, ns, size, seen, cpu, "",
                                         len(trace), spans))
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
        cases(directory)
        if args.out:
            run(directory, args.out, args.sizes, args.trials)


if __name__ == "__main__":
    main()
