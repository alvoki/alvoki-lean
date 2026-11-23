#!/usr/bin/env python3
import argparse
import csv
import os
from pathlib import Path
import random
import subprocess
import tempfile

from native import mixed_spans, split_spans
from packed import merged_records, summarize
from run import ROOT
from generate import WORD_MASK, block, dataset

BINARIES = {
    "lean": ROOT / "lean/.lake/build/bin/alvoki-merge-phases",
    "rust": ROOT / "rust/target/release/alvoki-merge-phases",
}
MODES = ("select", "replay-checksum", "replay-write", "merge")


def decisions(left, right):
    """Build a trace outside the timer from the independent sorted-union oracle."""
    left_keys = set(dict(left))
    right_keys = set(dict(right))
    return bytes(
        2 if key in left_keys and key in right_keys else int(key in right_keys)
        for key in sorted(left_keys | right_keys)
    )


def checksum(records):
    result = 0
    for key, value in records:
        result = (result * 3 + (key ^ value)) & WORD_MASK
    return result


def tag(encoded):
    return int.from_bytes(encoded[:8], "little") ^ int.from_bytes(encoded[-8:], "little") ^ len(encoded)


def invoke(binary, mode, inputs, output, reps=1, check=True):
    result = subprocess.run([binary, mode, *inputs, output, str(reps)],
                            text=True, capture_output=True, check=check)
    return result if not check else [tuple(map(int, line.split())) for line in result.stdout.splitlines()]


def set_inputs(inputs, left, right):
    a, b, trace = inputs
    a.write_bytes(block(left))
    b.write_bytes(block(right))
    trace.write_bytes(decisions(left, right))


def check_cases(directory):
    paths = tuple(directory / name for name in ("left", "right", "trace"))
    output = directory / "output"
    rng = random.Random(833)
    cases = [([], []), ([], [(0, 1), (WORD_MASK, 2)]),
             ([(0, 1), (WORD_MASK, 2)], []),
             ([(0, 1), (WORD_MASK, 2)], [(0, WORD_MASK), (7, 3), (WORD_MASK, 0)])]
    for size in (1, 3, 16, 127, 1027):
        a, b = [
            [(key, rng.getrandbits(64)) for key in sorted(rng.sample(range(size * 2), size))]
            for _ in range(2)
        ]
        cases.append((a, b))
    cases.extend([split_spans(dataset(1027), 1), mixed_spans(dataset(1027))])
    for a, b in cases:
        set_inputs(paths, a, b)
        expected = merged_records(a, b)
        for binary in BINARIES.values():
            for mode in ("select", "replay-checksum"):
                assert invoke(binary, mode, paths, output)[0][1] == checksum(expected), (binary, mode)
            for mode in ("check-replay-write", "check-merge"):
                invoke(binary, mode, paths, output)
                assert output.read_bytes() == block(expected), (binary, mode)

    set_inputs(paths, [(0, 1)], [(1, 2)])
    for malformed in (b"", b"\x00", b"\x00\x00", b"\xff\x01", b"\x02\x01"):
        paths[2].write_bytes(malformed)
        for binary in BINARIES.values():
            result = invoke(binary, "replay-write", paths, output, check=False)
            assert result.returncode != 0 and "invalid replay trace" in result.stderr
    print(f"Passed {len(cases)} exact merge and checksum fixtures and 5 malformed trace fixtures.")


def run(directory, destination, sizes, trials):
    cpu = min(os.sched_getaffinity(0))
    os.sched_setaffinity(0, {cpu})
    rng = random.Random(974)
    inputs = tuple(directory / name for name in ("left", "right", "trace"))
    output = directory / "output"
    with destination.open("w", newline="") as stream:
        writer = csv.writer(stream, lineterminator="\n")
        writer.writerow(("records", "workload", "variant", "trial", "ns", "operations",
                         "checksum", "cpu", "peak_rss_kib", "output_records"))
        for size in sizes:
            records = dataset(size)
            half, shift = size // 2, size // 8
            collisions = (records[:half], [(k, v ^ WORD_MASK) for k, v in records[shift:shift + size - half]])
            workloads = [("alternating", split_spans(records, 1)),
                         ("mixed-spans", mixed_spans(records)), ("collision-heavy", collisions)]
            for workload, (a, b) in workloads:
                set_inputs(inputs, a, b)
                expected = merged_records(a, b)
                expected_bytes = block(expected)
                for binary in BINARIES.values():
                    for mode in ("check-replay-write", "check-merge"):
                        invoke(binary, mode, inputs, output)
                        assert output.read_bytes() == expected_bytes, (binary, mode, workload)
                output_tag = tag(expected_bytes)
                sum_tag = checksum(expected)
                order = [(label, mode) for label in BINARIES for mode in MODES]
                rng.shuffle(order)
                for label, mode in order:
                    samples = invoke(BINARIES[label], mode, inputs, output, trials + 1)
                    assert len(samples) == trials + 1, (label, mode)
                    want = sum_tag if mode in ("select", "replay-checksum") else output_tag
                    assert all(seen == want for _, seen in samples), (label, mode, workload)
                    for trial, (elapsed, seen) in enumerate(samples[1:], 1):
                        writer.writerow((size, workload, f"{label}-{mode}", trial, elapsed,
                                         size, seen, cpu, "", len(expected)))
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
        check_cases(directory)
        if args.out:
            run(directory, args.out, args.sizes, args.trials)


if __name__ == "__main__":
    main()
