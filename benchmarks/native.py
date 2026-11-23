#!/usr/bin/env python3
import argparse
import csv
import os
from pathlib import Path
import random
import tempfile

from packed import checksum, merge_inputs, merged_records, run_once, summarize
from run import ROOT, measured
from generate import WORD_MASK, block, dataset

LEAN = ROOT / "lean/.lake/build/bin/alvoki-native"
RUST = ROOT / "rust/target/release/alvoki-native"
SCALAR = ROOT / "rust/target/scalar/release/alvoki-native"
RUST_MERGE = ROOT / "rust/target/release/alvoki-packed"
SCAN = [(LEAN, variant) for variant in ("scan-original", "scan-bounded", "scan-unrolled")]
SCAN += [(RUST, "scan"), (SCALAR, "scan")]
ENCODE = [(LEAN, "encode-direct"), (LEAN, "encode-staged"), (LEAN, "encode-pair"), (RUST, "encode")]
MERGE = [(LEAN, "merge"), (LEAN, "merge-spans"), (LEAN, "merge-indexed"), (RUST_MERGE, "merge")]
SPANS = (1, 4, 16, 64, 256)


def label(binary, mode):
    return f"{'lean' if binary == LEAN else 'rust-scalar' if binary == SCALAR else 'rust'}-{mode}"


def split_spans(records, length):
    sides = ([], [])
    for start in range(0, len(records), length):
        sides[(start // length) % 2].extend(records[start:start + length])
    return sides


def flipped(records):
    return [(key, value ^ 1) for key, value in records]


def check(directory):
    rng = random.Random(117)
    data, aux, output = (directory / name for name in ("data", "aux", "output"))
    cases = [[], [(0, 0)], [(0, WORD_MASK), (WORD_MASK, 4)]]
    for size in (3, 4, 5, 15, 16, 17, 255, 256, 257, 1027):
        keys = sorted(rng.sample(range(size * 5), size))
        cases.append([(k, rng.getrandbits(64)) for k in keys])
    for records in cases:
        data.write_bytes(block(records))
        for binary, mode in SCAN:
            samples, _, _ = measured(label(binary, mode), binary, mode, data, aux, 0, 1)
            assert int(samples[0].split()[1]) == checksum(records), (binary, mode, len(records))
        for binary, mode in [(LEAN, "check-direct"), (LEAN, "check-staged"), (LEAN, "check-pair"), (RUST, "check-encode")]:
            run_once(binary, mode, data, aux, output)
            assert output.read_bytes() == block(flipped(records)), (binary, mode, len(records))
    merges = [(a, b) for a, b in zip(cases, reversed(cases))]
    merges += [split_spans(cases[-1], length) for length in SPANS]
    merges += [(cases[-1], flipped(cases[-1])), merge_inputs(1027, "overlap")]
    for left, right in merges:
        data.write_bytes(block(left))
        aux.write_bytes(block(right))
        for binary, mode in MERGE:
            run_once(binary, "check-" + mode, data, aux, output)
            assert output.read_bytes() == block(merged_records(left, right)), (mode, len(left), len(right))
    print(f"Passed {len(cases)} scan/encode fixtures and {len(merges)} exact merge fixtures.")


def run(directory, path, sizes, trials):
    cpu = min(os.sched_getaffinity(0))
    os.sched_setaffinity(0, {cpu})
    rng = random.Random(512)
    data, aux = (directory / name for name in ("data", "aux"))
    with path.open("w", newline="") as out:
        writer = csv.writer(out, lineterminator="\n")
        writer.writerow(("records", "workload", "variant", "trial", "ns", "operations",
                         "checksum", "cpu", "peak_rss_kib"))
        for size in sizes:
            records = dataset(size)
            data.write_bytes(block(records))
            jobs = [("scan", SCAN), ("encode", ENCODE)]
            jobs += [(f"span-{length}", MERGE) for length in SPANS]
            jobs += [("overlap", MERGE), ("disjoint", MERGE)]
            for workload, variants in jobs:
                if workload.startswith("span-"):
                    left, right = split_spans(records, int(workload.removeprefix("span-")))
                    data.write_bytes(block(left))
                    aux.write_bytes(block(right))
                elif variants == MERGE:
                    left, right = merge_inputs(size, workload)
                    data.write_bytes(block(left))
                    aux.write_bytes(block(right))
                order = list(variants)
                rng.shuffle(order)
                checksums = set()
                for binary, mode in order:
                    variant = label(binary, mode)
                    samples, rss, _ = measured(variant, binary, mode, data, aux, 0, trials + 1)
                    assert len(samples) == trials + 1, (variant, workload)
                    for trial, line in enumerate(samples[1:], 1):
                        ns, tag = map(int, line.split())
                        checksums.add(tag)
                        writer.writerow((size, workload, variant, trial, ns, size, tag, cpu, rss))
                assert len(checksums) == 1, (workload, checksums)
                out.flush()


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
