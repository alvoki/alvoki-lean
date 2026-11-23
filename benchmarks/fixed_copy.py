#!/usr/bin/env python3
import argparse
import csv
import os
from pathlib import Path
import random
import subprocess
import tempfile

from support import MERGE_BINARIES
from support import ROOT, set_inputs, split_spans, summarize, tag
from support import invoke_replay as invoke
from generate import WORD_MASK, block, dataset, workloads

BINARIES = dict(MERGE_BINARIES, fixed=ROOT / "lean/.lake/build/bin/alvoki-merge-phases-fixed",
                inline=ROOT / "lean/.lake/build/bin/alvoki-merge-phases-inline")
GROUP = 256


def setup(paths, records, span, width):
    left, right = split_spans(records, span)
    paths[0].write_bytes(block(left))
    paths[1].write_bytes(block(right))
    count = width // 16
    paths[2].write_bytes(bytes((i // span) % 2 for i in range(0, len(records), count)))


def cases(directory):
    paths = tuple(directory / name for name in ("left", "right", "trace"))
    output = directory / "output"
    for size, span in [(0, GROUP), (512, GROUP), (9, 1), (1024, GROUP)]:
        records = dataset(size)
        for width in (16, 32, 64, 4096) if span == GROUP else (16,):
            setup(paths, records, span, width)
            for binary in BINARIES.values():
                invoke(binary, f"check-copy{width}", paths, output)
                assert output.read_bytes() == block(records), (binary, width)
    for label, binary in BINARIES.items():
        if label != "rust":
            subprocess.run([binary, "copy-contract"], check=True)
    print("Passed fixed-width output fixtures for all four binaries.")


def run(directory, out, trials):
    cpu = min(os.sched_getaffinity(0))
    os.sched_setaffinity(0, {cpu})
    rng = random.Random(706)
    paths = tuple(directory / name for name in ("left", "right", "trace"))
    output = directory / "output"
    with out.open("w", newline="") as stream:
        writer = csv.writer(stream, lineterminator="\n")
        writer.writerow(("records", "workload", "variant", "trial", "ns", "operations",
                         "checksum", "cpu", "peak_rss_kib"))
        for size in (1024, 102400, 1024000):
            records = dataset(size)
            expected = block(records)
            for width in (16, 32, 64, 4096):
                setup(paths, records, GROUP, width)
                run_job(rng, writer, size, f"copy{width}", paths, output, expected, trials, cpu)
            left, right = split_spans(records, 1)
            set_inputs(paths, left, right)
            for mode in ("copy16", "merge", "replay-write"):
                run_job(rng, writer, size, mode, paths, output, expected, trials, cpu,
                        workload="alternating-" + mode)
            targets = workloads(size)["mixed"]
            paths[2].write_bytes(block(list(enumerate(targets))))
            values = dict(records)
            expected_tag = (sum(k ^ v for k, v in records) + sum(values.get(k, 0) for k in targets)) & WORD_MASK
            variants = list(BINARIES.items())
            rng.shuffle(variants)
            for label, binary in variants:
                samples = invoke(binary, "pipeline", paths, output, trials + 1)
                assert len(samples) == trials + 1 and all(seen == expected_tag for _, seen in samples)
                for trial, (elapsed, seen) in enumerate(samples[1:], 1):
                    writer.writerow((size, "alternating-pipeline", label, trial, elapsed, size, seen, cpu, ""))
            stream.flush()


def run_job(rng, writer, size, mode, paths, output, expected, trials, cpu, workload=None):
    variants = list(BINARIES.items())
    rng.shuffle(variants)
    for label, binary in variants:
        invoke(binary, f"check-{mode}", paths, output)
        assert output.read_bytes() == expected, (label, mode, size)
        samples = invoke(binary, mode, paths, output, trials + 1)
        assert len(samples) == trials + 1 and all(seen == tag(expected) for _, seen in samples)
        for trial, (elapsed, seen) in enumerate(samples[1:], 1):
            writer.writerow((size, workload or mode, label, trial, elapsed, size, seen, cpu, ""))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path)
    parser.add_argument("--summarize", type=Path)
    parser.add_argument("--trials", type=int, default=9)
    args = parser.parse_args()
    if args.summarize:
        summarize(args.summarize)
        return
    if args.trials < 1:
        parser.error("positive trial count required")
    with tempfile.TemporaryDirectory() as temp:
        directory = Path(temp)
        cases(directory)
        if args.out:
            run(directory, args.out, args.trials)


if __name__ == "__main__":
    main()
